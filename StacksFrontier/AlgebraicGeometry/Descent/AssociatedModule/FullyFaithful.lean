module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.UnitFree
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.AssociatedModuleColimits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Full faithfulness of the associated-module functor

Stacks 0GN7 says that `𝓕 ↦ 𝓕^a` is fully faithful on quasi-coherent modules, and the proof the
source gives is the adjunction one: `𝓕 ↦ 𝓕^a` is the pullback along a morphism of ringed sites
(Remark 03FH), its right adjoint `f_*` is restriction along the inclusion of the small Zariski
site, and `f_* f^* 𝓕 = 𝓕` for quasi-coherent `𝓕`.  In other words full faithfulness *is* the
statement that the unit `𝓕 ⟶ (𝓕^a)|_{S_Zar}` of
`AlgebraicGeometry.BigFppfOver.associatedModuleAdjunction` is an isomorphism at every
quasi-coherent `𝓕`.

This file does three things.

First it isolates the categorical half: for an adjunction `L ⊣ R` and a functor `G` into the
source, `G ⋙ L` is faithful as soon as the unit is a monomorphism at each `G.obj a` and `G` is
faithful, and full as soon as the unit is an isomorphism there and `G` is full.  Only the
objects in the image of `G` matter, which is what makes the statement usable on a full
subcategory such as `QCoh(𝒪_S)`.

Second it proves, **with no hypothesis on `S`**, that the unit is an isomorphism at every *free*
`𝒪_S`-module.  `StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.UnitFree` proves that the
unit at `free I` is an isomorphism on sections at any object of the small Zariski site which is
quasi-compact there and whose image in the big fppf site is quasi-compact; the affine opens of
`S` are such objects and they form a basis of the topology, so the unit is an isomorphism of
Zariski sheaves.  This removes the `CompactSpace ↥S` hypothesis of
`AlgebraicGeometry.BigFppfOver.isFullOnFree_of_compactSpace` — no localization of the setup to
an open subscheme is needed, because sections of a restriction along the inclusion of the small
Zariski site are sections at the corresponding object of the big site, so the quasi-compactness
input is available at every affine open directly.

Third, it records what this file leaves open for 0GN7 — and where 0GN7 is in fact discharged and
tagged.  See the implementation notes.

## Main results

* `CategoryTheory.Adjunction.bijective_map_of_isIso_unit_app`: a left adjoint is bijective on
  morphisms into an object at which the unit is an isomorphism.
* `CategoryTheory.Adjunction.faithful_comp_L_of_mono_unit_app` and
  `CategoryTheory.Adjunction.full_comp_L_of_isIso_unit_app`: full faithfulness of a left
  adjoint restricted along a functor, from the unit at the objects in that functor's image.
* `AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_app_affineOpens`: a morphism of sheaves of
  modules on a scheme is an isomorphism as soon as it is one on sections over every affine open.
* `AlgebraicGeometry.BigFppfOver.isIso_unit_app_free`: the unit of the associated-module
  adjunction is an isomorphism at every free `𝒪_S`-module, for every `S`.
* `AlgebraicGeometry.BigFppfOver.isFullOnFree`:
  `AlgebraicGeometry.BigFppfOver.IsFullOnFree` with no hypothesis, which is
  `AlgebraicGeometry.BigFppfOver.isFullOnFree_of_compactSpace` with `CompactSpace ↥S` removed.
* `AlgebraicGeometry.BigFppfOver.exists_isQuasicoherent_iso_associatedModule_of_cokernelFree'`:
  the local step of the essential surjectivity half of Stacks 03DX (1) for `τ = fppf`, now with
  no remaining hypothesis.
* `AlgebraicGeometry.BigFppfOver.bijective_associatedModule_map_free`: **Stacks 0GN7 with free
  target** — `Hom(𝓕, ⊕_I 𝒪_S) ⟶ Hom(𝓕^a, ⊕_I 𝒪)` is bijective for every `𝒪_S`-module `𝓕`.
* `AlgebraicGeometry.BigFppfOver.full_associatedModuleQcoh` and
  `AlgebraicGeometry.BigFppfOver.faithful_associatedModuleQcoh`: **Stacks 0GN7** over the single
  hypothesis `AlgebraicGeometry.BigFppfOver.UnitIsoOnQuasicoherent`.  These are the two
  instances that
  `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimitsOfSize`
  already consumes.

## Implementation notes

Nothing here is tagged, and in particular Stacks 0GN7 is not discharged **in this file**.  What
this file leaves open is exactly `AlgebraicGeometry.BigFppfOver.UnitIsoOnQuasicoherent`: the unit
at a quasi-coherent `𝓕` which is not free.  It is open here only; it is discharged with no
hypothesis in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FullyFaithfulUnconditional` as
`AlgebraicGeometry.BigFppfOver.unitIsoOnQuasicoherent`, and 0GN7 itself carries its tag
`τ`-parametrically on
`AlgebraicGeometry.BigFppfOver.fullyFaithfulBaseAssociatedModuleQcoh`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseFullyFaithful.lean`).

It does **not** follow from the free case, and the reason is structural
rather than a matter of friction.  Write a quasi-coherent `𝓕` as a cokernel
`⊕_{I₂} 𝒪_S ⟶ ⊕_{I₁} 𝒪_S ⟶ 𝓕 ⟶ 0` of free modules.  The associated-module functor is a left
adjoint, so it carries that presentation to a presentation of `𝓕^a`; but
`AlgebraicGeometry.BigFppfOver.restrictModule` is a *right* adjoint, so it preserves kernels and
not cokernels, and the unit at `𝓕` is therefore not determined by the unit at `⊕_{I₁} 𝒪_S` and
`⊕_{I₂} 𝒪_S`.  Concretely, over an open `U` of `S` the unit at `𝓕` is the map
`Γ(U, 𝓕) ⟶ Γ(U^{big}, 𝓕^a)`, where `U^{big}` is `U` viewed as an object of the big fppf site of
`S`; taking sections there is left exact, so what is missing is its *surjectivity* — the
vanishing of the obstruction carried by the first fppf cohomology of the kernel of
`⊕_{I₁} 𝒪 ⟶ 𝓕^a`.  That is flat descent, not a formal consequence of the free case, and it is
the step for which Stacks appeals to the *sections* description of `𝓕^a` — Definition 03DU (3)
together with Stacks 070S (1).

**Both are now in the library.**  The sections presheaf is
`AlgebraicGeometry.BigFppfOver.sectionsPresheafOfModules`
(`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherentSectionsModule.lean:189`), and its
identification with this pullback is
`AlgebraicGeometry.BigFppfOver.associatedModuleIsoSections`
(`StacksFrontier/AlgebraicGeometry/Descent/SectionsPullbackComparison/Comparison.lean:1284`),
with no hypothesis beyond quasi-coherence of `𝓕`; it is the `τ = .fppf` instance of
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSections` (`ibid.:1263`), which is the
declaration carrying
`@[stacks 070S "part (1)", stacks 03FH "part (1)"]`.  (The tag is carried by the
`τ`-parametric form, of which the fppf form is an instance.)

What that does *not* yet give is the surjectivity above.  `associatedModuleIsoSections` is an
isomorphism **of objects**, one `𝓕` at a time, not a natural isomorphism of functors, and
sections of a sheafification at an object are not sections of the presheaf there — so the
obstruction relocates to the fppf sheaf condition for that presheaf rather than disappearing.
That sheaf condition is Stacks 03DT; see
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.UnitQuasicoherent`, which proves this
file's `UnitIsoOnQuasicoherent` over exactly it.

The statement `AlgebraicGeometry.BigFppfOver.faithful_associatedModuleQcoh` only needs the unit
to be a monomorphism at the quasi-coherent modules, and that weaker statement is blocked at the
same place: a left exact functor does not preserve images, so `Mono` at a cokernel of free
modules is not a consequence of `IsIso` at the free modules either.

0GN7 quantifies over the five topologies `τ` and over both the big and the small `τ` site of
`S` (the small one only at `τ ∈ {Zariski, étale}`, which is where Definition 03DU gives it).
Everything here is the big fppf site, because
`AlgebraicGeometry.BigFppfOver.associatedModule` is constructed only there.  The coarser forms
are proved, uniformly in `τ`, by
`AlgebraicGeometry.BigFppfOver.fullyFaithfulBaseAssociatedModuleQcoh` in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseFullyFaithful`, which is where the
tag sits.  The target category is
`Mod((Sch/S)_fppf, 𝒪)` rather than `QCoh((Sch/S)_fppf, 𝒪)`, which is the same statement because
the latter is a full subcategory of the former — and what lands the functor in it is Stacks 03DV,
which this library **does** have:
`AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseOpenCoverQuasicoherence.lean:250`)
for clause (1) at every `τ`, with clause (2) at its two `τ` in the two small-site modules.

## References

* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {A : Type u₃} [Category.{v₃} A] {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)

/-- The unit of an adjunction composed with a morphism is the image of that morphism under the
adjunction bijection: this is `CategoryTheory.Adjunction.homEquiv_unit` read through the
naturality of the unit. -/
public theorem homEquiv_map_eq_comp_unit {X Y : C} (f : X ⟶ Y) :
    h.homEquiv X (L.obj Y) (L.map f) = f ≫ h.unit.app Y := by
  rw [Adjunction.homEquiv_unit, h.unit_naturality]

/-- **A left adjoint is bijective on morphisms into an object at which the unit is an
isomorphism.**  Composing with the unit at `Y` is a bijection, and the adjunction identifies it
with the action of the left adjoint on morphisms. -/
public theorem bijective_map_of_isIso_unit_app (X : C) {Y : C} (hY : IsIso (h.unit.app Y)) :
    Function.Bijective (fun f : X ⟶ Y => L.map f) := by
  have := hY
  refine ⟨fun f g hfg => ?_, fun k => ?_⟩
  · refine (cancel_mono (h.unit.app Y)).mp ?_
    rw [← h.homEquiv_map_eq_comp_unit f, ← h.homEquiv_map_eq_comp_unit g]
    exact congrArg _ hfg
  · refine ⟨h.homEquiv X (L.obj Y) k ≫ inv (h.unit.app Y), ?_⟩
    refine (h.homEquiv X (L.obj Y)).injective ?_
    rw [h.homEquiv_map_eq_comp_unit, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

variable (G : A ⥤ C)

/-- **Faithfulness of a left adjoint restricted along a functor.**  If `G` is faithful and the
unit of the adjunction is a monomorphism at every object in the image of `G`, then `G ⋙ L` is
faithful.  Only the objects in the image of `G` are constrained, which is what
`CategoryTheory.Adjunction.faithful_L_of_mono_unit_app` does not allow.

Faithfulness of `G` is an explicit hypothesis rather than an instance because the categories
this is applied to are presented through two definitionally equal but syntactically different
`CategoryTheory.Category` instances, which instance search does not identify. -/
@[sga "4 I 6.4" "more general"]
public theorem faithful_comp_L_of_mono_unit_app (hG : G.Faithful)
    (hu : ∀ a : A, Mono (h.unit.app (G.obj a))) : (G ⋙ L).Faithful where
  map_injective {X Y f g} hfg := by
    have := hu Y
    have := hG
    refine G.map_injective ((cancel_mono (h.unit.app (G.obj Y))).mp ?_)
    rw [← h.unit_naturality (G.map f), ← h.unit_naturality (G.map g)]
    exact congrArg _ (congrArg R.map hfg)

/-- **Fullness of a left adjoint restricted along a functor.**  If `G` is full and the unit of
the adjunction is an isomorphism at every object in the image of `G`, then `G ⋙ L` is full.
Fullness of `G` is an explicit hypothesis for the reason given on
`CategoryTheory.Adjunction.faithful_comp_L_of_mono_unit_app`. -/
@[sga "4 IV 4.3.5" "partial"]
public theorem full_comp_L_of_isIso_unit_app (hG : G.Full)
    (hu : ∀ a : A, IsIso (h.unit.app (G.obj a))) : (G ⋙ L).Full where
  map_surjective {X Y} f := by
    have := hG
    obtain ⟨β, hβ⟩ := (h.bijective_map_of_isIso_unit_app (G.obj X) (hu Y)).2 f
    obtain ⟨γ, hγ⟩ := G.map_surjective β
    exact ⟨γ, by rw [Functor.comp_map, hγ]; exact hβ⟩

end CategoryTheory.Adjunction

namespace AlgebraicGeometry

/-- **A morphism of sheaves of modules on a scheme is an isomorphism as soon as it is one on
sections over every affine open.**  The affine opens form a basis of the topology, so the
underlying morphism of abelian sheaves is an isomorphism, and `SheafOfModules.toSheaf` reflects
isomorphisms. -/
public theorem Scheme.Modules.isIso_of_isIso_app_affineOpens {S : Scheme.{u}}
    {M N : SheafOfModules.{u} S.ringCatSheaf} (f : M ⟶ N)
    (h : ∀ U : S.affineOpens,
      IsIso (((SheafOfModules.toSheaf.{u} S.ringCatSheaf).map f).hom.app (op U.1))) :
    IsIso f := by
  have : IsIso ((SheafOfModules.toSheaf.{u} S.ringCatSheaf).map f) :=
    TopCat.Sheaf.isIso_iff_isIso_basis (B := fun U : S.affineOpens => U.1)
      (by simpa using S.isBasis_affineOpens) h
  have : (SheafOfModules.toSheaf.{u} S.ringCatSheaf ⋙
      sheafToPresheaf (Opens.grothendieckTopology ↥S) AddCommGrpCat.{u}).ReflectsIsomorphisms :=
    inferInstanceAs (SheafOfModules.forget.{u} S.ringCatSheaf ⋙
      PresheafOfModules.toPresheaf _).ReflectsIsomorphisms
  have : (SheafOfModules.toSheaf.{u} S.ringCatSheaf).ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_comp _ (sheafToPresheaf _ _)
  exact isIso_of_reflects_iso f (SheafOfModules.toSheaf.{u} S.ringCatSheaf)

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An affine open of `S`, as an object of the big fppf site of `S`, is a quasi-compact object
of that site: its underlying scheme is affine, hence a quasi-compact space. -/
public theorem isQuasiCompactObject_opensToBig_affineOpen (U : S.affineOpens) :
    (topology B S hS).IsQuasiCompactObject ((opensToBig B S hS).obj U.1) :=
  isQuasiCompactObject_of_compactSpace B S hS _
    (inferInstanceAs (CompactSpace ↥((U.1 : Scheme.{u}))))

/-- **The unit of the associated-module adjunction is an isomorphism at a free module**, for an
arbitrary scheme `S`.

Both sides are Zariski sheaves on `S`, and over an affine open `U` the unit is an isomorphism
by `SheafOfModules.isIso_toSheaf_map_unit_app_free_app`: `U` is a quasi-compact object of the
small Zariski site, `U` viewed in the big fppf site is a quasi-compact object there, and the
comparison of structure sheaves is an isomorphism at `U`.  The affine opens are a basis, so the
unit is an isomorphism. -/
public theorem isIso_unit_app_free (I : Type u) :
    IsIso ((associatedModuleAdjunction B S hS).unit.app
      (SheafOfModules.free (R := S.ringCatSheaf) I)) :=
  Scheme.Modules.isIso_of_isIso_app_affineOpens _ fun U =>
    SheafOfModules.isIso_toSheaf_map_unit_app_free_app (structureMap B S hS) U.1
      (Stacks.SheafOfModules.isQuasiCompactObject_of_isCompact (X := TopCat.of ↥S) U.1
        (by simpa using U.2.isCompact))
      (isQuasiCompactObject_opensToBig_affineOpen B S hS U)
      (isIso_structureMap_hom_app B S hS (op U.1)) I

/-- **Fullness of `𝓕 ↦ 𝓕^a` on free modules**, with no hypothesis on `S`.  This is
`AlgebraicGeometry.BigFppfOver.isFullOnFree_of_compactSpace` with `CompactSpace ↥S` removed: the
route through the terminal object of the big fppf site needs `S` quasi-compact, the route
through a basis of affine opens does not. -/
public theorem isFullOnFree : IsFullOnFree B S hS :=
  isFullOnFree_of_isIso_unit B S hS (isIso_unit_app_free B S hS)

/-- **Stacks 03DX (1), essential surjectivity, local step, for `τ = fppf`**, with no remaining
hypothesis: this is
`AlgebraicGeometry.BigFppfOver.exists_isQuasicoherent_iso_associatedModule_of_cokernelFree` with
`AlgebraicGeometry.BigFppfOver.IsFullOnFree` discharged by
`AlgebraicGeometry.BigFppfOver.isFullOnFree`.

It is still not a covering set for Stacks 03DX (1), which is an equivalence of categories: this
is the local step of one half of it, and the globalization over an fppf covering is the appeal
to the effectivity of descent, Stacks 023T. -/
public theorem exists_isQuasicoherent_iso_associatedModule_of_cokernelFree' {I₁ I₂ : Type u}
    (α : SheafOfModules.free (R := structureSheaf B S hS) I₂ ⟶ SheafOfModules.free I₁)
    {G : SheafOfModules.{u} (structureSheaf B S hS)}
    {π : SheafOfModules.free (R := structureSheaf B S hS) I₁ ⟶ G} (hπ : α ≫ π = 0)
    (hc : IsColimit (CokernelCofork.ofπ π hπ)) :
    ∃ G' : S.Modules, G'.IsQuasicoherent ∧
      Nonempty ((associatedModule B S hS).obj G' ≅ G) :=
  exists_isQuasicoherent_iso_associatedModule_of_cokernelFree B S hS (isFullOnFree B S hS)
    α hπ hc

/-- **Stacks 0GN7 with free target.**  For every `𝒪_S`-module `𝓕` and every type `I`, the map
`Hom(𝓕, ⊕_I 𝒪_S) ⟶ Hom(𝓕^a, ⊕_I 𝒪)` given by `β ↦ β^a` is bijective.

This is full faithfulness of `𝓕 ↦ 𝓕^a` at every pair whose second entry is free, with no
quasi-coherence or quasi-compactness hypothesis anywhere; it is the whole of Stacks 0GN7 for the
free modules, since a free module is quasi-coherent. -/
public theorem bijective_associatedModule_map_free (M : S.Modules) (I : Type u) :
    Function.Bijective (fun β : M ⟶ SheafOfModules.free (R := S.ringCatSheaf) I =>
      (associatedModule B S hS).map β) :=
  (associatedModuleAdjunction B S hS).bijective_map_of_isIso_unit_app M
    (isIso_unit_app_free B S hS I)

/-- **Stacks 0GN7 at the big fppf site of `S`**, as a hypothesis: the unit
`𝓕 ⟶ (𝓕^a)|_{S_Zar}` of the associated-module adjunction is an isomorphism at every
quasi-coherent `𝒪_S`-module.

By `AlgebraicGeometry.BigFppfOver.isIso_unit_app_free` it holds at every free module; what it
asks for beyond that is the sections description of `𝓕^a`, Stacks 070S (1).  It is named here,
in the style of `AlgebraicGeometry.BigFppfOver.AssociatedModuleIsQuasicoherent`, so that the
results below can be read against the source and so that the attribute can be placed with no
change to any proof as soon as it is discharged. -/
public abbrev UnitIsoOnQuasicoherent : Prop :=
  ∀ M : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory,
    IsIso ((associatedModuleAdjunction B S hS).unit.app M.obj)

/-- **Stacks 0GN7, the fullness half**, over
`AlgebraicGeometry.BigFppfOver.UnitIsoOnQuasicoherent`.  This is one of the two instances
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimitsOfSize`
consumes. -/
public theorem full_associatedModuleQcoh (h : UnitIsoOnQuasicoherent B S hS) :
    (associatedModuleQcoh B S hS).Full :=
  (associatedModuleAdjunction B S hS).full_comp_L_of_isIso_unit_app
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι (ObjectProperty.full_ι _) h

/-- **Stacks 0GN7, the faithfulness half**, over
`AlgebraicGeometry.BigFppfOver.UnitIsoOnQuasicoherent` — of which only the weaker statement that
the unit is a monomorphism at the quasi-coherent modules is used. -/
public theorem faithful_associatedModuleQcoh (h : UnitIsoOnQuasicoherent B S hS) :
    (associatedModuleQcoh B S hS).Faithful :=
  (associatedModuleAdjunction B S hS).faithful_comp_L_of_mono_unit_app
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι (ObjectProperty.faithful_ι _) fun M => by
      have := h M
      exact inferInstanceAs
        (Mono ((associatedModuleAdjunction B S hS).unit.app M.obj))

/-- **Stacks 0GN7** for `τ = fppf`, over
`AlgebraicGeometry.BigFppfOver.UnitIsoOnQuasicoherent`: the functor `𝓕 ↦ 𝓕^a` from the
quasi-coherent `𝒪_S`-modules to the modules on the big fppf site of `S` is fully faithful. -/
public noncomputable def fullyFaithfulAssociatedModuleQcoh (h : UnitIsoOnQuasicoherent B S hS) :
    (associatedModuleQcoh B S hS).FullyFaithful :=
  have := full_associatedModuleQcoh B S hS h
  have := faithful_associatedModuleQcoh B S hS h
  .ofFullyFaithful _

end BigFppfOver

end AlgebraicGeometry

end
