module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.Comparison
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentSheaf

/-!
# The unit of the associated-module adjunction at a quasi-coherent module

Stacks 0GN7 says that `𝓕 ↦ 𝓕^a` is fully faithful on quasi-coherent modules, and
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FullyFaithful` reduces it to the single
statement `AlgebraicGeometry.BigFppfOver.UnitIsoOnQuasicoherent`: the unit
`𝓕 ⟶ (𝓕^a)|_{S_Zar}` of `AlgebraicGeometry.BigFppfOver.associatedModuleAdjunction` is an
isomorphism at every quasi-coherent `𝓕`.  This file proves that statement **from the sheaf
condition for the pullback-sections presheaf**, and hence from Stacks 03DT.

The unit argument itself is given for **each of the five topologies**
`τ ∈ {Zariski, étale, smooth, syntomic, fppf}`, as
`AlgebraicGeometry.BigFppfOver.isIso_baseUnit_app_of_isSheaf`, and the fppf statement
`AlgebraicGeometry.BigFppfOver.isIso_unit_app_of_isSheaf` is its `τ = fppf` instance; the file
is described below in the fppf case, which is the one the rest of this chain consumes.  What the
`τ`-form needs beyond the fppf one is nothing: Stacks 070S (1) is available at every `τ` as
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSections`, and the comparison morphisms are
one morphism serving all five sites.  The `τ`-form's sheaf hypothesis is discharged in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseFullyFaithful`, which is where
Stacks 0GN7 for the big site is proved and tagged.

The route is the one the source takes.  Stacks 070S (1),
`AlgebraicGeometry.BigFppfOver.associatedModuleIsoSections`, presents `𝓕^a` as the fppf
sheafification of the presheaf `(f : T → S) ↦ Γ(T, f^*𝓕)` of Stacks 03DS.  Over an open `U` of
`S` the unit is then the composite of two maps: the map which pulls a section of `𝓕` over `U`
back to the open subscheme `U`, which is
`AlgebraicGeometry.BigFppfOver.sectionsUnit`; and the sheafification map of the
pullback-sections presheaf, evaluated at `U` viewed in the big fppf site.  The first is an
isomorphism because pullback along an open immersion is restriction, and the second is an
isomorphism exactly when the pullback-sections presheaf is already a sheaf — which is Stacks
03DT.

Taking sections of a sheafification is therefore **not** what makes the unit an isomorphism:
Stacks 070S (1) alone does not suffice, because the sections of a sheafification at an object
are not the sections of the presheaf there.  What is needed beyond 070S (1) is the sheaf
condition itself, and in this library that is
`AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_fpqc`, which carries the hypothesis
`AlgebraicGeometry.FpqcDescentOfQuasicoherentHoms` — the full-faithfulness half of Stacks 023T.
See the implementation notes.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.toOver`: the big fppf category over `S`, mapped to the schemes
  over `S`; it remembers the structure morphism, which is what the pullback-sections presheaf
  needs.

## Main results

* `CategoryTheory.isIso_left_of_comp_eq` and
  `CategoryTheory.isIso_left_of_comp_eq_comp`: cancelling an isomorphism on the right of a
  composite which is known to be an isomorphism, stated with the objects as variables so that
  the two spellings of a middle object never have to be identified.
* `CategoryTheory.Adjunction.unit_comp_map_unit_comp`: for two adjunctions `LP ⊣ RP` and
  `LS ⊣ RS` and a morphism `c` out of `LP.obj X`, the transpose of the `LS`-unit at `LP.obj X`
  becomes, after composing with `RP RS LS c`, the transpose of `c` composed with the `LS`-unit
  at the target of `c`.
* `CategoryTheory.Adjunction.isIso_unit_app_of_isIso_unit_app`: two left adjoints of one
  functor have their units isomorphisms at the same objects.
* `AlgebraicGeometry.isIso_pullbackSectionHom_ι`: **pulling a section of a module back to an
  open subscheme is bijective**, for an arbitrary module on an arbitrary scheme.
* `AlgebraicGeometry.BigFppfOver.isIso_sectionsUnit`: consequently
  `AlgebraicGeometry.BigFppfOver.sectionsUnit` is an isomorphism.
* `AlgebraicGeometry.BigFppfOver.isIso_baseUnit_app_of_isSheaf`: **the unit of the
  associated-module adjunction of `(Sch/S)_τ` is an isomorphism at a quasi-coherent module whose
  pullback-sections presheaf is a `τ`-sheaf**, for each of the five topologies, and
  `AlgebraicGeometry.BigFppfOver.isIso_unit_app_of_isSheaf`: its `τ = fppf` instance.
* `AlgebraicGeometry.BigFppfOver.isSheaf_sectionsPresheafOfModules`: **Stacks 03DT on the big
  fppf site of `S`**, granted `AlgebraicGeometry.FpqcDescentOfQuasicoherentHoms`.
* `AlgebraicGeometry.BigFppfOver.unitIsoOnQuasicoherent_of_fpqcDescent`:
  `AlgebraicGeometry.BigFppfOver.UnitIsoOnQuasicoherent` over that hypothesis, and
  `AlgebraicGeometry.BigFppfOver.full_associatedModuleQcoh_of_fpqcDescent`,
  `AlgebraicGeometry.BigFppfOver.faithful_associatedModuleQcoh_of_fpqcDescent` and
  `AlgebraicGeometry.BigFppfOver.fullyFaithfulAssociatedModuleQcoh_of_fpqcDescent`:
  **Stacks 0GN7 for `τ = fppf` over that hypothesis.**

## Implementation notes

Nothing here is tagged, and the reason is that every statement below still carries a hypothesis:
what this file does is replace the bespoke
`AlgebraicGeometry.BigFppfOver.UnitIsoOnQuasicoherent` by
`AlgebraicGeometry.FpqcDescentOfQuasicoherentHoms`, which is the hypothesis of Stacks 03DT and
is shared with `StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.Basic`.  That
hypothesis is no longer open — it is the theorem
`AlgebraicGeometry.fpqcDescentOfQuasicoherentHoms` of
`StacksFrontier.AlgebraicGeometry.Descent.FpqcHomSheafRefinement`, which this file does not import
— so the hypothesis-free forms, and the `stacks` attributes, live downstream in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FullyFaithfulUnconditional` (the fppf
case) and `StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseFullyFaithful` (every `τ`,
where **Stacks 0GN7 for the big site is tagged**).

The identification of the unit is `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`
applied to the two adjunctions whose left adjoints are
`CategoryTheory.SheafOfModules.pullback` and its description
`CategoryTheory.SheafOfModules.PullbackConstruction.adjunction` as a sheafified presheaf-level
pullback: the forgetful functor carries the unit of the second to the transpose of the
sheafification map, and that is an equality of presheaf morphisms which holds by `rfl`.

Three transparency obstacles are avoided by stating the step with the objects as variables rather
than by rewriting in place.  The middle object of a
composite has two spellings — sections of a pushforward over an open, and sections over the
preimage of that open — and `CategoryTheory.IsIso` carries the objects explicitly, so an
instance for a factor is not found at the composite's spelling even when the two are
definitionally equal; `CategoryTheory.isIso_left_of_comp_eq_comp` takes the factors as
hypotheses instead.  For the same reason bijectivity of
`AlgebraicGeometry.pullbackSectionHom` is assembled as a statement about *functions*, through
`CategoryTheory.ConcreteCategory.isIso_iff_bijective`, rather than as a composite of
isomorphisms.  And `CategoryTheory.NatIso.isIso_app_of_isIso` is not found for an isomorphism
of functors out of `AlgebraicGeometry.Scheme.Modules`, whose `CategoryTheory.Category` instance
is definitionally but not syntactically the `CategoryTheory.SheafOfModules` one, so the
cancellation is done inside `CategoryTheory.Adjunction.isIso_unit_app_of_isIso_unit_app`, where
the categories are variables.

## References

* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe v₁ v₂ v₃ w₁ w₂ w₃ u

namespace CategoryTheory

/-- **Cancelling an isomorphism on the right.**  If `f ≫ g` is known to equal an isomorphism
`h` and `g` is an isomorphism, then `f` is an isomorphism.  The three morphisms are explicit
arguments and the isomorphism hypotheses are explicit too, so that the statement applies
whichever of the definitionally equal spellings of the middle object the composite was
elaborated at. -/
public theorem isIso_left_of_comp_eq {C : Type w₁} [Category.{v₁} C] {X Y Z : C} {f : X ⟶ Y}
    {g : Y ⟶ Z} {h : X ⟶ Z} (hfg : f ≫ g = h) (hg : IsIso g) (hh : IsIso h) : IsIso f := by
  have := hg
  have : IsIso (f ≫ g) := hfg ▸ hh
  exact IsIso.of_isIso_comp_right f g

/-- **Cancelling an isomorphism on the right of a composite of isomorphisms.**  This is
`CategoryTheory.isIso_left_of_comp_eq` with the right-hand side presented as a composite, which
is how the comparisons of this file arise. -/
public theorem isIso_left_of_comp_eq_comp {C : Type w₁} [Category.{v₁} C] {W X Y Z : C}
    {f : X ⟶ Y} {g : Y ⟶ Z} {u : X ⟶ W} {v : W ⟶ Z} (hfg : f ≫ g = u ≫ v) (hg : IsIso g)
    (hu : IsIso u) (hv : IsIso v) : IsIso f := by
  have := hu
  have := hv
  exact isIso_left_of_comp_eq hfg hg inferInstance

namespace Adjunction

variable {C : Type w₁} [Category.{v₁} C] {D : Type w₂} [Category.{v₂} D]
  {E : Type w₃} [Category.{v₃} E] {LP : C ⥤ D} {RP : D ⥤ C} {LS : D ⥤ E} {RS : E ⥤ D}

/-- **Transposing a unit through a second adjunction.**  Let `LP ⊣ RP` and `LS ⊣ RS` be
adjunctions and let `c : LP.obj X ⟶ Q`.  The transpose of the `LS`-unit at `LP.obj X`, composed
with the image under `RP RS LS` of `c`, is the transpose `su` of `c` composed with the
`LS`-unit at `Q`.

Applied to the presheaf-level pullback--pushforward adjunction and to the sheafification of
presheaves of modules, this says that the unit of the associated-module adjunction becomes, up
to isomorphisms, the map which pulls sections back followed by sheafification. -/
public theorem unit_comp_map_unit_comp (adjP : LP ⊣ RP) (adjS : LS ⊣ RS) (X : C) {Q : D}
    (c : LP.obj X ⟶ Q) {su : X ⟶ RP.obj Q} (hc : adjP.unit.app X ≫ RP.map c = su) :
    (adjP.unit.app X ≫ RP.map (adjS.unit.app (LP.obj X))) ≫ RP.map (RS.map (LS.map c)) =
      su ≫ RP.map (adjS.unit.app Q) := by
  rw [Category.assoc, ← RP.map_comp, adjS.unit_naturality c, RP.map_comp, ← Category.assoc, hc]

/-- **Two left adjoints of one functor have their units isomorphisms at the same objects.**  The
comparison of the two left adjoints is `CategoryTheory.Adjunction.leftAdjointUniq`, and
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` identifies the one unit with the other
composed with its image. -/
public theorem isIso_unit_app_of_isIso_unit_app {L L' : C ⥤ D} {R : D ⥤ C} (adj1 : L ⊣ R)
    (adj2 : L' ⊣ R) (X : C) (h : IsIso (adj2.unit.app X)) : IsIso (adj1.unit.app X) :=
  isIso_left_of_comp_eq (unit_leftAdjointUniq_hom_app adj1 adj2 X) inferInstance h

end Adjunction

end CategoryTheory

namespace AlgebraicGeometry

/-- A restriction map of a module on a scheme between two opens which are equal is an
isomorphism: a morphism of the poset of opens between equal objects is `eqToHom`. -/
public theorem Scheme.Modules.isIso_presheaf_map_of_eq {X : Scheme.{u}} (M : X.Modules)
    {V W : X.Opens} (h : V ≤ W) (hVW : W = V) : IsIso (M.presheaf.map (homOfLE h).op) := by
  rw [Subsingleton.elim (homOfLE h) (eqToHom hVW.symm), eqToHom_op]
  infer_instance

/-- **The unit of the pullback--pushforward adjunction of an open immersion is an isomorphism on
sections over its own open.**  Pullback along the inclusion of an open `U` is restriction to `U`
(`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`), and the unit of the restriction
adjunction is, over `U`, the restriction map to `U.ι ''ᵁ (U.ι ⁻¹ᵁ U) = U`. -/
public theorem Scheme.Modules.isIso_unit_app_app_ι {S : Scheme.{u}} (F : S.Modules)
    (U : S.Opens) :
    IsIso (((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F).app U) := by
  rw [← Adjunction.unit_leftAdjointUniq_hom_app
    (Scheme.Modules.restrictAdjunction U.ι)
    (Scheme.Modules.pullbackPushforwardAdjunction U.ι) F, Scheme.Modules.Hom.comp_app]
  have h2 : IsIso (((Scheme.Modules.restrictAdjunction U.ι).unit.app F).app U) := by
    rw [Scheme.Modules.restrictAdjunction_unit_app_app]
    exact F.isIso_presheaf_map_of_eq _ (by simp)
  exact IsIso.comp_isIso

/-- **Pulling a section of a module back to an open subscheme is bijective.**  For an open `U`
of `S` and any `𝒪_S`-module `F`, the map `Γ(F, U) ⟶ Γ(U.ι^*F, ⊤)` of
`AlgebraicGeometry.pullbackSectionHom` is an isomorphism: it is the unit of the
pullback--pushforward adjunction of `U.ι` over `U`, which is an isomorphism by
`AlgebraicGeometry.Scheme.Modules.isIso_unit_app_app_ι`, followed by the restriction map along
`U.ι ⁻¹ᵁ U = ⊤`.

Bijectivity of the underlying functions is composed rather than the isomorphisms themselves,
because the middle object of the composite has two definitionally equal spellings; see the
implementation notes. -/
public theorem isIso_pullbackSectionHom_ι {S : Scheme.{u}} (F : S.Modules) (U : S.Opens) :
    IsIso (pullbackSectionHom U.ι F U ⊤ (Scheme.Opens.top_le_ι_preimage le_rfl)) := by
  have h1 := Scheme.Modules.isIso_unit_app_app_ι F U
  have h4 := Scheme.Modules.isIso_presheaf_map_of_eq ((Scheme.Modules.pullback U.ι).obj F)
    (Scheme.Opens.top_le_ι_preimage (V := U) (U := U) le_rfl) (by simp)
  have b1 := ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F).app U)
  have b2 := ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.pullback U.ι).obj F).presheaf.map
        (homOfLE (Scheme.Opens.top_le_ι_preimage (V := U) (U := U) le_rfl)).op)
  exact (ConcreteCategory.isIso_iff_bijective _).2 (b2.comp b1)

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The big fppf category over `S`, mapped to the schemes over `S`.  Unlike
`AlgebraicGeometry.BigFppfOver.toScheme` it remembers the structure morphism, which is what the
pullback-sections presheaf of Stacks 03DS needs. -/
public abbrev toOver : BigFppfOver B S hS ⥤ Over S :=
  Over.post (X := B.obj hS) B.inclusion

/-- Forgetting the structure morphism takes the canonical functor to the schemes over `S` to
the canonical functor to all schemes. -/
public theorem toOver_comp_forget : toOver B S hS ⋙ Over.forget S = toScheme B S hS := rfl

/-- The canonical functor from the big fppf category over `S` to the schemes over `S`
preserves fibre products: it does so after forgetting the structure morphism, and
`CategoryTheory.Over.forget` reflects fibre products. -/
public instance preservesPullbacks_toOver :
    PreservesLimitsOfShape WalkingCospan (toOver B S hS) := by
  have : PreservesLimitsOfShape WalkingCospan (toOver B S hS ⋙ Over.forget S) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (toScheme B S hS))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget S)

/-- The canonical functor from the big fppf category over `S` to the schemes over `S` is
compatible-preserving for the fpqc topology: a cospan of the big fppf category is completed by
its fibre product there, and the lift is a morphism over `S` because the two projections are. -/
public theorem compatiblePreserving_toOver :
    CompatiblePreserving.{u} (Scheme.fpqcTopology.{u}.over S) (toOver B S hS) := by
  refine Stacks.Sites.compatiblePreserving_of_lift _ _ ?_
  intro Y₁ Y₂ Z g₁ g₂ T f₁ f₂ e
  have h : IsPullback ((toOver B S hS).map (pullback.fst g₁ g₂))
      ((toOver B S hS).map (pullback.snd g₁ g₂)) ((toOver B S hS).map g₁)
      ((toOver B S hS).map g₂) :=
    (IsPullback.of_hasPullback g₁ g₂).map (toOver B S hS)
  exact ⟨pullback g₁ g₂, pullback.fst g₁ g₂, pullback.snd g₁ g₂, h.lift f₁ f₂ e,
    pullback.condition, h.lift_fst f₁ f₂ e, h.lift_snd f₁ f₂ e⟩

/-- The canonical functor from the big fppf category over `S` to the schemes over `S` is cover
preserving from the localized fppf topology to the localized fpqc topology.  This is
`AlgebraicGeometry.BigFppfOver.coverPreserving_toScheme` read through the identification of
sieves on an object of the schemes over `S` with sieves on its underlying scheme. -/
public theorem coverPreserving_toOver :
    CoverPreserving (topology B S hS) (Scheme.fpqcTopology.{u}.over S) (toOver B S hS) := by
  refine ⟨fun {X R} hR => ?_⟩
  have key : Sieve.overEquiv ((toOver B S hS).obj X) (R.functorPushforward (toOver B S hS)) =
      R.functorPushforward (toScheme B S hS) :=
    (Sieve.functorPushforward_comp (toOver B S hS) (Over.forget S) R).symm
  rw [GrothendieckTopology.mem_over_iff, key]
  exact (coverPreserving_toScheme B S hS).cover_preserve hR

/-- **Stacks 03DT on the big fppf site of `S`, granted the descent of morphisms of
quasi-coherent modules.**  The pullback-sections presheaf of modules of a quasi-coherent module
`F` on `S` is a sheaf on the big fppf site of `S`.

The fpqc sheaf condition on the schemes over `S` is
`AlgebraicGeometry.isSheaf_presheafHom` read through
`AlgebraicGeometry.quasiCoherentPresheafIsoPresheafHom`; it is carried to the big fppf site by
`AlgebraicGeometry.BigFppfOver.compatiblePreserving_toOver` and
`AlgebraicGeometry.BigFppfOver.coverPreserving_toOver`, one covering sieve at a time, exactly as
for the structure sheaf. -/
public theorem isSheaf_sectionsPresheafOfModules (hd : FpqcDescentOfQuasicoherentHoms.{u})
    (F : S.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (topology B S hS) (sectionsPresheafOfModules B S hS F).presheaf := by
  have htype : Presheaf.IsSheaf (Scheme.fpqcTopology.{u}.over S)
      (quasiCoherentPresheafFunctor S F ⋙ CategoryTheory.forget AddCommGrpCat) :=
    (Presheaf.isSheaf_of_iso_iff (quasiCoherentPresheafIsoPresheafHom F)).mpr
      (isSheaf_presheafHom hd (Scheme.unitModule S) F)
  rw [sectionsPresheafOfModules_presheaf]
  refine Stacks.Sites.isSheaf_addCommGrpCat_of_isSheaf_forget _ _ ?_
  intro X R hR
  exact Stacks.Sites.isSheafFor_op_comp (compatiblePreserving_toOver B S hS) ⟨_, htype⟩ R
    ((coverPreserving_toOver B S hS).cover_preserve hR)

/-- The sheafification map of a presheaf of modules on one of the five big sites of `S` which is
already a sheaf there is an isomorphism.  The underlying map of presheaves of abelian groups is
`CategoryTheory.toSheafify`, and `CategoryTheory.PresheafOfModules.toPresheaf` reflects
isomorphisms. -/
public theorem isIso_baseSheafificationAdjunction_unit_app (τ : SiteKind)
    (Q : PresheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ).obj)
    (hQ : Presheaf.IsSheaf (baseOverTopology B S hS τ) Q.presheaf) :
    IsIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).unit.app Q) := by
  have h1 : IsIso (CategoryTheory.toSheafify (baseOverTopology B S hS τ) Q.presheaf) :=
    CategoryTheory.isIso_toSheafify _ hQ
  rw [← isIso_iff_of_reflects_iso _
      (PresheafOfModules.toPresheaf (FibredSite.baseRingStructureSheaf B S hS τ).obj),
    PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact h1

/-- The sheafification map of a presheaf of modules on the big fppf site which is a sheaf is an
isomorphism.  The `τ = fppf` case of
`AlgebraicGeometry.BigFppfOver.isIso_baseSheafificationAdjunction_unit_app`. -/
public theorem isIso_sheafificationAdjunction_unit_app
    (Q : PresheafOfModules.{u} (structureSheaf B S hS).obj)
    (hQ : Presheaf.IsSheaf (topology B S hS) Q.presheaf) :
    IsIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (structureSheaf B S hS).obj)).unit.app Q) :=
  isIso_baseSheafificationAdjunction_unit_app B S hS .fppf Q hQ

/-- **Pulling sections back is an isomorphism.**  The morphism
`AlgebraicGeometry.BigFppfOver.sectionsUnit` from `F` to the restriction, along the inclusion of
the small Zariski site of `S`, of the pullback-sections presheaf is an isomorphism: its
component at an open `U` is the map of `AlgebraicGeometry.isIso_pullbackSectionHom_ι`. -/
public theorem isIso_sectionsUnit (F : S.Modules) [F.IsQuasicoherent] :
    IsIso (sectionsUnit B S hS F) := by
  rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf S.ringCatSheaf.obj),
    NatTrans.isIso_iff_isIso_app]
  intro U
  exact isIso_pullbackSectionHom_ι F U.unop

/-- **The unit of the associated-module adjunction of `(Sch/S)_τ` is an isomorphism at a
quasi-coherent module whose pullback-sections presheaf is a `τ`-sheaf**, for each of the five
topologies `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.

`CategoryTheory.SheafOfModules.pullbackIso` presents the associated-module functor as the
`τ`-sheafification of the presheaf-level pullback, and
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` therefore reduces the claim to the unit
of `CategoryTheory.SheafOfModules.PullbackConstruction.adjunction`, which the forgetful functor
carries to the transpose of the sheafification map.  By
`AlgebraicGeometry.BigFppfOver.unit_comp_map_sectionsComparison` and
`CategoryTheory.Adjunction.unit_comp_map_unit_comp` that transpose agrees, after composing with
the `τ`-sheafification of `AlgebraicGeometry.BigFppfOver.sectionsComparison` — an isomorphism by
Stacks 070S (1), which
`AlgebraicGeometry.BigFppfOver.isIso_baseSheafification_map_sectionsComparison` supplies at every
`τ` — with `AlgebraicGeometry.BigFppfOver.sectionsUnit` followed by the sheafification map of the
pullback-sections presheaf.  Both of those are isomorphisms, the first always and the second by
the hypothesis.

Nothing here is fppf-specific: `AlgebraicGeometry.BigFppfOver.baseStructureMap` has
`AlgebraicGeometry.BigFppfOver.structureMap` as its body, so the presheaf-level morphisms
`AlgebraicGeometry.BigFppfOver.sectionsUnit` and
`AlgebraicGeometry.BigFppfOver.sectionsComparison` serve all five sites unchanged and the
identification `hforget` of the two spellings of the unit still holds by `rfl`. -/
public theorem isIso_baseUnit_app_of_isSheaf (τ : SiteKind) (F : S.Modules)
    [F.IsQuasicoherent]
    (hQ : Presheaf.IsSheaf (baseOverTopology B S hS τ)
      (sectionsPresheafOfModules B S hS F).presheaf) :
    IsIso ((baseAssociatedModuleAdjunction B S hS τ).unit.app F) := by
  have hB : IsIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).unit.app
        (sectionsPresheafOfModules B S hS F)) :=
    isIso_baseSheafificationAdjunction_unit_app B S hS τ _ hQ
  have hA : IsIso (sectionsUnit B S hS F) := isIso_sectionsUnit B S hS F
  have hc : IsIso ((PresheafOfModules.sheafification.{u}
      (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).map
        (sectionsComparison B S hS F)) :=
    isIso_baseSheafification_map_sectionsComparison B S hS τ F
  have hc2 : IsIso ((PresheafOfModules.pushforward.{u} (baseStructureMap B S hS τ).hom).map
      ((SheafOfModules.forget (FibredSite.baseRingStructureSheaf B S hS τ) ⋙
          PresheafOfModules.restrictScalars
            (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).map
        ((PresheafOfModules.sheafification.{u}
          (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).map
            (sectionsComparison B S hS F)))) :=
    inferInstance
  have hB2 : IsIso ((PresheafOfModules.pushforward.{u} (baseStructureMap B S hS τ).hom).map
      ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).unit.app
        (sectionsPresheafOfModules B S hS F))) := inferInstance
  have hkey := Adjunction.unit_comp_map_unit_comp
      (PresheafOfModules.pullbackPushforwardAdjunction.{u} (baseStructureMap B S hS τ).hom)
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj))
      ((SheafOfModules.forget S.ringCatSheaf).obj F)
      (sectionsComparison B S hS F)
      (unit_comp_map_sectionsComparison B S hS F)
  have hforget : (SheafOfModules.forget S.ringCatSheaf).map
        ((SheafOfModules.PullbackConstruction.adjunction.{u}
          (baseStructureMap B S hS τ)).unit.app F) =
      (PresheafOfModules.pullbackPushforwardAdjunction.{u}
          (baseStructureMap B S hS τ).hom).unit.app
          ((SheafOfModules.forget S.ringCatSheaf).obj F) ≫
        (PresheafOfModules.pushforward.{u} (baseStructureMap B S hS τ).hom).map
          ((PresheafOfModules.sheafificationAdjunction
              (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).unit.app
            ((PresheafOfModules.pullback.{u} (baseStructureMap B S hS τ).hom).obj
              ((SheafOfModules.forget S.ringCatSheaf).obj F))) := rfl
  rw [← hforget] at hkey
  have h2 : IsIso ((SheafOfModules.forget S.ringCatSheaf).map
      ((SheafOfModules.PullbackConstruction.adjunction.{u}
        (baseStructureMap B S hS τ)).unit.app F)) :=
    isIso_left_of_comp_eq_comp hkey hc2 hA hB2
  have h3 : IsIso ((SheafOfModules.PullbackConstruction.adjunction.{u}
      (baseStructureMap B S hS τ)).unit.app F) :=
    isIso_of_reflects_iso _ (SheafOfModules.forget S.ringCatSheaf)
  exact Adjunction.isIso_unit_app_of_isIso_unit_app
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (baseStructureMap B S hS τ))
    (SheafOfModules.PullbackConstruction.adjunction.{u} (baseStructureMap B S hS τ)) F h3

/-- **The unit of the associated-module adjunction is an isomorphism at a quasi-coherent module
whose pullback-sections presheaf is a sheaf.**  The `τ = fppf` case of
`AlgebraicGeometry.BigFppfOver.isIso_baseUnit_app_of_isSheaf`, which is where the argument is
given; this is the form the rest of the fppf chain consumes. -/
public theorem isIso_unit_app_of_isSheaf (F : S.Modules) [F.IsQuasicoherent]
    (hQ : Presheaf.IsSheaf (topology B S hS)
      (sectionsPresheafOfModules B S hS F).presheaf) :
    IsIso ((associatedModuleAdjunction B S hS).unit.app F) :=
  isIso_baseUnit_app_of_isSheaf B S hS .fppf F hQ

/-- **`AlgebraicGeometry.BigFppfOver.UnitIsoOnQuasicoherent`, granted the descent of morphisms
of quasi-coherent modules.**  The unit `𝓕 ⟶ (𝓕^a)|_{S_Zar}` is an isomorphism at every
quasi-coherent `𝒪_S`-module, over the hypothesis of Stacks 03DT. -/
public theorem unitIsoOnQuasicoherent_of_fpqcDescent
    (hd : FpqcDescentOfQuasicoherentHoms.{u}) : UnitIsoOnQuasicoherent B S hS := fun M => by
  have : M.obj.IsQuasicoherent := M.property
  exact isIso_unit_app_of_isSheaf B S hS M.obj
    (isSheaf_sectionsPresheafOfModules B S hS hd M.obj)

/-- **Stacks 0GN7 for `τ = fppf`, the fullness half, over the hypothesis of Stacks 03DT.** -/
public theorem full_associatedModuleQcoh_of_fpqcDescent
    (hd : FpqcDescentOfQuasicoherentHoms.{u}) : (associatedModuleQcoh B S hS).Full :=
  full_associatedModuleQcoh B S hS (unitIsoOnQuasicoherent_of_fpqcDescent B S hS hd)

/-- **Stacks 0GN7 for `τ = fppf`, the faithfulness half, over the hypothesis of Stacks
03DT.** -/
public theorem faithful_associatedModuleQcoh_of_fpqcDescent
    (hd : FpqcDescentOfQuasicoherentHoms.{u}) : (associatedModuleQcoh B S hS).Faithful :=
  faithful_associatedModuleQcoh B S hS (unitIsoOnQuasicoherent_of_fpqcDescent B S hS hd)

/-- **Stacks 0GN7 for `τ = fppf`, over the hypothesis of Stacks 03DT**: the functor
`𝓕 ↦ 𝓕^a` from the quasi-coherent `𝒪_S`-modules to the modules on the big fppf site of `S` is
fully faithful.

The clause is proved for the big fppf site only, and the reason is **not** the functor: the
morphism of ringed sites `((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪_S)` exists for every
`AlgebraicGeometry.SiteKind` as `AlgebraicGeometry.BigFppfOver.baseStructureMap`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseRingedSite.lean:206`) and the
pullback along it is `AlgebraicGeometry.BigFppfOver.baseAssociatedModule`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseRingedSite.lean:232`).  The
restriction
is that the input `hd` is consumed here through fppf-specific sheafification.  (Analogues of
the morphism are available at the coarser topologies as well.)

0GN7 also asserts full faithfulness of the small-site functor `QCoh(𝒪_S) ⥤ QCoh(S_τ, 𝒪)` of
Definition 03DU (4).  That is not this functor, and its full faithfulness is not proved here —
but **the functor itself is in the library**: at `τ = étale` it is
`AlgebraicGeometry.SmallEtale.associatedModule`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleRingedSite.lean:417`), with
its adjunction at `:429` and clauses (2), (3) of Lemma 06VE for it in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.SmallEtaleAssociatedModuleColimits`.
What the small-site half of 0GN7 still needs is the analogue of `hd` below — the unit
`𝓕 ⟶ (𝓕^a)|_{S_Zar}` being an isomorphism at every quasi-coherent `𝓕`, which here is obtained
from fppf-specific sheafification. -/
public noncomputable def fullyFaithfulAssociatedModuleQcoh_of_fpqcDescent
    (hd : FpqcDescentOfQuasicoherentHoms.{u}) : (associatedModuleQcoh B S hS).FullyFaithful :=
  fullyFaithfulAssociatedModuleQcoh B S hS (unitIsoOnQuasicoherent_of_fpqcDescent B S hS hd)

end BigFppfOver

end AlgebraicGeometry

end
