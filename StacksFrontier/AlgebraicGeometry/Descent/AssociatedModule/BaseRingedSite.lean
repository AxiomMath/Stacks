module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.Functor
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposHom

/-!
# The associated-module functor of each of the five big sites of a scheme

`AlgebraicGeometry.BigFppfOver.associatedModule` is the pullback of sheaves of modules along
the morphism of ringed sites `((Sch/S)_fppf, 𝒪) → (S_Zar, 𝒪_S)`.  Nothing in that morphism is
fppf-specific: over an open `U` the comparison of structure sheaves is the identification of
`Γ(𝒪_S, U)` with the global functions of the open subscheme `U`, and the structure sheaf of
each of the five big sites over `S` has the *same* underlying presheaf
(`AlgebraicGeometry.FibredSite.baseRingStructureSheaf_obj` is `rfl`).  What has to be supplied
for a coarser topology is the *continuity* of the inclusion of the small Zariski site, and
continuity gets harder as the target topology gets coarser: a sieve covering for `τ` is
covering for fppf, not conversely.

This module supplies it for all five `τ : SiteKind` at once.  An open covering of an open of
`S` consists of open immersions, and an open immersion is étale, smooth, syntomic and an open
immersion; so the family it cuts out in the big category of schemes is a covering family for
each of the five covering predicates, and the chosen fppf family representing it combinatorially
is one too, because combinatorially equivalent families generate the same presieve.  With
continuity in hand the comparison of structure sheaves is literally the fppf one, and the
associated-module functor, its right adjoint and their adjunction are the pullback, the
pushforward and the pullback–pushforward adjunction along it.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.baseStructureMap`: the comparison of structure sheaves for the
  indicated big site over `S`, the ring half of the morphism of ringed sites
  `((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪_S)`.
* `AlgebraicGeometry.BigFppfOver.baseAssociatedModule`: the associated-module functor
  `S.Modules ⥤ SheafOfModules (FibredSite.baseRingStructureSheaf B S hS τ)` of the indicated
  big site over `S`.
* `AlgebraicGeometry.BigFppfOver.baseRestrictModule`: its right adjoint, restriction along the
  inclusion of the small Zariski site.
* `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleAdjunction`: the adjunction between them.
* `AlgebraicGeometry.Scheme.zariskiRingedTopos` and
  `AlgebraicGeometry.Scheme.zariskiRingedSite`: the ringed topos `(S_Zar, 𝒪_S)` of a scheme, and
  the same data read as a ringed site.
* `AlgebraicGeometry.BigFppfOver.baseRingedTopos`: the ringed topos `((Sch/S)_τ, 𝒪)` of the
  indicated big site over `S`.
* `AlgebraicGeometry.BigFppfOver.baseToZariskiRingedToposHom`: the data of the morphism
  `((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪_S)` of Stacks 070U — the continuous inclusion of the small Zariski
  site and the comparison of structure sheaves — as an `AlgebraicGeometry.RingedToposSiteHom`,
  which records continuity only.  The morphism of ringed sites in the sense of Stacks 03AD, with
  the exactness of the inverse image, is
  `AlgebraicGeometry.BigFppfOver.baseToZariskiRingedSiteHom`, which carries Stacks 070U.

## Main results

* `AlgebraicGeometry.BigFppfOver.sieve₀_mem_baseTopology_of_isOpenImmersion`: a jointly
  surjective family of open immersions generates a covering sieve of each of the five big sites
  of schemes.
* `AlgebraicGeometry.BigFppfOver.coverPreserving_baseOpensToBig` and
  `AlgebraicGeometry.BigFppfOver.isContinuous_baseOpensToBig`: the inclusion of the small
  Zariski site of `S` is cover preserving, hence continuous, into each of the five localized
  topologies on the big fppf category over `S`.
* `AlgebraicGeometry.BigFppfOver.preservesColimitsOfSize_baseAssociatedModule`: the
  associated-module functor of each of the five sites preserves all colimits.
* `AlgebraicGeometry.BigFppfOver.isIso_basePullbackObjUnitToUnit`: it takes the unit object to
  the unit object, the inclusion of the small Zariski site being final.

## Implementation notes

`AlgebraicGeometry.BigFppfOver.sieve₀_mem_baseTopology_of_isOpenImmersion` is stated for an
arbitrary jointly surjective family of open immersions rather than for the family cut out by an
open covering.

The three coarser presieve-level covering predicates — `AlgebraicGeometry.IsZariskiCovering`,
`AlgebraicGeometry.IsEtaleCovering` and `AlgebraicGeometry.SmoothCovering` — transfer to the
chosen fppf representative directly from the equality of presieves.
`AlgebraicGeometry.SyntomicCovering` is instead stated for an indexed family, so it is
transferred through `AlgebraicGeometry.Scheme.presieve₀_mem_precoverage_iff` read at the
representative family itself.

Each of the five morphism properties is named explicitly at the call sites rather than left to
unification: the covering predicates are stated against `AlgebraicGeometry.Scheme.etalePrecoverage`
and `AlgebraicGeometry.Scheme.zariskiPretopology`, which are not syntactically
`AlgebraicGeometry.Scheme.precoverage _`, so an underscore leaves the property a metavariable and
the `IsOpenImmersion`-to-property instance search has nothing to search for.

`AlgebraicGeometry.BigFppfOver.baseStructureMap` is *definitionally* the fppf comparison
`AlgebraicGeometry.BigFppfOver.structureMap`: the two sheaves of rings it compares have the same
underlying presheaves, and the topology enters only through the (proof-irrelevant) sheaf
conditions and the continuity instance.

The small Zariski site `S_Zar` is presented by the opens of the underlying space of `S`, to
which it is equivalent by Tag 020X, and `𝒪_S` is then the structure sheaf of the scheme itself
rather than an isomorphic copy of it.  Accordingly the target of the morphism of ringed sites
is `AlgebraicGeometry.Scheme.zariskiRingedTopos`, while its source is the big site, whose
objects form a type one universe higher.  The two therefore have different object universes,
and the morphism is recorded as an `AlgebraicGeometry.RingedToposSiteHom`, whose geometric
datum is exactly a continuous functor between the underlying sites in the opposite direction,
as in the Stacks convention for a morphism of sites.  The structure sheaves take values in
`CommRingCat`, as a ringed topos does; forgetting commutativity recovers the `RingCat`-valued
comparison `AlgebraicGeometry.BigFppfOver.baseStructureMap` over which the associated-module
functor is formed, so the associated-module functor is the pullback of sheaves of modules
along this morphism.

## References

* [Stacks Project, Tag 070U](https://stacks.math.columbia.edu/tag/070U)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The ringed topos `(S_Zar, 𝒪_S)` of a scheme: the small Zariski site of `S`, presented by
the opens of its underlying space, together with the structure sheaf `𝒪_S`. -/
public def Scheme.zariskiRingedTopos (S : Scheme.{u}) : RingedTopos.{u, u, u} where
  C := S.Opens
  J := Opens.grothendieckTopology ↥S
  O := S.sheaf

/-- The sheaf of rings of `AlgebraicGeometry.Scheme.zariskiRingedTopos S` is `S.sheaf`. -/
@[simp]
public theorem Scheme.zariskiRingedTopos_O (S : Scheme.{u}) :
    S.zariskiRingedTopos.O = S.sheaf := rfl

/-- The ringed site `(S_Zar, 𝒪_S)` of a scheme, in the sense of Stacks 03AD: the same data as
`AlgebraicGeometry.Scheme.zariskiRingedTopos`, read through `AlgebraicGeometry.RingedSite`.  It
is a reducible abbreviation because the sheaf-of-modules and sheafification instances are stated
for the projections `.C`, `.J` and `.O`, which have to reduce at instance transparency for those
instances to be found. -/
public abbrev Scheme.zariskiRingedSite (S : Scheme.{u}) : RingedSite.{u, u, u} where
  C := S.Opens
  J := Opens.grothendieckTopology ↥S
  O := S.sheaf

/-- The sheaf of rings of `AlgebraicGeometry.Scheme.zariskiRingedSite S` is `S.sheaf`. -/
@[simp]
public theorem Scheme.zariskiRingedSite_O (S : Scheme.{u}) :
    S.zariskiRingedSite.O = S.sheaf := rfl

/-- The sheaf of rings of the small Zariski ringed site of a scheme is the scheme's own sheaf of
rings: an `𝒪_S`-module *is* a sheaf of modules on that ringed site, with no comparison. -/
public theorem Scheme.zariskiRingedSite_ringSheaf (S : Scheme.{u}) :
    (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O) = S.ringCatSheaf :=
  rfl

end AlgebraicGeometry

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Continuity of the small Zariski site in each of the five big sites -/

/-- **A jointly surjective family of open immersions covers for every one of the five
topologies.**  An open immersion is flat and locally of finite presentation, étale, smooth,
syntomic and an open immersion, so such a family satisfies all five covering predicates; the
chosen fppf family representing it combinatorially does too, combinatorially equivalent families
generating the same presieve. -/
public theorem sieve₀_mem_baseTopology_of_isOpenImmersion (τ : SiteKind) {X : B.Schemes}
    (E : PreZeroHypercover.{u + 1} X)
    (hsurj : ∀ x : ↥(B.inclusion.obj X), ∃ i, x ∈ Set.range ⇑(B.inclusion.map (E.f i)))
    (himm : ∀ i, IsOpenImmersion (B.inclusion.map (E.f i))) :
    Sieve.generate E.presieve₀ ∈ B.baseTopology τ X := by
  have key : ∀ P : MorphismProperty Scheme.{u},
      (∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z), IsOpenImmersion f → P f) →
      ∀ F : PreZeroHypercover.{u + 1} X, F.presieve₀ = E.presieve₀ →
      (F.map B.inclusion).presieve₀ ∈
        (Scheme.precoverage P).coverings (B.inclusion.obj X) := by
    intro P hP F hF
    rw [PreZeroHypercover.presieve₀_map, hF, ← PreZeroHypercover.presieve₀_map,
      Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨hsurj, fun i => hP _ (himm i)⟩
  have hfppf : IsFppfCovering (κ := B.cutoff) ⟨X, E⟩ := by
    change Presieve.map B.inclusion E.presieve₀ ∈ Scheme.fppfPrecoverage.coverings _
    rw [← PreZeroHypercover.presieve₀_map]
    exact key (@Flat.{u} ⊓ @LocallyOfFinitePresentation.{u})
      (fun _ hf => ⟨inferInstance, inferInstance⟩) E rfl
  obtain ⟨E', hE', hcomb⟩ := B.fppf_has_representative ⟨X, E⟩ hfppf
  obtain ⟨W, F⟩ := E'
  obtain ⟨hobj, hce⟩ := hcomb
  cases hobj
  dsimp only at hce
  have hpre : F.presieve₀ = E.presieve₀ :=
    (PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hce).symm
  rw [← hpre]
  cases τ with
  | fppf => exact Precoverage.generate_mem_toGrothendieck ⟨F, rfl, hE'⟩
  | zariski =>
      exact Precoverage.generate_mem_toGrothendieck
        ⟨F, rfl, hE', key (@IsOpenImmersion.{u}) (fun _ hf => hf) F hpre⟩
  | etale =>
      exact Precoverage.generate_mem_toGrothendieck
        ⟨F, rfl, hE', key (@Etale.{u}) (fun _ hf => inferInstance) F hpre⟩
  | smooth =>
      exact Precoverage.generate_mem_toGrothendieck
        ⟨F, rfl, hE', key (@Smooth.{u}) (fun _ hf => inferInstance) F hpre⟩
  | syntomic =>
      refine Precoverage.generate_mem_toGrothendieck ⟨F, rfl, hE', ?_⟩
      have h := (Scheme.presieve₀_mem_precoverage_iff (F.map B.inclusion)).1
        (key (@Syntomic.{u}) (fun _ hf => syntomic_of_isOpenImmersion _) F hpre)
      exact ⟨h.2, Set.eq_univ_iff_forall.2 fun x => Set.mem_iUnion.2 (h.1 x)⟩

/-- A covering sieve of the small Zariski site of `S` generates a covering sieve of each of the
five big sites of schemes: it is cut out by the open immersions of its members, and it is jointly
surjective because it is already an fppf covering family. -/
public theorem sieve₀_opensHypercover_mem_baseTopology (τ : SiteKind) {U : S.Opens}
    (R : Sieve U) (hR : R ∈ Opens.grothendieckTopology ↥S U) :
    Sieve.generate (opensHypercover B S hS R).presieve₀ ∈
      B.baseTopology τ (opensObj B S hS U).left := by
  have hfppf : ((opensHypercover B S hS R).map B.inclusion).presieve₀ ∈
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)).coverings
        (B.inclusion.obj (opensObj B S hS U).left) := by
    rw [PreZeroHypercover.presieve₀_map]
    exact isFppfCovering_opensHypercover B S hS R hR
  exact sieve₀_mem_baseTopology_of_isOpenImmersion B τ _
    ((Scheme.presieve₀_mem_precoverage_iff _).1 hfppf).1
    (fun i => inferInstanceAs (IsOpenImmersion (S.homOfLE (leOfHom i.down.2.1))))

/-- The small Zariski site of `S` is cover preserving into each of the five localized
topologies on the big fppf category over `S`. -/
public theorem coverPreserving_baseOpensToBig (τ : SiteKind) :
    CoverPreserving (Opens.grothendieckTopology ↥S) (baseOverTopology B S hS τ)
      (opensToBig B S hS) := by
  refine ⟨fun {U R} hR => ?_⟩
  rw [GrothendieckTopology.mem_over_iff]
  refine (B.baseTopology τ).superset_covering ?_
    (sieve₀_opensHypercover_mem_baseTopology B S hS τ R hR)
  refine (Sieve.generate_le_iff _ _).2 ?_
  rintro Y g ⟨i⟩
  refine (Sieve.overEquiv_iff _ _).2 ?_
  refine ⟨i.down.1, i.down.2.1, Over.homMk (𝟙 _) ?_, i.down.2.2, ?_⟩
  · exact (Category.id_comp _).trans
      (ObjectProperty.hom_ext _ (S.homOfLE_ι (leOfHom i.down.2.1)).symm)
  · exact Over.OverMorphism.ext (Category.id_comp _).symm

/-- The small Zariski site of `S` is continuous into each of the five localized topologies on
the big fppf category over `S`, so it induces a morphism of sites
`(Sch/S)_τ → S_Zar` for every `τ`. -/
public instance isContinuous_baseOpensToBig (τ : SiteKind) :
    (opensToBig B S hS).IsContinuous (Opens.grothendieckTopology ↥S)
      (baseOverTopology B S hS τ) :=
  CategoryTheory.Functor.isContinuous_iff_coverPreserving.2
    (coverPreserving_baseOpensToBig B S hS τ)

/-! ### The morphism of ringed sites and the associated-module functor -/

/-- Abelian presheaves on each of the five big sites over `S` have a sheafification. -/
public instance hasWeakSheafify_baseOverTopology (τ : SiteKind) :
    HasWeakSheafify (baseOverTopology B S hS τ) AddCommGrpCat.{u} :=
  hasWeakSheafify B S hS τ

/-- Weak equivalences of abelian presheaves on each of the five big sites over `S` are the
locally bijective maps. -/
public instance wEqualsLocallyBijective_baseOverTopology (τ : SiteKind) :
    (baseOverTopology B S hS τ).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  wEqualsLocallyBijective B S hS τ

/-- The comparison of structure sheaves along the inclusion of the small Zariski site of `S`
into the indicated big site of schemes over `S`: over an open `U` it is the identification of
the sections of `𝒪_S` over `U` with the global functions of the open subscheme `U`.  Together
with the continuity of the inclusion this is the morphism of ringed sites
`((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪_S)`. -/
public noncomputable def baseStructureMap (τ : SiteKind) :
    S.ringCatSheaf ⟶ ((opensToBig B S hS).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology ↥S) (baseOverTopology B S hS τ)).obj
        (FibredSite.baseRingStructureSheaf B S hS τ) :=
  structureMap B S hS

/-- Over an open `U` of `S`, `baseStructureMap` is the inverse of
`AlgebraicGeometry.Scheme.Opens.topIso U`, as a morphism of rings. -/
@[simp]
public theorem baseStructureMap_hom_app (τ : SiteKind) (U : (S.Opens)ᵒᵖ) :
    (baseStructureMap B S hS τ).hom.app U
      = (CategoryTheory.forget₂ CommRingCat RingCat.{u}).map
          (Scheme.Opens.topIso U.unop).inv := rfl

/-- The pushforward of presheaves of modules along the structure-sheaf comparison of the
indicated big site has a left adjoint. -/
public instance basePresheafPushforward_isRightAdjoint (τ : SiteKind) :
    (PresheafOfModules.pushforward.{u} (baseStructureMap B S hS τ).hom).IsRightAdjoint :=
  Stacks.ModulePullback.isRightAdjoint_pushforward _

/-- The pushforward of sheaves of modules along the morphism of ringed sites of the indicated
big site has a left adjoint. -/
public instance baseSheafPushforward_isRightAdjoint (τ : SiteKind) :
    (SheafOfModules.pushforward.{u} (baseStructureMap B S hS τ)).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction.{u} (baseStructureMap B S hS τ)).isRightAdjoint

/-- The associated-module functor of the indicated big site of `S`: the pullback of sheaves of
modules along the morphism of ringed sites `((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪_S)`. -/
public noncomputable def baseAssociatedModule (τ : SiteKind) :
    S.Modules ⥤ SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ) :=
  SheafOfModules.pullback.{u} (baseStructureMap B S hS τ)

/-- Restriction of a sheaf of modules on the indicated big site of `S` along the inclusion of
the small Zariski site of `S`, the right adjoint of the associated-module functor. -/
public noncomputable def baseRestrictModule (τ : SiteKind) :
    SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ) ⥤ S.Modules :=
  SheafOfModules.pushforward.{u} (baseStructureMap B S hS τ)

/-- The associated-module functor of the indicated big site is left adjoint to restriction
along the inclusion of the small Zariski site. -/
public noncomputable def baseAssociatedModuleAdjunction (τ : SiteKind) :
    baseAssociatedModule B S hS τ ⊣ baseRestrictModule B S hS τ :=
  SheafOfModules.pullbackPushforwardAdjunction.{u} (baseStructureMap B S hS τ)

/-- The associated-module functor of the indicated big site is a left adjoint. -/
public instance isLeftAdjoint_baseAssociatedModule (τ : SiteKind) :
    (baseAssociatedModule B S hS τ).IsLeftAdjoint :=
  (baseAssociatedModuleAdjunction B S hS τ).isLeftAdjoint

/-- **Stacks 03DC, applied.**  The associated-module functor of the indicated big site
preserves all colimits, being a left adjoint. -/
public noncomputable instance preservesColimitsOfSize_baseAssociatedModule.{w, w'}
    (τ : SiteKind) :
    PreservesColimitsOfSize.{w, w'} (baseAssociatedModule B S hS τ) :=
  (baseAssociatedModuleAdjunction B S hS τ).leftAdjoint_preservesColimits

/-- The pullback of the unit object along the morphism of ringed sites of the indicated big
site is an isomorphism, the inclusion of the small Zariski site being final. -/
public instance isIso_basePullbackObjUnitToUnit (τ : SiteKind) :
    IsIso (SheafOfModules.pullbackObjUnitToUnit.{u} (baseStructureMap B S hS τ)) :=
  SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _

/-! ### The morphism of ringed sites `((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪_S)` -/

/-- The ringed topos `((Sch/S)_τ, 𝒪)` of the indicated big site of schemes over `S`: the big
site together with the sheaf of global functions `T/S ↦ Γ(T, 𝒪_T)`. -/
public noncomputable def baseRingedTopos (τ : SiteKind) : RingedTopos.{u, u + 1, u} where
  C := BigFppfOver B S hS
  J := baseOverTopology B S hS τ
  O := FibredSite.baseStructureSheaf B S hS τ

/-- The sheaf of rings of `baseRingedTopos` is `FibredSite.baseStructureSheaf`. -/
@[simp]
public theorem baseRingedTopos_O (τ : SiteKind) :
    (baseRingedTopos B S hS τ).O = FibredSite.baseStructureSheaf B S hS τ := rfl

/-- The comparison of structure sheaves of commutative rings along the inclusion of the small
Zariski site of `S` into the indicated big site of schemes over `S`: over an open `U` it is the
identification of the sections of `𝒪_S` over `U` with the global functions of the open
subscheme `U`. -/
public noncomputable def baseCommStructureMap (τ : SiteKind) :
    S.zariskiRingedTopos.O ⟶
      ((opensToBig B S hS).sheafPushforwardContinuous CommRingCat.{u}
        (Opens.grothendieckTopology ↥S) (baseOverTopology B S hS τ)).obj
          (baseRingedTopos B S hS τ).O where
  hom :=
    { app := fun U => (Scheme.Opens.topIso U.unop).inv
      naturality := fun _ _ h =>
        (Scheme.Opens.topIso_inv_appTop (X := S) (leOfHom h.unop)).symm }

/-- Over an open `U` of `S`, `baseCommStructureMap` is the inverse of
`AlgebraicGeometry.Scheme.Opens.topIso U`. -/
@[simp]
public theorem baseCommStructureMap_hom_app (τ : SiteKind) (U : (S.Opens)ᵒᵖ) :
    (baseCommStructureMap B S hS τ).hom.app U = (Scheme.Opens.topIso U.unop).inv := rfl

/-- The data of the morphism `f : ((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)` of Stacks 070U, for each
`τ ∈ {Zariski, étale, smooth, syntomic, fppf}`, as an `AlgebraicGeometry.RingedToposSiteHom`:
the continuous inclusion of the small Zariski site of `S` into the big site, with structure map
the identification of the sections of `𝒪_S` over an open with the functions on it.

This records only the continuity of the underlying functor, not that it defines a morphism of
sites, so it is not yet a morphism of ringed sites in the sense of Stacks 03AD.  That morphism,
with the same functor and structure map and the exactness of the inverse image added, is
`AlgebraicGeometry.BigFppfOver.baseToZariskiRingedSiteHom`, which carries Stacks 070U. -/
public noncomputable def baseToZariskiRingedToposHom (τ : SiteKind) :
    RingedToposSiteHom (baseRingedTopos B S hS τ) S.zariskiRingedTopos where
  u := opensToBig B S hS
  isContinuous := isContinuous_baseOpensToBig B S hS τ
  fSharp := baseCommStructureMap B S hS τ

/-- The underlying functor of `baseToZariskiRingedToposHom` is `opensToBig`. -/
@[simp]
public theorem baseToZariskiRingedToposHom_u (τ : SiteKind) :
    (baseToZariskiRingedToposHom B S hS τ).u = opensToBig B S hS := rfl

/-- The structure map of `baseToZariskiRingedToposHom` is `baseCommStructureMap`. -/
@[simp]
public theorem baseToZariskiRingedToposHom_fSharp (τ : SiteKind) :
    (baseToZariskiRingedToposHom B S hS τ).fSharp = baseCommStructureMap B S hS τ := rfl

/-- Forgetting commutativity in the structure map of the morphism of ringed sites gives the
comparison `baseStructureMap` over which the associated-module functor is taken, so the
associated-module functor is the pullback of modules along that morphism. -/
public theorem baseStructureMap_hom_eq_whiskerRight (τ : SiteKind) :
    (baseStructureMap B S hS τ).hom =
      Functor.whiskerRight (baseCommStructureMap B S hS τ).hom
        (forget₂ CommRingCat.{u} RingCat.{u}) := rfl

end AlgebraicGeometry.BigFppfOver

end
