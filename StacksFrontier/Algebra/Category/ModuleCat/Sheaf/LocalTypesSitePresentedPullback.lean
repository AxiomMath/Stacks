module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalizedPullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesIsoInvariance
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackTopos
import StacksCore.Tactic.StacksAttribute

/-!
# Local types of modules under the pullback along a site-presented morphism of ringed topoi

Let `(h, h♯) : (Sh(C'), O_{C'}) ⟶ (Sh(D'), O_{D'})` be a morphism of ringed topoi whose
underlying morphism of topoi is the one Stacks 00XC attaches to a morphism of sites
`u : D' ⥤ C'`.  The four clauses 03DL (1), (2), (3) and (6) are stable under its pullback of
sheaves of modules, by the case of Stacks 03DO that Section 03DG proves for a morphism of
ringed *sites*.

The passage from the one presentation to the other is what this file supplies.  A
`AlgebraicGeometry.RingedToposHom` records the structure map as a morphism
`O_{D'} ⟶ (pushforwardCommRingFunctor h).obj O_{C'}` into the direct image of a sheaf of
commutative rings along a morphism of *topoi*, that is, into the direct image of the underlying
sheaf of sets with the ring operations carried along; a
`AlgebraicGeometry.RingedToposSiteHom`, which is the shape
`AlgebraicGeometry.RingedSite.Hom.ofRingedToposSiteHom` consumes, records it as a morphism into
`(u.sheafPushforwardContinuous CommRingCat _ _).obj O_{C'}`, the restriction of the sheaf of
commutative rings along `u`.  The two agree, by
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`, and composing with that identification is
the whole of the passage.

## Main definitions

* `AlgebraicGeometry.RingedToposSiteHom.ofMorphismOfSites`: **a morphism of ringed topoi whose
  underlying morphism of topoi comes from a morphism of sites, read as a
  `AlgebraicGeometry.RingedToposSiteHom`.**
* `AlgebraicGeometry.RingedToposHom.pullbackModulesIsoPullbackTopos`: its pullback of sheaves of
  modules is the site-presented pullback.

## Main results

* `AlgebraicGeometry.RingedToposHom.isLocallyFreeOnSite_pullbackModules_of_isMorphismOfSites`,
  `.isFiniteLocallyFreeOnSite_pullbackModules_of_isMorphismOfSites`,
  `.isLocallyGeneratedBySectionsOnSite_pullbackModules_of_isMorphismOfSites` and
  `.isQuasicoherentOnSite_pullbackModules_of_isMorphismOfSites`: the clauses 03DL (1), (2), (3)
  and (6) are carried by the pullback of modules along a morphism of ringed topoi presented by a
  left exact morphism of sites.

## Implementation notes

The underlying morphism of topoi is not asked to *be* `hu.morphismOfTopoi` as a field; it is
asked to be equal to it, which is the form Stacks 03CR produces.  Each statement below discharges
that equality by destructuring the morphism and substituting, after which the structure map is
the only remaining datum and the comparison above applies to it directly.

## References

* [Stacks Project, Tag 00XC](https://stacks.math.columbia.edu/tag/00XC)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03DG](https://stacks.math.columbia.edu/tag/03DG)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry

universe v

variable {X Y : RingedTopos.{v, v, v}} {u : Y.C ⥤ X.C}

/-- **A morphism of ringed topoi presented by a morphism of sites, read as a
`AlgebraicGeometry.RingedToposSiteHom`.**  The underlying functor is the one the morphism of
sites is given by, and the structure map is the given one followed by the identification
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso` of the direct image of a sheaf of
commutative rings along the induced morphism of topoi with its restriction along the functor.

This is the passage inverse to `AlgebraicGeometry.RingedSite.Hom.ofRingedToposSiteHom`; the
identification it composes with is the identity on underlying sheaves of sets. -/
noncomputable def RingedToposSiteHom.ofMorphismOfSites (hu : u.IsMorphismOfSites Y.J X.J)
    (φ : Y.O ⟶ (pushforwardCommRingFunctor hu.morphismOfTopoi).obj X.O) :
    RingedToposSiteHom X Y :=
  haveI := hu.isContinuous
  { u := u
    fSharp := φ ≫ (restrictionCommRingIso Y.J X.J u X.O).hom }

/-- **The morphism of ringed topoi presented by a morphism of sites**, with a prescribed
structure map: the morphism of topoi of Stacks 00XC together with that map. -/
noncomputable abbrev RingedToposHom.ofMorphismOfSites (hu : u.IsMorphismOfSites Y.J X.J)
    (φ : Y.O ⟶ (pushforwardCommRingFunctor hu.morphismOfTopoi).obj X.O) :
    RingedToposHom X Y where
  toToposHom := hu.morphismOfTopoi
  fSharp := φ

/-- **The two passages are inverse to one another.**  Reading a site-presented morphism of ringed
topoi as a `AlgebraicGeometry.RingedToposSiteHom`, then as a morphism of ringed sites, and then
back as a morphism of ringed topoi, returns it: the two structure maps differ by the comparison
of the two direct images and by its inverse. -/
theorem RingedToposSiteHom.ringedToposHom_ofMorphismOfSites (hu : u.IsMorphismOfSites Y.J X.J)
    (φ : Y.O ⟶ (pushforwardCommRingFunctor hu.morphismOfTopoi).obj X.O) :
    (RingedSite.Hom.ofRingedToposSiteHom (RingedToposSiteHom.ofMorphismOfSites hu φ)
        hu).ringedToposHom =
      RingedToposHom.ofMorphismOfSites hu φ := by
  simp only [RingedSite.Hom.ringedToposHom, RingedToposSiteHom.ofMorphismOfSites,
    RingedSite.Hom.ofRingedToposSiteHom]
  rfl

namespace RingedToposHom

variable [HasWeakSheafify X.J AddCommGrpCat.{v}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- **The pullback of sheaves of modules along a site-presented morphism of ringed topoi is the
site-presented pullback.**  Both are left adjoints of the direct image, and the two presentations
of the morphism are identified by
`AlgebraicGeometry.RingedToposSiteHom.ringedToposHom_ofMorphismOfSites`. -/
noncomputable def pullbackModulesIsoPullbackTopos (hu : u.IsMorphismOfSites Y.J X.J)
    (φ : Y.O ⟶ (pushforwardCommRingFunctor hu.morphismOfTopoi).obj X.O) :
    (ofMorphismOfSites hu φ).toModulesHom.pullbackModules ≅
      (RingedToposSiteHom.ofMorphismOfSites hu φ).pullbackTopos :=
  pullbackModulesViaComparisonIso (ofMorphismOfSites hu φ) ≪≫
    eqToIso (by rw [RingedToposSiteHom.ringedToposHom_ofMorphismOfSites]) ≪≫
    RingedSite.Hom.pullbackModulesToposIso
      (RingedSite.Hom.ofRingedToposSiteHom (RingedToposSiteHom.ofMorphismOfSites hu φ) hu)

/-- A property of sheaves of modules passes along the pullback of a site-presented morphism of
ringed topoi once it passes along the pullback of the morphism of ringed sites it presents. -/
private theorem pullbackModules_obj_of_isMorphismOfSites [PreservesFiniteLimits u]
    {f : RingedToposHom X Y}
    (hu : u.IsMorphismOfSites Y.J X.J) (hf : f.toToposHom = hu.morphismOfTopoi)
    {F : SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    {P : SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) → Prop}
    {Q : SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) → Prop}
    (hQ : ∀ {M N}, (M ≅ N) → Q M → Q N)
    (h : ∀ fSharp, PreservesFiniteLimits (RingedSite.Hom.ofRingedToposSiteHom
      (RingedToposSiteHom.ofMorphismOfSites hu fSharp) hu).u → P F →
        Q ((RingedToposSiteHom.ofMorphismOfSites hu fSharp).pullbackTopos.obj F))
    (hF : P F) : Q (f.toModulesHom.pullbackModules.obj F) := by
  obtain ⟨fTop, fSharp⟩ := f
  subst hf
  exact hQ ((pullbackModulesIsoPullbackTopos hu fSharp).app F).symm
    (h fSharp (inferInstanceAs (PreservesFiniteLimits u)) hF)

section Clauses

variable [HasFiniteLimits Y.C] [PreservesFiniteLimits u]
  [∀ V : X.C, HasWeakSheafify (X.J.over V) AddCommGrpCat.{v}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{v}]
  [∀ V : Y.C, HasWeakSheafify (Y.J.over V) AddCommGrpCat.{v}]
  [∀ V : Y.C, (Y.J.over V).WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- **Local freeness is carried by the pullback along a morphism of ringed topoi presented by a
left exact morphism of sites.**  This is the clause 03DL (1) of Stacks 03DO in the case
Section 03DG proves it, transported from the morphism of ringed *sites* to the morphism of ringed
topoi it presents. -/
theorem isLocallyFreeOnSite_pullbackModules_of_isMorphismOfSites (f : RingedToposHom X Y)
    (hu : u.IsMorphismOfSites Y.J X.J) (hf : f.toToposHom = hu.morphismOfTopoi)
    (F : SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hF : F.IsLocallyFreeOnSite) :
    (f.toModulesHom.pullbackModules.obj F).IsLocallyFreeOnSite := by
  exact pullbackModules_obj_of_isMorphismOfSites hu hf
    Stacks.SheafOfModules.Intrinsic.isLocallyFreeOnSite_of_iso
    (fun fSharp _ => Stacks.Sheaves.LocalizedPullback.isLocallyFreeOnSite_pullbackTopos
      (RingedSite.Hom.ofRingedToposSiteHom
        (RingedToposSiteHom.ofMorphismOfSites hu fSharp) hu)) hF

/-- **Finite local freeness is carried by the pullback along a morphism of ringed topoi presented
by a left exact morphism of sites.**  This is the clause 03DL (2) of Stacks 03DO in the case
Section 03DG proves it; the rank on each member of the covering is unchanged. -/
theorem isFiniteLocallyFreeOnSite_pullbackModules_of_isMorphismOfSites (f : RingedToposHom X Y)
    (hu : u.IsMorphismOfSites Y.J X.J) (hf : f.toToposHom = hu.morphismOfTopoi)
    (F : SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hF : F.IsFiniteLocallyFreeOnSite) :
    (f.toModulesHom.pullbackModules.obj F).IsFiniteLocallyFreeOnSite := by
  exact pullbackModules_obj_of_isMorphismOfSites hu hf
    Stacks.SheafOfModules.Intrinsic.isFiniteLocallyFreeOnSite_of_iso
    (fun fSharp _ => Stacks.Sheaves.LocalizedPullback.isFiniteLocallyFreeOnSite_pullbackTopos
      (RingedSite.Hom.ofRingedToposSiteHom
        (RingedToposSiteHom.ofMorphismOfSites hu fSharp) hu)) hF

/-- **Local generation by sections is carried by the pullback along a morphism of ringed topoi
presented by a left exact morphism of sites.**  This is the clause 03DL (3) of Stacks 03DO in the
case Section 03DG proves it; the index type of the generating family is unchanged. -/
theorem isLocallyGeneratedBySectionsOnSite_pullbackModules_of_isMorphismOfSites
    (f : RingedToposHom X Y)
    (hu : u.IsMorphismOfSites Y.J X.J) (hf : f.toToposHom = hu.morphismOfTopoi)
    (F : SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hF : F.IsLocallyGeneratedBySectionsOnSite) :
    (f.toModulesHom.pullbackModules.obj F).IsLocallyGeneratedBySectionsOnSite := by
  exact pullbackModules_obj_of_isMorphismOfSites hu hf
    Stacks.SheafOfModules.Intrinsic.isLocallyGeneratedBySectionsOnSite_of_iso
    (fun fSharp _ =>
      Stacks.Sheaves.LocalizedPullback.isLocallyGeneratedBySectionsOnSite_pullbackTopos
      (RingedSite.Hom.ofRingedToposSiteHom
        (RingedToposSiteHom.ofMorphismOfSites hu fSharp) hu)) hF

/-- **Quasi-coherence is carried by the pullback along a morphism of ringed topoi presented by a
left exact morphism of sites.**  This is the clause 03DL (6) of Stacks 03DO in the case
Section 03DG proves it. -/
theorem isQuasicoherentOnSite_pullbackModules_of_isMorphismOfSites (f : RingedToposHom X Y)
    (hu : u.IsMorphismOfSites Y.J X.J) (hf : f.toToposHom = hu.morphismOfTopoi)
    (F : SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hF : F.IsQuasicoherentOnSite) :
    (f.toModulesHom.pullbackModules.obj F).IsQuasicoherentOnSite := by
  exact pullbackModules_obj_of_isMorphismOfSites hu hf SheafOfModules.IsQuasicoherentOnSite.of_iso
    (fun fSharp _ => Stacks.Sheaves.LocalizedPullback.isQuasicoherentOnSite_pullbackTopos
      (RingedSite.Hom.ofRingedToposSiteHom
        (RingedToposSiteHom.ofMorphismOfSites hu fSharp) hu)) hF

end Clauses

end RingedToposHom

end AlgebraicGeometry

end
