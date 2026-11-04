module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentOfFinitePresentationUnit
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineSiteQuasiCoherentObjects
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFinitenessAgreement
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiLocalTypesComparison
public import StacksFrontier.AlgebraicGeometry.Etale.SupportSections
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallSiteAffineBasis
import StacksCore.Tactic.StacksAttribute

/-!
# Coherence under `𝓕 ↦ 𝓕^a` on the small Zariski and small étale sites

Descent, Lemma 05VG compares the properties of Modules on Sites, Definitions 03DE, 03DL and 03ER
across the comparison functors `𝓕 ↦ 𝓕^a` of Descent, Proposition 03DX.  It excludes coherence
from the general assertion, and then asserts it in one restricted case: **for the small site of a
locally Noetherian scheme `S` and `τ ∈ {Zariski, étale}`, a quasi-coherent `𝒪_S`-module `𝓕` is
coherent if and only if `𝓕^a` is coherent on the small site.**  This file proves that clause, at
both of its two topologies.

## The route

The source reduces the clause to Stacks 01XZ, and so does this file.  Over a locally Noetherian
scheme the five conditions of 01XZ are equivalent
(`Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae`), so on the scheme side coherence is
interchangeable with finite presentation and, for a quasi-coherent module, with finite type.
Both of those *are* clauses of 05VG already proved at both small sites, and each direction uses
one of them:

* `𝓕` coherent gives `𝓕` of finite presentation, hence `𝓕^a` of finite presentation by
  clause 03DL (7) — `AlgebraicGeometry.SmallEtale.isFinitePresentation_associatedModule_iff` and
  `AlgebraicGeometry.SmallZariski.isFinitePresentation_iff_associatedModule`.  A sheaf of modules
  of finite presentation on a ringed site whose structure sheaf is coherent is coherent, which is
  `Stacks.SheafOfModules.isCoherentOnSite_of_isFinitePresentation_of_unit`; the structure sheaf of
  either small site of a locally Noetherian scheme is coherent, which is
  `AlgebraicGeometry.SmallEtale.isCoherentOnSite_unit` and
  `AlgebraicGeometry.SmallZariski.isCoherentOnSite_unit` below.
* `𝓕^a` coherent gives `𝓕^a` of finite type, hence `𝓕` of finite type by clause 03DL (5) —
  `AlgebraicGeometry.SmallEtale.isFiniteType_associatedModule_iff` and
  `AlgebraicGeometry.SmallZariski.isFiniteType_iff_associatedModule` — and a quasi-coherent module
  of finite type on a locally Noetherian scheme is coherent, which is 01XZ (2) ⟹ (1).

## Main results

* `AlgebraicGeometry.SmallEtale.isCoherentOnSite_unit` and
  `AlgebraicGeometry.SmallZariski.isCoherentOnSite_unit`: **the structure sheaf of the small
  étale, respectively small Zariski, site of a locally Noetherian scheme is coherent.**
* `AlgebraicGeometry.SmallEtale.isCoherentOnSite_associatedModule_iff` and
  `AlgebraicGeometry.SmallZariski.isCoherentOnSite_associatedModule_iff`: **Descent, Lemma 05VG
  for coherence, at the small site, for `τ = étale` and `τ = Zariski`.**

## Implementation notes

Coherence of the structure sheaf is `AlgebraicGeometry.RingedSite.isFiniteType_relations_unit`,
the general statement that the relations among a finite family of sections of the structure sheaf
of a ringed site are of finite type on the slice site as soon as every object is covered by
objects with Noetherian ring of sections and mutually flat restriction maps.  Its three inputs at
either small site of a scheme are supplied here: the affine objects generate a covering sieve
(`AlgebraicGeometry.SmallEtale.sieve_generate_isAffine_mem_topology` and its Zariski sibling, in
`StacksFrontier.AlgebraicGeometry.Topologies.SmallSiteAffineBasis`), read into the factorization
shape the general statement asks for by
`CategoryTheory.GrothendieckTopology.exists_covering_factorThrough_of_generate`; an affine object
is étale, respectively an open immersion, over `S` and therefore locally Noetherian, so its ring
of global sections is Noetherian; and a morphism between affine objects is flat, so its map on
rings of global sections is flat.  The finite-type clause of coherence needs no hypothesis and is
`PresheafOfModules.isFiniteType_unit`.

Each equivalence carries exactly the source's hypotheses and no others: `S` locally Noetherian
and `𝓕` quasi-coherent.  The quasi-coherence is used twice — once as the hypothesis of
clause 03DL (7) at the small site, and once in 01XZ (2) ⟹ (1).

## References

* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

/-- The covering sieve generated by the arrows out of the objects with a property `Good` is a
covering sieve all of whose arrows factor through a `Good` object.  This is the shape in which
`AlgebraicGeometry.RingedSite.isFiniteType_relations_unit` asks for its covering. -/
public theorem CategoryTheory.GrothendieckTopology.exists_covering_factorThrough_of_generate
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (Good : C → Prop)
    (h : ∀ W : C, Sieve.generate (fun {V : C} (_ : V ⟶ W) ↦ Good V) ∈ J W) (W : C) :
    ∃ Sv : Sieve W, Sv ∈ J W ∧
      ∀ ⦃Y : C⦄ (f : Y ⟶ W), Sv f →
        ∃ (A : C) (l : Y ⟶ A) (m : A ⟶ W), Good A ∧ f = l ≫ m := by
  refine ⟨_, h W, ?_⟩
  rintro Y f ⟨Z, g, m, hm, hcomp⟩
  exact ⟨Z, g, m, hm, hcomp.symm⟩

namespace AlgebraicGeometry

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Coherence of the structure sheaf of the small étale site -/

/-- Over a locally Noetherian scheme the ring of sections of the structure sheaf of the small
étale site at an affine object is Noetherian: the object is étale over `S`, hence locally of
finite type over it, hence locally Noetherian, and being affine it is its own only component. -/
public theorem isNoetherianRing_ringSheaf_obj [IsLocallyNoetherian S] (A : SmallEtale B S hS)
    (hA : _root_.AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B S hS).obj A)) :
    IsNoetherianRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).obj.obj
        (op A)) := by
  have : IsLocallyNoetherian ((SmallEtale.toScheme B S hS).obj A) :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := S) (B.inclusion.map A.obj.hom)
  exact IsLocallyNoetherian.component_noetherian
    ⟨⊤, isAffineOpen_top ((SmallEtale.toScheme B S hS).obj A)⟩

/-- Restriction of sections of the structure sheaf of the small étale site between affine objects
is a flat ring homomorphism: the morphism of schemes is étale, hence flat, and flatness of a
morphism of affine schemes is flatness of the induced map on rings of global sections. -/
public theorem flat_ringSheaf_obj_map {A A' : SmallEtale B S hS} (h : A' ⟶ A)
    (hA : _root_.AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B S hS).obj A))
    (hA' : _root_.AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B S hS).obj A')) :
    RingHom.Flat ((smallEtaleRingedSite B S hS).O.obj.map h.op).hom := by
  have : Etale ((SmallEtale.toScheme B S hS).map h) := etale_toScheme_map h
  exact Scheme.Hom.flat_appTop ((SmallEtale.toScheme B S hS).map h)

/-- **The structure sheaf of the small étale site of a locally Noetherian scheme is coherent.**

The finite-type clause is `PresheafOfModules.isFiniteType_unit` and needs no hypothesis.  The
relations clause is `AlgebraicGeometry.RingedSite.isFiniteType_relations_unit` at the covering by
the affine objects of the site, whose rings of sections are Noetherian and whose restriction maps
are flat. -/
public theorem isCoherentOnSite_unit [IsLocallyNoetherian S] :
    SheafOfModules.IsCoherentOnSite
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS).O)) where
  isFiniteType := PresheafOfModules.isFiniteType_unit _
  kernel_isFiniteType U n s :=
    RingedSite.isFiniteType_relations_unit (smallEtaleRingedSite B S hS)
      (fun A ↦ _root_.AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B S hS).obj A))
      (GrothendieckTopology.exists_covering_factorThrough_of_generate _ _
        (sieve_generate_isAffine_mem_topology B S hS))
      (fun A hA ↦ isNoetherianRing_ringSheaf_obj B S hS A hA)
      (fun h hA hA' ↦ flat_ringSheaf_obj_map B S hS h hA hA') U n s

/-! ### The clause of Descent, Lemma 05VG for coherence at `τ = étale` -/

/-- **Descent, Lemma 05VG for coherence, at the small site for `τ = étale`.**  For a locally
Noetherian scheme `S`, a quasi-coherent `𝒪_S`-module `𝓕` is coherent if and only if `𝓕ᵃ` is
coherent as an `𝒪`-module on `S_étale`.

Coherence on `S_étale` is Modules on Sites, Definition 03DL (8), and coherence of `𝓕` is the
ringed-space predicate of Stacks 01BV at the Zariski site of `S`.  The source excludes coherence
from the general assertion of 05VG and asserts exactly this restricted case, with the two
hypotheses carried here: `S` locally Noetherian and `𝓕` quasi-coherent.

Both directions run through Stacks 01XZ on the scheme, as the source does.  Forward: `𝓕` is of
finite presentation, so `𝓕ᵃ` is of finite presentation by clause 03DL (7) of 05VG
(`AlgebraicGeometry.SmallEtale.isFinitePresentation_associatedModule_iff`), and a module of
finite presentation on a ringed site with coherent structure sheaf is coherent
(`Stacks.SheafOfModules.isCoherentOnSite_of_isFinitePresentation_of_unit`, applied to
`AlgebraicGeometry.SmallEtale.isCoherentOnSite_unit`).  Backward: coherence on the site contains
finite type, so `𝓕` is of finite type by clause 03DL (5) of 05VG
(`AlgebraicGeometry.SmallEtale.isFiniteType_associatedModule_iff`), and a quasi-coherent module of
finite type over a locally Noetherian scheme is coherent.

The clause string records the scope: this is the coherence clause of 05VG at the **small** site
for `τ = étale`.  The small Zariski site is
`AlgebraicGeometry.SmallZariski.isCoherentOnSite_associatedModule_iff`. -/
@[stacks 05VG "coherent (03DL (8)), small site at τ = étale over a locally Noetherian base, at \
the comparison functor of 03DX itself"]
public theorem isCoherentOnSite_associatedModule_iff [IsLocallyNoetherian S] (𝓕 : S.Modules)
    [𝓕.IsQuasicoherent] :
    𝓕.IsCoherent ↔
      SheafOfModules.IsCoherentOnSite ((associatedModule B S hS).obj 𝓕) := by
  constructor
  · intro hc
    have : SheafOfModules.IsFinitePresentation
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O))
          ((associatedModule B S hS).obj 𝓕) :=
      (isFinitePresentation_associatedModule_iff B S hS 𝓕 inferInstance).mp
        (Stacks.AlgebraicGeometry.CoherentTFAE.isFinitePresentation_of_isCoherent' 𝓕)
    exact Stacks.SheafOfModules.isCoherentOnSite_of_isFinitePresentation_of_unit
      (smallEtaleRingedSite B S hS) ((associatedModule B S hS).obj 𝓕)
      (isCoherentOnSite_unit B S hS)
  · intro hm
    have : SheafOfModules.IsFiniteType 𝓕 :=
      (isFiniteType_associatedModule_iff B S hS 𝓕).mpr
        (SheafOfModules.isFiniteType_of_presheaf_isFiniteType _ hm.isFiniteType)
    exact Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType
      𝓕

end SmallEtale

namespace SmallZariski

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Coherence of the structure sheaf of the small Zariski site -/

/-- Over a locally Noetherian scheme the ring of sections of the structure sheaf of the small
Zariski site at an affine object is Noetherian: the object is an open immersion into `S`, hence
locally Noetherian, and being affine it is its own only component. -/
public theorem isNoetherianRing_ringSheaf_obj [IsLocallyNoetherian S] (A : SmallZariski B S hS)
    (hA : _root_.AlgebraicGeometry.IsAffine ((SmallZariski.toScheme B S hS).obj A)) :
    IsNoetherianRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallZariskiRingedSite B S hS).O).obj.obj
        (op A)) := by
  have : IsLocallyNoetherian ((SmallZariski.toScheme B S hS).obj A) :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := S) (B.inclusion.map A.obj.hom)
  exact IsLocallyNoetherian.component_noetherian
    ⟨⊤, isAffineOpen_top ((SmallZariski.toScheme B S hS).obj A)⟩

/-- Restriction of sections of the structure sheaf of the small Zariski site between affine
objects is a flat ring homomorphism: the morphism of schemes is an open immersion, hence flat,
and flatness of a morphism of affine schemes is flatness of the induced map on rings of global
sections. -/
public theorem flat_ringSheaf_obj_map {A A' : SmallZariski B S hS} (h : A' ⟶ A)
    (hA : _root_.AlgebraicGeometry.IsAffine ((SmallZariski.toScheme B S hS).obj A))
    (hA' : _root_.AlgebraicGeometry.IsAffine ((SmallZariski.toScheme B S hS).obj A')) :
    RingHom.Flat ((smallZariskiRingedSite B S hS).O.obj.map h.op).hom := by
  have : IsOpenImmersion ((SmallZariski.toScheme B S hS).map h) :=
    isOpenImmersion_smallZariski_toScheme_map B S hS h
  exact Scheme.Hom.flat_appTop ((SmallZariski.toScheme B S hS).map h)

/-- **The structure sheaf of the small Zariski site of a locally Noetherian scheme is
coherent.**  The two clauses are `PresheafOfModules.isFiniteType_unit` and
`AlgebraicGeometry.RingedSite.isFiniteType_relations_unit` at the covering by the affine objects
of the site. -/
public theorem isCoherentOnSite_unit [IsLocallyNoetherian S] :
    SheafOfModules.IsCoherentOnSite
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallZariskiRingedSite B S hS).O)) where
  isFiniteType := PresheafOfModules.isFiniteType_unit _
  kernel_isFiniteType U n s :=
    RingedSite.isFiniteType_relations_unit (smallZariskiRingedSite B S hS)
      (fun A ↦ _root_.AlgebraicGeometry.IsAffine ((SmallZariski.toScheme B S hS).obj A))
      (GrothendieckTopology.exists_covering_factorThrough_of_generate _ _
        (sieve_generate_isAffine_mem_topology B S hS))
      (fun A hA ↦ isNoetherianRing_ringSheaf_obj B S hS A hA)
      (fun h hA hA' ↦ flat_ringSheaf_obj_map B S hS h hA hA') U n s

/-! ### The clause of Descent, Lemma 05VG for coherence at `τ = Zariski` -/

/-- **Descent, Lemma 05VG for coherence, at the small site for `τ = Zariski`.**  For a locally
Noetherian scheme `S`, a quasi-coherent `𝒪_S`-module `𝓕` is coherent if and only if `𝓕ᵃ` is
coherent as an `𝒪`-module on `S_Zar`.

This is the `τ = Zariski` half of the one case in which 05VG asserts coherence, under the two
hypotheses the source carries: `S` locally Noetherian and `𝓕` quasi-coherent.  The route is the
same as at `τ = étale`, with clause 03DL (7) read off
`AlgebraicGeometry.SmallZariski.isFinitePresentation_iff_associatedModule` and clause 03DL (5)
off `AlgebraicGeometry.SmallZariski.isFiniteType_iff_associatedModule`.

The clause string records the scope: this is the coherence clause of 05VG at the **small** site
for `τ = Zariski`.  The small étale site is
`AlgebraicGeometry.SmallEtale.isCoherentOnSite_associatedModule_iff`. -/
@[stacks 05VG "coherent (03DL (8)), small site at τ = Zariski over a locally Noetherian base, at \
the comparison functor of 03DX itself"]
public theorem isCoherentOnSite_associatedModule_iff [IsLocallyNoetherian S] (𝓕 : S.Modules)
    [𝓕.IsQuasicoherent] :
    𝓕.IsCoherent ↔
      SheafOfModules.IsCoherentOnSite ((associatedModule B S hS).obj 𝓕) := by
  constructor
  · intro hc
    have : SheafOfModules.IsFinitePresentation
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallZariskiRingedSite B S hS).O))
          ((associatedModule B S hS).obj 𝓕) :=
      (isFinitePresentation_iff_associatedModule B S hS 𝓕).mp
        (Stacks.AlgebraicGeometry.CoherentTFAE.isFinitePresentation_of_isCoherent' 𝓕)
    exact Stacks.SheafOfModules.isCoherentOnSite_of_isFinitePresentation_of_unit
      (smallZariskiRingedSite B S hS) ((associatedModule B S hS).obj 𝓕)
      (isCoherentOnSite_unit B S hS)
  · intro hm
    have : SheafOfModules.IsFiniteType 𝓕 :=
      (isFiniteType_iff_associatedModule B S hS 𝓕).mpr
        (SheafOfModules.isFiniteType_of_presheaf_isFiniteType _ hm.isFiniteType)
    exact Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType
      𝓕

end SmallZariski

end AlgebraicGeometry

end
