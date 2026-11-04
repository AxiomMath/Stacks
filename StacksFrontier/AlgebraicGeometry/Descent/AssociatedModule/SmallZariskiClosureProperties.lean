module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.AssociatedModuleColimits
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.CategoryTheory.Sites.Modules.Tensor
import StacksCore.Tactic.StacksAttribute

/-!
# The identity reading on the small Zariski site: direct sums, colimits, right exactness, tensor
products and extensions

Stacks 06VE states its ten clauses of the two functors
`QCoh(𝒪_S) ⥤ Mod((Sch/S)_τ, 𝒪)` and `QCoh(𝒪_S) ⥤ Mod(S_τ, 𝒪)`, `𝓕 ↦ 𝓕^a`, the second of which
exists for `τ ∈ {Zariski, étale}`.

**Nothing here is registered against Stacks 06VE any more, and that is deliberate.**  Every
statement below is about `AlgebraicGeometry.SmallZariski.associatedModuleQcohOfIdentity`, the
*identity reading* of `𝓕 ↦ 𝓕^a` — the pullback along the **identity** morphism of ringed sites,
which `AlgebraicGeometry.SmallZariski.associatedModuleIsoOfIdentity` identifies with `𝟭`.  As the
module documentation of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiFullyFaithful` records, that
reading presupposes the identification of the two structure sheaves which the source proves
(Tag 020X with Tag 03FG), so the functor-half of each clause becomes a statement about the
identity functor: what survives is the clause's half about the source category `QCoh(𝒪_S)` and
nothing else.  That is the same defect retired for Stacks 0GN7, for clause (1) of 06VE, and for
03DU (4) and 03DX (2) at `τ = Zariski`.

Clauses (2), (3), (4) and (10) at `τ = Zariski` are therefore stated and proved over the functor
of Definition 03DU (4), `AlgebraicGeometry.SmallZariski.associatedModuleQcoh`, in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRealClosureProperties`,
where the `06VE` attributes for them now sit.  Clause (7) at `τ = Zariski` is likewise proved
over that functor, and over the sections-defined one, in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.SmallZariskiAssociatedModuleTensor`
(see "What was not proved here" below).  The statements here are kept because other files
transport iso-invariant properties along them.

The rest of the lemma at the other sites: the big-site half of (2), (3), (4) is
`AlgebraicGeometry.BigFppfOver.preservesColimitsOfShape_discrete_baseAssociatedModuleQcoh` and
its two siblings, of (7) is
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso`, and the small étale half is
`AlgebraicGeometry.SmallEtale.preservesColimitsOfShape_discrete_associatedModuleQcoh`,
`AlgebraicGeometry.SmallEtale.preservesColimitsOfSize_associatedModuleQcoh`,
`AlgebraicGeometry.SmallEtale.preservesFiniteColimits_associatedModuleQcoh` and
`AlgebraicGeometry.SmallEtale.associatedModuleTensorBifunctorIso`.

At `τ = Zariski` the source disposes of the whole lemma in one sentence, used in the proof of
clause (8): the category of `𝒪`-modules on `S_Zar` *is* the category of `𝒪_S`-modules on the
topological space `S`, and `𝓕 ↦ 𝓕^a` is the identity on it.  Read as a *definition* of the
functor that sentence makes each clause below its half about the source category `QCoh(𝒪_S)` and
nothing else — which is why none of them carries a tag:

* clauses (2), (3): colimits of quasi-coherent modules on a scheme are their colimits as
  `𝒪_S`-modules, Schemes, Section 01LA, which is
  `AlgebraicGeometry.BigFppfOver.preservesColimitsOfShape_isQuasicoherent_ι`;
* clause (4): the same for finite colimits, from the weak Serre subcategory of
  `Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerreClass`;
* clause (7): the tensor product of `𝒪`-modules on `S_Zar` *is* the tensor product of
  `𝒪_S`-modules, the same bifunctor on both sides, so nothing is compared;
* clause (10): quasi-coherent `𝒪_S`-modules are closed under extensions, again Schemes,
  Section 01LA, which is
  `Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_X₂_of_shortExact`.

For clause (10) the source's proof is not formal, and under the identity reading none of it is
used: the two steps the source takes — the vanishing `H^1(U, 𝓕₁^a) = 0` on an affine `U` of
Proposition 03DW, and the universal injectivity of `𝓕₁(U) → 𝓔(U)` tested against the
`A`-algebras `A ⊕ M` — are there precisely to compare the restriction `𝓔|_{S_Zar}` with `𝓔`
itself, and under the identity reading that restriction is `𝓔`.  Over the real functor the
comparison is an equivalence by Stacks 03FG, which is a theorem and is what
`AlgebraicGeometry.SmallZariski.essImage_X₂_of_shortExactOfComparison` uses.

## Main results

All six are about the identity reading, and none is a formalization of the clause named beside
it; the tagged statements of (2), (3), (4) and (10) are in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRealClosureProperties`.

* `AlgebraicGeometry.SmallZariski.preservesColimitsOfShape_discrete_associatedModuleQcoh`:
  the identity reading commutes with direct sums (the shape of 06VE (2)).
* `AlgebraicGeometry.SmallZariski.preservesColimitsOfSize_associatedModuleQcoh`: it commutes
  with colimits (the shape of 06VE (3)).
* `AlgebraicGeometry.SmallZariski.preservesFiniteColimits_associatedModuleQcoh`: it is right
  exact (the shape of 06VE (4)).
* `AlgebraicGeometry.SmallZariski.associatedModuleTensorObjIso`: `(𝓕 ⊗_{𝒪_S} 𝓖)^a ≅ 𝓕^a ⊗_𝒪 𝓖^a`
  for the identity reading, where both tensor products are the *same* bifunctor — the shape of
  06VE (7) with nothing compared.
* `AlgebraicGeometry.SmallZariski.essImage_associatedModuleQcoh_iff`: a module on `S_Zar` is in
  the essential image of the identity reading exactly when it is quasi-coherent.
* `AlgebraicGeometry.SmallZariski.essImage_X₂_of_shortExact`: the essential image of the identity
  reading is closed under extensions (the shape of 06VE (10)).

## Implementation notes

The functor is `AlgebraicGeometry.SmallZariski.associatedModuleQcohOfIdentity`.  Clause (1) of
06VE at `τ = Zariski`, and 0GN7, 03DU (4) and 03DX (2) with it, are registered over the real
functor `AlgebraicGeometry.SmallZariski.associatedModuleQcoh` in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRealFullyFaithful`; the two
functors are different and no statement here is about that one.

Right exactness is not deduced from the size-indexed clause (3), for the reason recorded on
`AlgebraicGeometry.BigFppfOver.preservesFiniteColimits_baseAssociatedModuleQcoh`:
`CategoryTheory.Limits.PreservesFiniteColimits` quantifies over finite categories in `Type 0`
while clause (3) is stated at the universe of the scheme, and neither contains the other.

The extension statement is made with the short exact sequence as a
`CategoryTheory.ShortComplex.ShortExact`, and with the two outer terms only *assumed* to be in
the essential image rather than presented as `𝓕₁^a` and `𝓕₂^a` for named `𝓕₁`, `𝓕₂`: that is the
same hypothesis, since the essential image is by definition the objects isomorphic to some
`𝓕^a`, and it is the form the clause is consumed in — Stacks 0GNB (4) and 0GNC (4) know their
outer terms are quasi-coherent, not which quasi-coherent module they come from.

**What was not proved here, and now is elsewhere.**  Clause (7) at `τ = Zariski` over the functor
of Definition 03DU (4) asserts

`(associatedModule B S hS).obj ((tensorSheafBifunctor (Opens.grothendieckTopology ↥S)
  (Osharp := S.sheaf)).obj (F, G)) ≅ (tensorSheafBifunctor (SmallZariski.topology B S hS)
  (Osharp := 𝒪)).obj ((associatedModule B S hS).obj F, (associatedModule B S hS).obj G)`

— the two tensor products being taken over two *different* structure sheaves on two different
sites, where the identity reading has one and the same bifunctor on both sides.  Its proof is
Stacks 03EL, `Stacks.SheafOfModules.pullbackTensorIso`, for the morphism of ringed topoi
attached to Remark 03FH, as at `τ = étale`
(`AlgebraicGeometry.SmallEtale.associatedModuleTensorBifunctorIso`, over
`AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom`).  That is carried out:
`AlgebraicGeometry.SmallZariski.toOpensRingedSiteHom`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallZariskiRingedSiteHomGeneral.lean`)
packages `id_{small, Zar, Zar}` as an `AlgebraicGeometry.RingedSite.HomGeneral`, and
`AlgebraicGeometry.SmallZariski.associatedModuleTensorIsoOfComparison` with its objectwise and
sections-defined companions is the clause.  (The same packaging is what the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiTypesComparison` record as
blocking the local clauses of Stacks 05VG; those are a separate matter and remain open.)

Clause (10) at `τ = étale` and on the big sites is *not* a consequence of this file: there
`𝓕 ↦ 𝓕^a` is not the identity, and the restriction `𝓔 ↦ 𝓔|_{S_Zar}` genuinely has to be compared
with `𝓔`, which is what the source's two steps do.  Clause (8) at `τ = étale` and clause (9) are
likewise not here, and clause (8) at `τ = Zariski` is open over the real functor too —
`AlgebraicGeometry.SmallZariski.associatedModuleSheafHomIso` proves it for the identity reading
only.

The tensor statement is given objectwise only, which is the form the source states.  The
bifunctor form
that `AlgebraicGeometry.SmallEtale.associatedModuleTensorBifunctorIso` carries at `τ = étale` is
not
stated here: assembling it by whiskering needs `𝟭 × 𝟭 ≅ 𝟭` on the product category, whose
naturality square is `Prod.mkHom f.1 f.2 = f` and is not closed by `aesop_cat`.

## References

* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 01LA](https://stacks.math.columbia.edu/tag/01LA)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe uK vK u

namespace AlgebraicGeometry.SmallZariski

variable (S : Scheme.{u})

/-! ### Clauses (2), (3) and (4): direct sums, colimits, right exactness -/

section Shape

variable (K : Type uK) [Category.{vK} K]
  [∀ R : CommRingCat.{u}, HasColimitsOfShape K (ModuleCat.{u} R)]
  [HasColimitsOfShape K (SheafOfModules.{u} S.ringCatSheaf)]

/-- **Stacks 06VE (3) for the small site at `τ = Zariski`**, one shape at a time.  The functor
`QCoh(𝒪_S) ⥤ Mod(S_Zar, 𝒪)`, `𝓕 ↦ 𝓕^a`, commutes with colimits of shape `K`: it is the
inclusion of the quasi-coherent modules, which preserves them, followed by a functor isomorphic
to the identity.

The first factor is site-independent, so it is
`AlgebraicGeometry.BigFppfOver.preservesColimitsOfShape_isQuasicoherent_ι` unchanged — it is the
content of Schemes, Section 01LA that the source cites about `QCoh(𝒪_S)`, the common source of
both functors of 06VE. -/
public theorem preservesColimitsOfShape_associatedModuleQcoh :
    PreservesColimitsOfShape K (associatedModuleQcohOfIdentity S) := by
  have := BigFppfOver.preservesColimitsOfShape_isQuasicoherent_ι S K
  have : PreservesColimitsOfShape K (associatedModuleOfIdentity S) :=
    preservesColimitsOfShape_of_natIso (associatedModuleIsoOfIdentity S).symm
  exact Limits.comp_preservesColimitsOfShape
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι (associatedModuleOfIdentity S)

end Shape

/-- **The identity reading commutes with direct sums**, the shape of Stacks 06VE (2) at
`τ = Zariski`: a direct sum is a colimit over a discrete index category, so this is the discrete
case of the statement above.

**No attribute sits here.**  The clause of 06VE is about the functor of Definition 03DU (4) and
is registered on
`AlgebraicGeometry.SmallZariski.preservesColimitsOfShape_discrete_associatedModuleQcohOfComparison`
in `StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRealClosureProperties`;
see the module documentation. -/
public theorem preservesColimitsOfShape_discrete_associatedModuleQcoh (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (associatedModuleQcohOfIdentity S) :=
  preservesColimitsOfShape_associatedModuleQcoh S (Discrete I)

/-- **The identity reading commutes with all colimits indexed at the size of the scheme**, the
shape of Stacks 06VE (3) at `τ = Zariski`.

**No attribute sits here**, for the reason given on
`AlgebraicGeometry.SmallZariski.preservesColimitsOfShape_discrete_associatedModuleQcoh`; the
clause is registered on
`AlgebraicGeometry.SmallZariski.preservesColimitsOfSize_associatedModuleQcohOfComparison`. -/
public theorem preservesColimitsOfSize_associatedModuleQcoh :
    PreservesColimitsOfSize.{u, u} (associatedModuleQcohOfIdentity S) := by
  constructor
  intro K _
  exact preservesColimitsOfShape_associatedModuleQcoh S K

/-- **The identity reading is right exact**, i.e. commutes with finite colimits — the shape of
Stacks 06VE (4) at `τ = Zariski`.

As on the big site this is not read off the size-indexed statement but assembled from the two
factors, the inclusion of the quasi-coherent modules being right exact because they are a weak
Serre subcategory.

**No attribute sits here**; the clause is registered on
`AlgebraicGeometry.SmallZariski.preservesFiniteColimits_associatedModuleQcohOfComparison`. -/
public theorem preservesFiniteColimits_associatedModuleQcoh :
    PreservesFiniteColimits (associatedModuleQcohOfIdentity S) := by
  have : PreservesFiniteColimits (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι :=
    ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _
  have : PreservesFiniteColimits (associatedModuleOfIdentity S) :=
    preservesFiniteColimits_of_natIso (associatedModuleIsoOfIdentity S).symm
  exact Limits.comp_preservesFiniteColimits
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι (associatedModuleOfIdentity S)

/-! ### Clause (10): an extension of two associated modules is an associated module -/

/-- The essential image of `𝓕 ↦ 𝓕^a` on the small Zariski site is the quasi-coherent
`𝒪_S`-modules: the functor is the inclusion of `QCoh(𝒪_S)` composed with a functor isomorphic to
the identity.

This is Stacks 03DX (2) at `τ = Zariski`, read as a statement about objects. -/
public theorem essImage_associatedModuleQcoh_iff (E : SheafOfModules.{u} S.ringCatSheaf) :
    (associatedModuleQcohOfIdentity S).essImage E ↔ E.IsQuasicoherent := by
  constructor
  · rintro ⟨F, ⟨e⟩⟩
    exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
      (((associatedModuleIsoOfIdentity S).app F.obj).symm ≪≫ e) F.property
  · intro hE
    exact ⟨⟨E, hE⟩, ⟨(associatedModuleIsoOfIdentity S).app E⟩⟩

/-- **The essential image of the identity reading is closed under extensions**, the shape of
Stacks 06VE (10) at `τ = Zariski`: given a short exact sequence `0 → 𝓕₁^a → 𝓔 → 𝓕₂^a → 0` of
`𝒪`-modules, `𝓔` is itself in the essential image.

For the identity reading this is exactly closure of the quasi-coherent `𝒪_S`-modules under
extensions, Schemes, Section 01LA, formalized as
`Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isClosedUnderExtensions`, with
nothing about `𝓕 ↦ 𝓕^a` in it.

**No attribute sits here**; the clause is registered over the real functor on
`AlgebraicGeometry.SmallZariski.essImage_X₂_of_shortExactOfComparison`, where restriction along
the comparison of Remark 03FH has to be shown exact.  The clause at `τ = étale` and on the big
sites is a different statement again and is not implied by either; see the implementation notes
of this module. -/
public theorem essImage_X₂_of_shortExact
    {C : ShortComplex (SheafOfModules.{u} S.ringCatSheaf)} (hC : C.ShortExact)
    (h₁ : (associatedModuleQcohOfIdentity S).essImage C.X₁)
    (h₃ : (associatedModuleQcohOfIdentity S).essImage C.X₃) :
    (associatedModuleQcohOfIdentity S).essImage C.X₂ :=
  (essImage_associatedModuleQcoh_iff S _).2
    (ObjectProperty.prop_X₂_of_shortExact (SheafOfModules.isQuasicoherent S.ringCatSheaf) hC
      ((essImage_associatedModuleQcoh_iff S _).1 h₁)
      ((essImage_associatedModuleQcoh_iff S _).1 h₃))

/-! ### Clause (7): the tensor product -/

/-- The tensor product of `𝒪`-modules on the small Zariski site of `S`, which is the tensor
product of `𝒪_S`-modules on the scheme `S`: the site, the structure sheaf and the construction
are the same on both sides of clause (7) at `τ = Zariski`. -/
public noncomputable abbrev zariskiTensor : S.Modules × S.Modules ⥤ S.Modules :=
  Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S.sheaf)

/-- **The identity reading carries a tensor product to a tensor product**, the shape of
Stacks 06VE (7) at `τ = Zariski`:

`(𝓕 ⊗_{𝒪_S} 𝓖)^a ≅ 𝓕^a ⊗_𝒪 𝓖^a`.

**No attribute sits here, and clause (7) at `τ = Zariski` is open.**  For the identity reading
`𝓕 ↦ 𝓕^a` is the identity functor and the two tensor products are literally the same bifunctor
over the same structure sheaf on the same site, so the isomorphism below is
`AlgebraicGeometry.SmallZariski.associatedModuleIsoOfIdentity` conjugated in all three places and
nothing is compared.  Over the functor of Definition 03DU (4) the two sides are tensor products
over two different structure sheaves on two different sites, and the statement is Stacks 03EL for
the morphism of ringed topoi of Remark 03FH; the module documentation gives the missing statement
and what blocks it.  At `τ = étale`
(`AlgebraicGeometry.SmallEtale.associatedModuleTensorBifunctorIso`) and on the big sites
(`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso`) the clause *is* proved over the
real functor, with no quasi-coherence needed, which is why this is stated for all
`𝒪_S`-modules. -/
public noncomputable def associatedModuleTensorObjIso (F G : S.Modules) :
    (associatedModuleOfIdentity S).obj ((zariskiTensor S).obj (F, G)) ≅
      (zariskiTensor S).obj
        ((associatedModuleOfIdentity S).obj F, (associatedModuleOfIdentity S).obj G) :=
  (associatedModuleIsoOfIdentity S).app _ ≪≫
    (zariskiTensor S).mapIso
      (Iso.prod ((associatedModuleIsoOfIdentity S).app F).symm
        ((associatedModuleIsoOfIdentity S).app G).symm)

end AlgebraicGeometry.SmallZariski

end
