module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.NoetherianCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePseudoCoherentDerivedHom
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.RingTheory.Ext.DerivedFiniteness
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedBoundedBelow
import StacksCore.Tactic.StacksAttribute

/-!
# Coherence of the derived internal Hom of two associated complexes on an affine scheme

Let `R` be a Noetherian ring and `X = Spec R`. This file proves the coherence clause of
[Stacks, Tag 0D0C] on `X`, for the two arguments presented as derived sheafifications: if `K` is
an object of `D⁻_Coh(R)` and `L` an object of `D⁺_Coh(R)`, then every cohomology sheaf of

`R𝓗om_{𝒪_X}(K̃, L̃)`

is a coherent `𝒪_X`-module, so that `R𝓗om_{𝒪_X}(K̃, L̃)` lies in `D⁺_Coh(𝒪_X)`.

## Main results

* `AlgebraicGeometry.isCoherent_homology_affineDerivedSheafHom` — every cohomology sheaf of
  `R𝓗om_{𝒪_X}(K̃, L̃)` is coherent.
* `AlgebraicGeometry.derivedCategoryBPlus_coherent_affineDerivedSheafHom` — the packaged form,
  membership in `D⁺_Coh(𝒪_X)`, stated with the two hypotheses as membership in `D⁻_Coh(R)` and
  `D⁺_Coh(R)`.

## The proof

Three inputs combine, and none of them is assumed.

Over a Noetherian ring an object of `D(R)` is pseudo-coherent exactly when it is bounded above
with finite cohomology modules ([Stacks, Tag 066E]), so `K` is pseudo-coherent. Part (3)(a) of
[Stacks, Tag 0A6H] — `AlgebraicGeometry.affinePseudoCoherentDerivedSheafHomIso` — then identifies
`R𝓗om_{𝒪_X}(K̃, L̃)` with the derived sheafification of `RHom_R(K, L)`.

The cohomology modules of `RHom_R(K, L)` are finite: this is the commutative algebra behind the
tag, `StacksDraft.DerivedHom.finite_homology_derivedHom`, obtained there from finiteness of
`Ext^i_R(K, L)` by dévissage along the canonical truncation triangles.

Finally sheafification is exact, so the degree-`n` cohomology sheaf of the sheafification of a
complex is the sheaf associated with its degree-`n` cohomology module, and the sheaf associated
with a finite module over a Noetherian ring is coherent ([Stacks, Tag 01XZ]).

Boundedness below is not reproved here: it is
`Stacks.SheafOfModules.isBoundedBelow_derivedSheafHom`, the clause of [Stacks, Tag 0D0C] the
library already carries, applied to the two sheafifications once their cohomological bounds have
been read off from those of `K` and `L`.

## What this file states, and what the general case is

The tag speaks about an arbitrary locally Noetherian scheme `X` and arbitrary objects of
`D⁻_Coh(𝒪_X)` and `D⁺_Coh(𝒪_X)`; the statements below are the affine case, with both arguments
presented as derived sheafifications. The general case is **not** missing from the library: it is
`AlgebraicGeometry.derivedCategoryBPlus_isCoherent_derivedSheafHom` of
`StacksFrontier/AlgebraicGeometry/Duality/DerivedTilde/SchemeCoherentDerivedHom.lean`, which carries
the unqualified `@[stacks 0D0C]` and is deduced from the statements here.

Two steps of the reduction are available in the library. The
first is the transport of [Stacks, Tag 08DL] from the slice site `Opens X / U` to the affine open
*subscheme* `U ≅ Spec Γ(X, U)`; that is
`Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso` together with
`Stacks.SheafOfModules.derivedSheafHomSchemeIsoIso`, both in
`StacksFrontier/AlgebraicGeometry/Duality/OpenImmersion/`. The second is the derived Spec–Γ
equivalence of [Stacks, Tag 06Z0], needed to recognize a sheaf-level object of
`D⁻_Coh(𝒪_{Spec R})` as a sheafification; `AlgebraicGeometry.derivedTilde_isEquivalence` is an
unconditional instance in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalence.lean`, and the recognition
statement itself is `AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory`.

## Implementation notes

The derived category is the standard model, `CategoryTheory.HasDerivedCategory.standard`, which
is the model `AlgebraicGeometry.affinePseudoCoherentDerivedSheafHomIso` and
`Stacks.SheafOfModules.isBoundedBelow_derivedSheafHom` are stated at. The locally small model of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` is a *global* instance and would displace
that choice, giving a derived category that is a different type; the import surface is kept
minimal for that reason, and in particular the quasi-coherence statements of
`StacksFrontier/AlgebraicGeometry/DerivedTilde/Basic.lean` are not used.

`D⁻_Coh(R)` and `D⁺_Coh(R)` are `DerivedCategoryB.derivedCategoryBMinus` and
`DerivedCategoryB.derivedCategoryBPlus` applied to finiteness of modules, which is the spelling
[Stacks, Tag 0A72] is stated at in this library, coherent and finite agreeing over a Noetherian
ring. On the sheaf side the object property is
`Stacks.SheafOfModules.coherentModules (Spec R).ringCatSheaf`.

## References

* [Stacks Project, Tag 0D0C](https://stacks.math.columbia.edu/tag/0D0C)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 066E](https://stacks.math.columbia.edu/tag/066E)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance] Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor

universe u

namespace AlgebraicGeometry

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive

/-! ### Seating the tensor instances

The universes of the site `Opens Y` and of the sections of `𝒪_Y` coincide here, so the total
complex instance the derived internal Hom of a ringed space is stated with is named rather than
synthesized, as in `StacksFrontier/AlgebraicGeometry/Perfect/KoszulCohomologyComparison.lean`; the
two additivity facts it rests on are the shared
`Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive` and `sheafTensorObjAdditive`,
named for the same reason, and are brought into local instance search for the whole file above. -/

section TensorInstances

variable {Y : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} Y)

/-- The total complexes of the tensor double complexes of complexes of `𝒪_Y`-modules exist. -/
private instance hasMapBifunctorSheafTensor :
    ∀ K₁ K₂ : HomologicalComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Rc))
        (ComplexShape.up ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂
        (Stacks.SheafOfModules.Tensor.sheafTensor Rc) (ComplexShape.up ℤ) :=
  fun _ _ ↦ inferInstance

end TensorInstances

variable (R : CommRingCat.{u})

/-- The degree-`n` cohomology sheaf of a derived sheafification is the sheaf associated with the
degree-`n` cohomology module: sheafification is exact, so it commutes with taking cohomology. -/
private def homologyTildeDerivedIso (M : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (Spec R).Modules n).obj
        ((tilde.functor R).mapDerivedCategory.obj M) ≅
      tilde ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj M) :=
  (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
    (tilde.functor R) n).app M

/-- **The cohomology sheaves of a derived sheafification are coherent as soon as the cohomology
modules are finite.** Over a Noetherian ring the sheaf associated with a finite module is
coherent ([Stacks, Tag 01XZ]), and the degree-`n` cohomology sheaf of a sheafification is the
sheaf associated with the degree-`n` cohomology module. -/
theorem isCoherent_homology_tildeDerived [IsNoetherianRing R]
    (M : DerivedCategory (ModuleCat.{u} R)) (n : ℤ)
    (h : Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj M)) :
    Stacks.SheafOfModules.IsCoherent
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
        ((tilde.functor R).mapDerivedCategory.obj M)) :=
  have := h
  (Stacks.SheafOfModules.coherentModules (Spec R).ringCatSheaf).prop_of_iso
    (homologyTildeDerivedIso R M n).symm
    (Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_tilde _)

/-- The cohomology sheaf of a derived sheafification vanishes where the cohomology module does. -/
private theorem isZero_homology_tildeDerived (M : DerivedCategory (ModuleCat.{u} R)) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M)) :
    IsZero ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj
      ((tilde.functor R).mapDerivedCategory.obj M)) :=
  ((homologyTildeDerivedIso R M i).isZero_iff).2 ((tilde.functor R).map_isZero h)

/-- A derived sheafification has no cohomology above a bound of the sheafified object: the
cohomology sheaves are the sheaves associated with the cohomology modules, and sheafification is
additive. -/
theorem isBoundedAbove_tildeDerived (M : DerivedCategory (ModuleCat.{u} R)) (d : ℤ)
    (hM : ∀ i : ℤ, d < i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M)) :
    DerivedCategoryB.IsBoundedAbove ((tilde.functor R).mapDerivedCategory.obj M) :=
  ⟨d, fun i hi =>
    isZero_homology_tildeDerived R M i (hM i hi)⟩

/-- A derived sheafification has no cohomology below a bound of the sheafified object. -/
theorem isBoundedBelow_tildeDerived (M : DerivedCategory (ModuleCat.{u} R)) (b : ℤ)
    (hM : ∀ i : ℤ, i < b → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M)) :
    DerivedCategoryB.IsBoundedBelow ((tilde.functor R).mapDerivedCategory.obj M) :=
  ⟨b, fun i hi =>
    isZero_homology_tildeDerived R M i (hM i hi)⟩

variable [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The coherence clause of [Stacks, Tag 0D0C] on an affine scheme, for sheafified arguments.**
Let `R` be a Noetherian ring, let `K` be an object of `D(R)` vanishing in degrees above `d` with
finite cohomology modules, and let `L` be an object of `D(R)` vanishing in degrees below `b` with
finite cohomology modules. Then every cohomology sheaf of `R𝓗om_{𝒪_{Spec R}}(K̃, L̃)` is a
coherent `𝒪_{Spec R}`-module.

`K` is pseudo-coherent by [Stacks, Tag 066E], so part (3)(a) of [Stacks, Tag 0A6H] identifies the
derived internal Hom with the sheafification of `RHom_R(K, L)`; the cohomology modules of the
latter are finite by `StacksDraft.DerivedHom.finite_homology_derivedHom`, and the cohomology
sheaves of a sheafification with finite cohomology modules are coherent. -/
theorem isCoherent_homology_affineDerivedSheafHom [IsNoetherianRing R]
    (K L : DerivedCategory (ModuleCat.{u} R)) (d b : ℤ)
    (hKle : K.IsLE d) (hLge : L.IsGE b)
    (hK : ∀ k : ℤ, Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) k).obj K))
    (hL : ∀ k : ℤ, Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) k).obj L)) (n : ℤ) :
    Stacks.SheafOfModules.IsCoherent
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
        (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
            (op ((tilde.functor R).mapDerivedCategory.obj K))).obj
              ((tilde.functor R).mapDerivedCategory.obj L))) := by
  have hKpc : StacksDraft.PseudoCoherence.IsPseudoCoherent K := by
    have := hKle
    refine ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      K 0 (R : Type u)).2.1).2 ⟨⟨d, fun i hi => ?_⟩, hK⟩
    exact DerivedCategory.isZero_of_isLE K d i hi
  have hLplus : (DerivedCategory.TStructure.t).plus L := ⟨b, hLge⟩
  have hfin := StacksDraft.DerivedHom.finite_homology_derivedHom
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := (R : Type u))) K L d b hKle hLge hK hL n
  exact (Stacks.SheafOfModules.coherentModules (Spec R).ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor (Spec R).Modules n).mapIso
      (affinePseudoCoherentDerivedSheafHomIso R K L hKpc hLplus)).symm
    (isCoherent_homology_tildeDerived R _ n hfin)

/-- **The coherence clause of [Stacks, Tag 0D0C] on an affine scheme.** Let `R` be a Noetherian
ring, let `K` be an object of `D⁻_Coh(R)` and `L` an object of `D⁺_Coh(R)`. Then
`R𝓗om_{𝒪_{Spec R}}(K̃, L̃)` lies in `D⁺_Coh(𝒪_{Spec R})`: it is cohomologically bounded below and
all of its cohomology sheaves are coherent.

Boundedness below is `Stacks.SheafOfModules.isBoundedBelow_derivedSheafHom`, the clause of the
tag the library already carries, applied after transporting the bounds of `K` and `L` to their
sheafifications. Coherence is `isCoherent_homology_affineDerivedSheafHom`.

The hypotheses are on the module-level objects `K` and `L`; the source states the tag for objects
of `D⁻_Coh(𝒪_X)` and `D⁺_Coh(𝒪_X)` on an arbitrary locally Noetherian `X`, and neither the
reduction to an affine open nor the identification of a sheaf-level coherent complex with a
sheafification ([Stacks, Tag 06Z0]) is carried out here; see the module documentation. -/
@[stacks 0D0C "the coherence clause on Spec R, for sheafified D⁻_Coh and D⁺_Coh arguments"]
theorem derivedCategoryBPlus_coherent_affineDerivedSheafHom [IsNoetherianRing R]
    (K L : DerivedCategory (ModuleCat.{u} R))
    (hK : DerivedCategoryB.derivedCategoryBMinus
      (fun M : ModuleCat.{u} R => Module.Finite R M) K)
    (hL : DerivedCategoryB.derivedCategoryBPlus
      (fun M : ModuleCat.{u} R => Module.Finite R M) L) :
    DerivedCategoryB.derivedCategoryBPlus (A := (Spec R).Modules)
      (Stacks.SheafOfModules.coherentModules (Spec R).ringCatSheaf)
      (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
          (op ((tilde.functor R).mapDerivedCategory.obj K))).obj
            ((tilde.functor R).mapDerivedCategory.obj L)) := by
  obtain ⟨d, hd⟩ := hK.1
  obtain ⟨b, hb⟩ := hL.1
  have hKle : K.IsLE (d + 1) :=
    (DerivedCategory.isLE_iff K (d + 1)).mpr fun i hi => hd i (by omega)
  have hLge : L.IsGE b := (DerivedCategory.isGE_iff L b).mpr hb
  refine ⟨Stacks.SheafOfModules.isBoundedBelow_derivedSheafHom (Spec R).sheaf _ _
    (isBoundedAbove_tildeDerived R K d hd) (isBoundedBelow_tildeDerived R L b hb), fun n => ?_⟩
  exact isCoherent_homology_affineDerivedSheafHom R K L (d + 1) b hKle hLge hK.2 hL.2 n

/-- `derivedCategoryBPlus_coherent_affineDerivedSheafHom` read with the root coherence predicate
`SheafOfModules.IsCoherent` of [Stacks, Tag 01BW], which is the spelling the schemes material —
and in particular [Stacks, Tag 0D0B] — uses. The two predicates have the same two fields and are
identified by `AlgebraicGeometry.CoherentAbelian.coherentModules_eq`.

No `@[stacks 0D0C]` attribute is attached: this restates
`derivedCategoryBPlus_coherent_affineDerivedSheafHom`, which carries the tag, in a second
vocabulary, and tagging both would record the same case twice. -/
theorem derivedCategoryBPlus_isCoherent_affineDerivedSheafHom [IsNoetherianRing R]
    (K L : DerivedCategory (ModuleCat.{u} R))
    (hK : DerivedCategoryB.derivedCategoryBMinus
      (fun M : ModuleCat.{u} R => Module.Finite R M) K)
    (hL : DerivedCategoryB.derivedCategoryBPlus
      (fun M : ModuleCat.{u} R => Module.Finite R M) L) :
    DerivedCategoryB.derivedCategoryBPlus (A := (Spec R).Modules)
      (fun M : (Spec R).Modules => M.IsCoherent)
      (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
          (op ((tilde.functor R).mapDerivedCategory.obj K))).obj
            ((tilde.functor R).mapDerivedCategory.obj L)) := by
  obtain ⟨hbd, hcoh⟩ := derivedCategoryBPlus_coherent_affineDerivedSheafHom R K L hK hL
  exact ⟨hbd, fun n => CoherentAbelian.isCoherent_of_stacksIsCoherent (hcoh n)⟩

end AlgebraicGeometry

end
