module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.NoetherianCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportQuasicoherent
public import StacksFrontier.RingTheory.Dualizing.CoextendRestrictComparison.A72
public import StacksFrontier.RingTheory.Dualizing.TrivialDualityRing.Basic

/-!
# Derived sheaf Hom with exact support on coherent complexes

Let `i : Z ⟶ X` be a closed immersion of schemes with `X` locally Noetherian. [Stacks, Tag 0A79]
asserts that `R ℰom(𝒪_Z, -)` maps `D⁺_Coh(𝒪_X)` into `D⁺_Coh(𝒪_Z)`. The assertion has two
independent halves, and this file proves them separately.

*Boundedness below* is the half that needs nothing: `D⁺_Coh(𝒪_X)` is contained in `D⁺(𝒪_X)`, and
`R ℰom(𝒪_Z, -)` is left t-exact for any closed quotient morphism of ringed spaces. This is
`AlgebraicGeometry.Scheme.isBoundedBelow_derivedSheafHomExactSupport_of_isCoherent`, with no
hypothesis beyond the statement's own.

*Coherence of the cohomology sheaves* is the content. The source argues that the question is
local on `X`, reduces to `X = Spec A` and `Z = Spec B` with `A` Noetherian and `A → B`
surjective, transports the question to algebra along [Stacks, Tag 0A78] and finishes with
[Stacks, Tag 0A72]. The affine step of that argument is carried out here, in
`AlgebraicGeometry.affineDerivedSheafHomExactSupport_mem_derivedCategoryBPlus_coherent`: part (2)
of [Stacks, Tag 0A78] identifies `R ℰom(𝒪_Z, L^~)` with `(R Hom_A(B, L))^~`, [Stacks, Tag 0A72]
puts `R Hom_A(B, L)` in `D⁺_Coh(B)`, and the sheaf associated to a finite module over a
Noetherian ring is coherent ([Stacks, Tag 01XZ]).

## Main results

* `AlgebraicGeometry.Scheme.isBoundedBelow_derivedSheafHomExactSupport_of_isCoherent` — the
  bounded-below half of [Stacks, Tag 0A79], for every closed immersion.
* `AlgebraicGeometry.isCoherent_homology_tilde_mapDerivedCategory_obj` — over a Noetherian ring,
  a cohomology sheaf of a derived sheafification is coherent as soon as the corresponding
  cohomology module is finite.
* `AlgebraicGeometry.derivedCategoryBPlus_coherent_tilde_mapDerivedCategory_obj` — derived
  sheafification carries `D⁺_Coh(R)` into `D⁺_Coh(𝒪_{Spec R})`.
* `AlgebraicGeometry.finite_of_isClosedImmersion_specMap` — the ring map underlying a closed
  immersion of affine schemes is finite.
* `AlgebraicGeometry.derivedCategoryBPlus_finite_derivedHom_obj` — [Stacks, Tag 0A72] read on
  `Dualizing.derivedHom`.
* `AlgebraicGeometry.affineDerivedSheafHomExactSupport_mem_derivedCategoryBPlus_coherent` — the
  coherent half of [Stacks, Tag 0A79] in the affine case.

## Implementation notes

**Which `D⁺_Coh` this is.** Membership is `DerivedCategoryB.derivedCategoryBPlus` applied to
`Stacks.SheafOfModules.coherentModules X.ringCatSheaf`, exactly parallel to the
`SheafOfModules.isQuasicoherent X.ringCatSheaf` that [Stacks, Tag 0A78] uses one file over. The
repository has two coherence predicates with the same two fields — the root
`SheafOfModules.IsCoherent` of [Stacks, Tag 01BW] and `Stacks.SheafOfModules.IsCoherent` — and
the second is the one the closure theory of [Stacks, Tag 01BY] is proved for; they are identified
by `AlgebraicGeometry.CoherentAbelian.isCoherent_iff_stacksIsCoherent`.

The named object property is load-bearing, not cosmetic. Writing the property as the lambda
`fun M : X.Modules => M.IsCoherent` — the spelling that
`StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/BoundedBelowDerivedDirectImage.lean` uses
for [Stacks, Tag 0D0B] — pins the ambient category to `AlgebraicGeometry.Scheme.Modules`, which is a
`def`; the object produced by `derivedSheafHomExactSupport` lives in the
`structureSheafRing` spelling, and unifying the two across that `def` loses the
`Abelian` instance. This is the same three-spellings hazard recorded in the implementation notes
of `ExactSupportQuasicoherent.lean`.

On the algebra side `D⁺_Coh(R)` is
`DerivedCategoryB.derivedCategoryBPlus (fun M => Module.Finite R M)`, which is the spelling
[Stacks, Tag 0A72] is stated at, coherent and finite agreeing over a Noetherian ring.

**Neither declaration below carries a hypothesis.** Part (2) of [Stacks, Tag 0A78], which the
affine case is proved from, is itself unconditional; the coherence of the image is proved, from
[Stacks, Tag 0A72], and not assumed. The adjunction of [Stacks, Tag 0A70] is not carried either:
the conclusion is a proposition, so the `Nonempty` that
`Dualizing.restrictScalarsDerived_adj_derivedHom` provides is destructed inside the proof.

**The passage from the affine case to a general locally Noetherian `X` is not carried out here**,
but it is carried out in the library:
`AlgebraicGeometry.derivedSheafHomExactSupport_mem_derivedCategoryBPlus_coherent` of
`StacksFrontier/AlgebraicGeometry/Duality/DerivedTilde/SchemeCoherentDerivedHom.lean` is
[Stacks, Tag 0A79] for every closed immersion into a locally Noetherian scheme, and carries the
unqualified attribute. The two attributes attached below therefore each carry a suffix naming the
half and the case they cover; they are not the tag's full content.

The globalization does not need a restriction isomorphism for
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomExactSupport`
along an open immersion: no such isomorphism is in the library, and none is needed. The
globalization goes through `i_*` instead,
which turns `R ℰom(𝒪_Z, K)` into the ordinary derived internal Hom `R𝓗om_{𝒪_X}(Ri_*𝒪_Z, K)` by
[Stacks, Tag 0A77] and so reduces the question to [Stacks, Tag 0D0C] on `X`, where restriction to
an open subscheme *is* available ([Stacks, Tag 08DL]).

## References

* [Stacks Project, Tag 0A79](https://stacks.math.columbia.edu/tag/0A79)
* [Stacks Project, Tag 0A78](https://stacks.math.columbia.edu/tag/0A78)
* [Stacks Project, Tag 0A72](https://stacks.math.columbia.edu/tag/0A72)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

namespace Scheme

/-- **Stacks Project, Tag 0A79, the bounded-below half.** Let `i : Z ⟶ X` be a closed immersion
of schemes with `X` locally Noetherian. Then `R ℰom(𝒪_Z, -)` carries an object of `D⁺_Coh(𝒪_X)`
to an object of `D⁺(𝒪_Z)`.

An object of `D⁺_Coh(𝒪_X)` is in particular bounded below, and
`isBoundedBelow_derivedSheafHomExactSupport_obj` in the namespace
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces` says that `R ℰom(𝒪_Z, -)`,
being the right derived functor of a left exact functor, preserves boundedness below. Neither
step uses coherence or the Noetherian hypothesis. -/
theorem isBoundedBelow_derivedSheafHomExactSupport_of_isCoherent
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hK : DerivedCategoryB.derivedCategoryBPlus
      (Stacks.SheafOfModules.coherentModules X.ringCatSheaf) K) :
    DerivedCategoryB.IsBoundedBelow
      ((Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
        i).derivedSheafHomExactSupport.obj K) :=
  (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
    i).isBoundedBelow_derivedSheafHomExactSupport_obj K hK.1

end Scheme

/-! ### Derived sheafification and coherence -/

/-- **A cohomology sheaf of a derived sheafification is coherent when the cohomology module is
finite.** Derived sheafification is exact, so the degree-`n` cohomology sheaf of `L^~` is the
sheaf associated to `Hⁿ(L)`; over a Noetherian ring that sheaf is of finite type exactly when the
module is finite ([Stacks, Tag 01PB]), and a quasi-coherent module of finite type on a locally
Noetherian scheme is coherent ([Stacks, Tag 01XZ]). -/
theorem isCoherent_homology_tilde_mapDerivedCategory_obj (R : CommRingCat.{u})
    [IsNoetherianRing R] (L : DerivedCategory (ModuleCat.{u} R)) (n : ℤ)
    (h : Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj L)) :
    Stacks.SheafOfModules.IsCoherent
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
        ((tilde.functor R).mapDerivedCategory.obj L)) := by
  have _ : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_Spec.mpr ‹_›
  have hft : SheafOfModules.IsFiniteType.{u, u, u}
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n ⋙ tilde.functor R).obj L) :=
    (tilde_isFiniteType_iff _).mpr h
  have _ : ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
      ((tilde.functor R).mapDerivedCategory.obj L)).IsFiniteType :=
    have := hft
    Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
        (tilde.functor R) n).app L).symm
  have _ : ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
      ((tilde.functor R).mapDerivedCategory.obj L)).IsQuasicoherent :=
    AlgebraicGeometry.affineTilde_isQuasicoherent R L n
  exact Stacks.AlgebraicGeometry.CoherentTFAE.stacksIsCoherent_of_isQuasicoherent_of_isFiniteType _

/-- **Derived sheafification carries `D⁺_Coh(R)` into `D⁺_Coh(𝒪_{Spec R})`** for `R` Noetherian.
Boundedness below is `AlgebraicGeometry.isBoundedBelow_tilde_mapDerivedCategory_obj` and each
cohomology sheaf is `AlgebraicGeometry.isCoherent_homology_tilde_mapDerivedCategory_obj`. -/
theorem derivedCategoryBPlus_coherent_tilde_mapDerivedCategory_obj (R : CommRingCat.{u})
    [IsNoetherianRing R] (L : DerivedCategory (ModuleCat.{u} R))
    (hL : DerivedCategoryB.derivedCategoryBPlus
      (fun M : ModuleCat.{u} R => Module.Finite R M) L) :
    DerivedCategoryB.derivedCategoryBPlus
      (Stacks.SheafOfModules.coherentModules (Spec R).ringCatSheaf)
      ((tilde.functor R).mapDerivedCategory.obj L) :=
  ⟨isBoundedBelow_tilde_mapDerivedCategory_obj R L hL.1,
    fun n => isCoherent_homology_tilde_mapDerivedCategory_obj R L n (hL.2 n)⟩

/-! ### The algebra side -/

/-- **The ring map underlying a closed immersion of affine schemes is finite.** A closed immersion
with affine target has affine source and is surjective on global sections, and on `Spec` of a ring
map that surjectivity is surjectivity of the map itself; a surjective ring map is finite. -/
theorem finite_of_isClosedImmersion_specMap {A B : CommRingCat.{u}} (φ : A ⟶ B)
    [IsClosedImmersion (Spec.map φ)] : φ.hom.Finite :=
  RingHom.Finite.of_surjective φ.hom
    ((RingHom.surjective_respectsIso.arrow_mk_iso_iff (arrowIsoΓSpecOfIsAffine φ)).mpr
      (IsClosedImmersion.isAffine_surjective_of_isAffine (f := Spec.map φ)).2)

/-- **[Stacks, Tag 0A72] for `Dualizing.derivedHom`.** For a closed immersion of affine schemes
`Spec B ⟶ Spec A` with `A` and `B` Noetherian, `R Hom_A(B, -)` carries `D⁺_Coh(A)` into
`D⁺_Coh(B)`.

`Dualizing.derivedHom` is a right derived functor of coextension of scalars for its own
total-derived unit, so `Dualizing.isBoundedBelowCoherent_obj_rightDerivedCoextendScalars` applies
to it; the ring map is finite by `AlgebraicGeometry.finite_of_isClosedImmersion_specMap`. -/
theorem derivedCategoryBPlus_finite_derivedHom_obj {A B : CommRingCat.{u}} (φ : A ⟶ B)
    [IsNoetherianRing A] [IsNoetherianRing B] [IsClosedImmersion (Spec.map φ)]
    (L : DerivedCategory (ModuleCat.{u} A))
    (hL : DerivedCategoryB.derivedCategoryBPlus
      (fun M : ModuleCat.{u} A => Module.Finite A M) L) :
    DerivedCategoryB.derivedCategoryBPlus
      (fun M : ModuleCat.{u} B => Module.Finite B M)
      ((Dualizing.derivedHom.{u, u, u} φ.hom).obj L) :=
  Dualizing.isBoundedBelowCoherent_obj_rightDerivedCoextendScalars φ.hom
    (finite_of_isClosedImmersion_specMap φ) (Dualizing.derivedHom.{u, u, u} φ.hom)
    ((Dualizing.coextendScalarsToDerivedCategory φ.hom).totalRightDerivedUnit
      DerivedCategory.Qh (HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))) hL

/-! ### The coherent half of Tag 0A79, affine case -/

/-- **Stacks Project, Tag 0A79, the coherent half, affine case.** Let `φ : A ⟶ B` be a ring map
whose spectrum is a closed immersion `i : Z = Spec B ⟶ X = Spec A`, with `A` and `B` Noetherian,
and let `L` be an object of `D⁺_Coh(A)`. Then `R ℰom(𝒪_Z, L^~)` lies in `D⁺_Coh(𝒪_Z)`.

This is the affine step of the argument of the source. Part (2) of [Stacks, Tag 0A78] identifies
`R ℰom(𝒪_Z, L^~)` with `(R Hom_A(B, L))^~`; [Stacks, Tag 0A72], in the form
`AlgebraicGeometry.derivedCategoryBPlus_finite_derivedHom_obj`, puts `R Hom_A(B, L)` in
`D⁺_Coh(B)`; and `AlgebraicGeometry.derivedCategoryBPlus_coherent_tilde_mapDerivedCategory_obj`
sheafifies that into `D⁺_Coh(𝒪_Z)`. Boundedness below is taken directly from
`AlgebraicGeometry.Scheme.isBoundedBelow_derivedSheafHomExactSupport_of_isCoherent` rather than
transported, and the cohomology sheaves are transported across the comparison isomorphism by
closure of coherence under isomorphisms ([Stacks, Tag 01BY]). -/
theorem affineDerivedSheafHomExactSupport_mem_derivedCategoryBPlus_coherent
    {A B : CommRingCat.{u}} (φ : A ⟶ B) [IsNoetherianRing A] [IsNoetherianRing B]
    [IsClosedImmersion (Spec.map φ)]
    (L : DerivedCategory (ModuleCat.{u} A))
    (hL : DerivedCategoryB.derivedCategoryBPlus
      (fun M : ModuleCat.{u} A => Module.Finite A M) L) :
    DerivedCategoryB.derivedCategoryBPlus
      (Stacks.SheafOfModules.coherentModules (Spec B).ringCatSheaf)
      ((Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
        (Spec.map φ)).derivedSheafHomExactSupport.obj
          ((tilde.functor A).mapDerivedCategory.obj L)) := by
  have hsrc := derivedCategoryBPlus_coherent_tilde_mapDerivedCategory_obj B _
    (derivedCategoryBPlus_finite_derivedHom_obj φ L hL)
  have _ : IsIso ((affineDerivedSheafHomComparison A B φ).app L) :=
    isIso_affineDerivedSheafHomComparison_app_of_noetherian A B φ L hL.1
  set e := asIso ((affineDerivedSheafHomComparison A B φ).app L) with he
  refine ⟨Scheme.isBoundedBelow_derivedSheafHomExactSupport_of_isCoherent (Spec.map φ) _
      (derivedCategoryBPlus_coherent_tilde_mapDerivedCategory_obj A L hL), fun n => ?_⟩
  exact (Stacks.SheafOfModules.coherentModules (Spec B).ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (Spec B).ringCatSheaf) n).mapIso e)
    (hsrc.2 n)

end AlgebraicGeometry

end
