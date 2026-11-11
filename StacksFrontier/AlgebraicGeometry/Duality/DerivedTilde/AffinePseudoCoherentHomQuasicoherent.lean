module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePseudoCoherentDerivedHom
public import StacksFrontier.Homology.HomComplex.Evaluation.Iterated

/-!
# The derived internal Hom out of a pseudo-coherent sheafification lies in `D⁺_QCoh`

Let `R` be a commutative ring and `X = Spec R`. Part (3)(a) of [Stacks, Tag 0A6H] identifies the
derived internal Hom of two sheafifications with a sheafification,

`R𝓗om_{𝒪_X}(K̃, L̃) ≅ (RHom_R(K, L))~`

for `K` pseudo-coherent and `L` bounded below; this is
`AlgebraicGeometry.affinePseudoCoherentDerivedSheafHomIso`. Part (1) of the same tag draws the
consequence the source draws from it: the derived internal Hom has quasi-coherent cohomology
sheaves and is locally bounded below. This file proves that consequence on an affine scheme,
for the two sheafified arguments the comparison speaks about.

Both halves are read off the comparison. Every cohomology sheaf of a sheafification is
quasi-coherent, so the right-hand side has quasi-coherent cohomology and the left-hand side
inherits it. For the lower bound, `K` is represented by a complex `E` vanishing above `b` with
finite free terms and `L` by a complex `J` vanishing below `a`; the Hom complex `Hom^•(E, J)`
then vanishes below `a - b`, so `RHom_R(K, L)` does, and sheafification is additive, so the
sheafified complex vanishes below `a - b` as well.

## Main results

* `AlgebraicGeometry.isQuasicoherent_homology_affinePseudoCoherentDerivedSheafHom` — every
  cohomology sheaf of `R𝓗om_{𝒪_X}(K̃, L̃)` is quasi-coherent.
* `AlgebraicGeometry.isBoundedBelow_affinePseudoCoherentDerivedSheafHom` —
  `R𝓗om_{𝒪_X}(K̃, L̃)` has no cohomology in sufficiently negative degrees.
* `AlgebraicGeometry.derivedCategoryBPlus_affinePseudoCoherentDerivedSheafHom` — the two
  together: `R𝓗om_{𝒪_X}(K̃, L̃)` lies in `D⁺_QCoh(𝒪_X)`.

## Implementation notes

What is proved here is part (1) of [Stacks, Tag 0A6H] *for an affine scheme and for arguments
already presented as sheafifications*. The source deduces part (1) in general by localizing and
then invoking part (3); the localization step and the identification of a pseudo-coherent object
of `D(𝒪_X)` with the sheafification of a pseudo-coherent object of `D(R)` ([Stacks, Tag 08E7])
are not used here, so the hypotheses name module-level data rather than deriving it from
sheaf-level data. The two steps are taken in
`StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineSheafPseudoCoherentHomQuasicoherent`
and in
`StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeSheafPseudoCoherentHomQuasicoherent`,
which is where part (1) reaches an arbitrary object of `D(𝒪_Y)` on an arbitrary scheme `Y`.

`AlgebraicGeometry.affinePseudoCoherentDerivedSheafHomIso` is stated at
`CategoryTheory.HasDerivedCategory.standard`, which its own file selects by a file-level local
instance. The locally small model of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`
is a *global* instance and so would displace that choice, giving a derived category that is a
different type and leaving the comparison inapplicable. This file therefore imports nothing that
reaches that file, and for the same reason it restates, as the private
`AlgebraicGeometry.isQuasicoherent_homology_tildeDerived`, the content of
`AlgebraicGeometry.isQuasicoherent_homology_mapDerivedCategory_obj`
(`StacksFrontier/AlgebraicGeometry/DerivedTilde/Basic.lean`), which is unreachable for that reason;
the two proofs are the same and the public statement to prefer is the one in that file.

## References

* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 0A66](https://stacks.math.columbia.edu/tag/0A66)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- **[Stacks, Tag 06Z0].** Every cohomology sheaf of the image of a complex of `R`-modules under
derived sheafification is quasi-coherent: the object is isomorphic to one of the form `Q(P^•)`,
and the degree-`n` cohomology of `Q(P̃^•)` is `H^n(P^•)^~` because `~` is exact.

This is `AlgebraicGeometry.isQuasicoherent_homology_mapDerivedCategory_obj`, restated at the
standard model of the derived category because the file carrying that statement also installs the
locally small model as a global instance. -/
theorem isQuasicoherent_homology_tildeDerived (R : CommRingCat.{u})
    (M : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) :
    SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
        ((tilde.functor R).mapDerivedCategory.obj M)) := by
  obtain ⟨P, ⟨e⟩⟩ : (DerivedCategory.Q (C := ModuleCat.{u} R)).essImage M :=
    Functor.EssSurj.mem_essImage (F := DerivedCategory.Q) M
  let F := tilde.functor R
  let ε : (DerivedCategory.homologyFunctor (Spec R).Modules n).obj
      (F.mapDerivedCategory.obj M) ≅ F.obj (P.homology n) :=
    (DerivedCategory.homologyFunctor (Spec R).Modules n).mapIso
        (F.mapDerivedCategory.mapIso e.symm) ≪≫
      (DerivedCategory.homologyFunctor (Spec R).Modules n).mapIso
        (F.mapDerivedCategoryFactors.app P) ≪≫
      (DerivedCategory.homologyFunctorFactors _ n).app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≪≫
      (P.sc n).mapHomologyIso F
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso ε.symm inferInstance

/-- **Part (1) of [Stacks, Tag 0A6H], the quasi-coherence half, on an affine scheme.** For `K`
pseudo-coherent and `L` bounded below in `D(R)`, every cohomology sheaf of
`R𝓗om_{𝒪_{Spec R}}(K̃, L̃)` is quasi-coherent.

The comparison `AlgebraicGeometry.affinePseudoCoherentDerivedSheafHomIso` identifies that object
with a sheafification, whose cohomology sheaves are quasi-coherent, and quasi-coherence is closed
under isomorphisms. -/
theorem isQuasicoherent_homology_affinePseudoCoherentDerivedSheafHom (R : CommRingCat.{u})
    [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (K L : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hL : (DerivedCategory.TStructure.t).plus L) (n : ℤ) :
    SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
        (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
            (op ((tilde.functor R).mapDerivedCategory.obj K))).obj
              ((tilde.functor R).mapDerivedCategory.obj L))) :=
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor (Spec R).Modules n).mapIso
      (affinePseudoCoherentDerivedSheafHomIso R K L hK hL)).symm
    (isQuasicoherent_homology_tildeDerived R _ n)

/-- **Part (1) of [Stacks, Tag 0A6H], the lower-bound half, on an affine scheme.** For `K`
pseudo-coherent and `L` bounded below in `D(R)`, the object `R𝓗om_{𝒪_{Spec R}}(K̃, L̃)` has no
cohomology in sufficiently negative degrees.

Pick a representative `E` of `K` vanishing above `b` with finite free — hence projective — terms,
and a representative `J` of `L` vanishing below `a`. The Hom complex `Hom^•(E, J)` vanishes below
`a - b`, and it computes `RHom_R(K, L)` by [Stacks, Tag 0A66]; sheafification is additive, so the
associated complex of sheaves vanishes below `a - b` too. The comparison carries that bound back
to the derived internal Hom. -/
theorem isBoundedBelow_affinePseudoCoherentDerivedSheafHom (R : CommRingCat.{u})
    [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (K L : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hL : (DerivedCategory.TStructure.t).plus L) :
    DerivedCategoryB.IsBoundedBelow
      (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
          (op ((tilde.functor R).mapDerivedCategory.obj K))).obj
            ((tilde.functor R).mapDerivedCategory.obj L)) := by
  obtain ⟨E, hE, ⟨eE⟩⟩ := id hK
  obtain ⟨b, hb⟩ := hE.upperBound
  obtain ⟨a, ha⟩ := id hL
  have hLGE : (DerivedCategory.TStructure.t).IsGE L a := ha
  obtain ⟨J, hJ, ⟨eJ⟩⟩ := L.exists_iso_Q_obj_of_isGE a
  have : ∀ i, Projective (E.X i) := fun i => by
    have := (hE.finiteFree i).2
    infer_instance
  have hC : CochainComplex.IsStrictlyGE
      (CochainComplex.HomComplexR (R : Type u) E J) (a - b) :=
    StacksDraft.DerivedHom.homComplexR_isStrictlyGE E J b a hb hJ
  have hCt : CochainComplex.IsStrictlyGE
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CochainComplex.HomComplexR (R : Type u) E J)) (a - b) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact (tilde.functor R).map_isZero
      ((CochainComplex.HomComplexR (R : Type u) E J).isZero_of_isStrictlyGE (a - b) i hi)
  let ι := affinePseudoCoherentDerivedSheafHomIso R K L hK hL ≪≫
    (tilde.functor R).mapDerivedCategory.mapIso
      ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.mapIso
          (Iso.prod eE.op eJ) ≪≫
        (StacksDraft.DerivedHom.projectiveHomComparison (R := R)).iso E J b) ≪≫
    (tilde.functor R).mapDerivedCategoryFactors.app
      (CochainComplex.HomComplexR (R : Type u) E J)
  have hGE : (DerivedCategory.TStructure.t).IsGE
      ((((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
        DerivedCategory.Q).obj (CochainComplex.HomComplexR (R : Type u) E J)) (a - b) :=
    inferInstanceAs ((DerivedCategory.TStructure.t).IsGE
      (DerivedCategory.Q.obj (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CochainComplex.HomComplexR (R : Type u) E J))) (a - b))
  have hres := DerivedCategory.TStructure.t.isGE_of_iso ι.symm (a - b)
  exact ⟨a - b, (DerivedCategory.isGE_iff _ (a - b)).1 hres⟩

/-- **Part (1) of [Stacks, Tag 0A6H] on an affine scheme.** For `K` pseudo-coherent and `L`
bounded below in `D(R)`, the derived internal Hom `R𝓗om_{𝒪_{Spec R}}(K̃, L̃)` lies in
`D⁺_QCoh(𝒪_{Spec R})`: its cohomology sheaves are quasi-coherent and vanish in sufficiently
negative degrees.

On an affine scheme "locally bounded below" is bounded below, so this is the full conclusion of
part (1) for the two sheafified arguments part (3)(a) speaks about. The conditions are on the
module-level objects `K` and `L`; the form for a pseudo-coherent object of `D(𝒪_{Spec R})` is
`AlgebraicGeometry.derivedCategoryBPlus_affineDerivedSheafHom_of_isPseudoCoherent`, and part (1)
on an arbitrary scheme is `AlgebraicGeometry.derivedCategoryB_derivedSheafHom_of_isPseudoCoherent`
with `AlgebraicGeometry.isLocallyBoundedBelow_derivedSheafHom_of_isPseudoCoherent`. -/
theorem derivedCategoryBPlus_affinePseudoCoherentDerivedSheafHom (R : CommRingCat.{u})
    [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (K L : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hL : (DerivedCategory.TStructure.t).plus L) :
    DerivedCategoryB.derivedCategoryBPlus (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)
      (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
          (op ((tilde.functor R).mapDerivedCategory.obj K))).obj
            ((tilde.functor R).mapDerivedCategory.obj L)) :=
  ⟨isBoundedBelow_affinePseudoCoherentDerivedSheafHom R K L hK hL,
    isQuasicoherent_homology_affinePseudoCoherentDerivedSheafHom R K L hK hL⟩

end AlgebraicGeometry

end
