module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentLocal
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SheafLevel
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.General
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeOpenImmersion
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.NestedRestriction
public import StacksFrontier.AlgebraicGeometry.QcohLimits.ClosedUnderKernels
public import StacksFrontier.AlgebraicGeometry.QcohLimits.ClosedUnderCokernels
import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherence of the cohomology of a pseudo-coherent complex

Let `X` be a scheme and let `E` be an `m`-pseudo-coherent object of `D(𝒪_X)`. Then `H^i(E)` is a
quasi-coherent `𝒪_X`-module for every `i > m`, and every point of `X` has a neighbourhood on
which `H^m(E)` is a quotient of a quasi-coherent module. Consequently a pseudo-coherent object
of `D(𝒪_X)` has quasi-coherent cohomology in every degree, that is, lies in `D_QCoh(𝒪_X)`.

## Main results

* `AlgebraicGeometry.isQuasicoherent_homology_of_isPseudoCoherent_scheme`: the whole of Stacks
  Lemma 08E5, with the degree-`m` clause in its corrected, local form.

* `AlgebraicGeometry.isQuasicoherent_homology_of_isStrictlyPerfect`: the cohomology of a strictly
  perfect complex on a scheme is quasi-coherent.
* `AlgebraicGeometry.isQuasicoherent_homology_of_isPseudoCoherentFrom`: `H^i(E)` is
  quasi-coherent for `i > m`.
* `AlgebraicGeometry.exists_local_epi_homology_of_isPseudoCoherentFrom`: in degree `m`, every
  point has a neighbourhood on which `H^m(E)` receives an epimorphism from a quasi-coherent
  module.
* `AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent`: a pseudo-coherent object lies
  in the full subcategory of `D(𝒪_X)` cut out by quasi-coherence of all cohomology sheaves.

## References

* [The Stacks Project, Lemma 36.10.1 (08E5)](https://stacks.math.columbia.edu/tag/08E5)
* [The Stacks Project, Definition 20.46.4 (08CB)](https://stacks.math.columbia.edu/tag/08CB)
* [The Stacks Project, Definition 20.46.1 (08C4)](https://stacks.math.columbia.edu/tag/08C4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u d

/-- A retract `E` of `F` is the kernel of `𝟙 F - r ≫ i`, the complementary idempotent of the
retraction. -/
private def retractIsoKernel {C : Type*} [Category C] [Preadditive C] [HasKernels C] {E F : C}
    (r : Retract E F) : E ≅ kernel (𝟙 F - r.r ≫ r.i) where
  hom := kernel.lift (𝟙 F - r.r ≫ r.i) r.i (by
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, r.retract,
      Category.id_comp, sub_self])
  inv := kernel.ι (𝟙 F - r.r ≫ r.i) ≫ r.r
  hom_inv_id := by simp [r.retract]
  inv_hom_id := by
    apply (cancel_mono (kernel.ι (𝟙 F - r.r ≫ r.i))).1
    have hk := kernel.condition (𝟙 F - r.r ≫ r.i)
    rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at hk
    simpa only [Category.assoc, kernel.lift_ι, Category.id_comp] using hk.symm

/-- A finite free `𝒪_X`-module on a scheme is quasi-coherent. -/
private lemma isQuasicoherent_finiteFree (X : Scheme.{u}) (n : ℕ) :
    (StrictlyPerfect.finiteFree X.toRingedSpace n).IsQuasicoherent := by
  let e : StrictlyPerfect.finiteFree X.toRingedSpace n ≅
      SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n)) :=
    biproduct.isoCoproduct _ ≪≫ (Sigma.reindex Equiv.ulift
      (fun _ : Fin n ↦ SheafOfModules.unit X.ringCatSheaf)).symm
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm inferInstance

/-- A direct summand of a finite free `𝒪_X`-module on a scheme is quasi-coherent. -/
private lemma isQuasicoherent_of_isDirectSummandOfFiniteFree (X : Scheme.{u})
    {M : StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace}
    (hM : StrictlyPerfect.IsDirectSummandOfFiniteFree M) : M.IsQuasicoherent := by
  let P := SheafOfModules.isQuasicoherent X.ringCatSheaf
  obtain ⟨n, ⟨r⟩⟩ := (StrictlyPerfect.isDirectSummandOfFiniteFree_iff_retract M).1 hM
  have hF : P (StrictlyPerfect.finiteFree X.toRingedSpace n) := isQuasicoherent_finiteFree X n
  exact P.prop_of_iso (retractIsoKernel r).symm (P.prop_kernel _ hF hF)

/-- The cohomology of a strictly perfect complex on a scheme is quasi-coherent. -/
public lemma isQuasicoherent_homology_of_isStrictlyPerfect (X : Scheme.{u})
    (K : CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace) ℤ)
    (hK : StrictlyPerfect.IsStrictlyPerfect K) (i : ℤ) : (K.homology i).IsQuasicoherent := by
  let P := SheafOfModules.isQuasicoherent X.ringCatSheaf
  have hcycles : P (K.cycles i) :=
    P.prop_of_iso
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel (K.d i (i + 1)))
        (K.cyclesIsKernel i (i + 1) (by simp)))
      (P.prop_kernel _ (isQuasicoherent_of_isDirectSummandOfFiniteFree X (hK.directSummand i))
        (isQuasicoherent_of_isDirectSummandOfFiniteFree X (hK.directSummand (i + 1))))
  exact P.prop_of_isColimit_cokernelCofork (K.homologyIsCokernel (i - 1) i (by simp))
    (isQuasicoherent_of_isDirectSummandOfFiniteFree X (hK.directSummand (i - 1))) hcycles

/-- The `i`-th cohomology of the restriction of a complex to an open subspace is the restriction
of its `i`-th cohomology. -/
private def restrictComplexHomologyIso (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (K : CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X) ℤ) (i : ℤ)
    [HomologicalComplex.HasHomology K i]
    [HomologicalComplex.HasHomology (RingedSpace.restrictComplex K U) i] :
    (RingedSpace.restrictComplex K U).homology i ≅
      (RingedSpace.restrictModules X U).obj (K.homology i) :=
  letI : (RingedSpace.restrictModules.{u, u} X U).PreservesHomology :=
    RingedSpace.restrictModules_preservesHomology X U
  (K.sc i).mapHomologyIso (RingedSpace.restrictModules X U)

/-- The `i`-th cohomology of the restriction of a complex to an open subscheme is the restriction
of its `i`-th cohomology, as a module on the open subscheme. -/
private def restrictComplexHomologyIsoRestrictFunctor (X : Scheme.{u}) (U : X.Opens)
    (K : CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace) ℤ) (i : ℤ) :
    (RingedSpace.restrictComplex K U).homology i ≅
      (Scheme.Modules.restrictFunctor U.ι).obj (K.homology i) :=
  restrictComplexHomologyIso X.toRingedSpace U K i ≪≫
    (RingedSpace.restrictModulesIsoRestrictFunctor X U).app (K.homology i)

/-- The cohomology of a complex is the cohomology of the object of the derived category it
represents. -/
private def homologyIsoOfIso (X : Scheme.{u})
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace)]
    (K : CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace) ℤ)
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace))
    (e : (DerivedCategory.Q).obj K ≅ E) (i : ℤ) :
    K.homology i ≅ ((DerivedCategory.homologyFunctor
      (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace) i).obj E) :=
  ((DerivedCategory.homologyFunctorFactors
    (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace) i).app K).symm ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso e

/-- Let `X` be a scheme and let `E` be an `m`-pseudo-coherent object of `D(𝒪_X)`. Then the
cohomology sheaf `H^i(E)` is a quasi-coherent `𝒪_X`-module for every `i > m`. -/
public theorem isQuasicoherent_homology_of_isPseudoCoherentFrom (X : Scheme.{u})
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace)]
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace)) (m i : ℤ)
    (hE : RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace) E m) (hi : m < i) :
    ((DerivedCategory.homologyFunctor
      (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace) i).obj E).IsQuasicoherent := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  choose U hxU P hP α hα _ using hK
  let W : X → X.Opens := fun x ↦ U x
  have hcover : ⨆ x : X, W x = ⊤ := by
    refine SetLike.ext fun x ↦ ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
    simpa only [Opens.mem_iSup] using ⟨x, hxU x⟩
  have hKq : (K.homology i).IsQuasicoherent := by
    refine Stacks.Modules.isQuasicoherent_of_restrict (K.homology i) W hcover fun x ↦ ?_
    have hlocal : ((RingedSpace.restrictComplex K (U x)).homology i).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent
        (StrictlyPerfect.structureSheafOfRings
          (X.toRingedSpace.restrict (U x).isOpenEmbedding))).prop_of_iso
        (@asIso _ _ _ _ (HomologicalComplex.homologyMap (α x) i) (hα x i hi))
        (isQuasicoherent_homology_of_isStrictlyPerfect (W x).toScheme (P x) (hP x) i)
    exact (SheafOfModules.isQuasicoherent ((W x).sheafRestrict.obj X.ringCatSheaf)).prop_of_iso
      (restrictComplexHomologyIsoRestrictFunctor X (U x) K i) hlocal
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (homologyIsoOfIso X K E e i) hKq

/-- Let `X` be a scheme and let `E` be an `m`-pseudo-coherent object of `D(𝒪_X)`. Then every point
of `X` has an open neighbourhood `U` on which `H^m(E)` is a quotient of a quasi-coherent
`𝒪_U`-module.

**Stacks erratum.** The source states this clause globally — that `H^m(E)` is a quotient of a
quasi-coherent module on all of `X` — and that is false; the corrected clause is the local one
stated here.

The counterexample is on `X = Spec k[x, y]`. With `L = V(x)`, `i : L → X` and
`Q = i_* i^{-1}𝒪_X` the pushforward of the *ordinary* inverse image of `𝒪_X`, the function
`g = x - y(y-1)` — the equation of the irreducible curve through `p0 = (0, 0)` and
`p1 = (0, 1)` — is invertible on `Q` over `U ∩ V`, where `U = X ∖ {p0}` and `V = X ∖ {p1}`.
Gluing `Q|_U` to `Q|_V` along `a = g b` gives an `𝒪_X`-module `F` that is locally cyclic, so
`F[0]` is `0`-pseudo-coherent, yet every global section of `F` vanishes in the fibre at `p1` by
the valuation along `g = 0`; as `X` is affine, no quasi-coherent module surjects onto `F`.
Quasi-compactness and quasi-separatedness would not have rescued the global form: `Spec k[x, y]`
has both. -/
public theorem exists_local_epi_homology_of_isPseudoCoherentFrom (X : Scheme.{u})
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace)]
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace)) (m : ℤ)
    (hE : RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace) E m) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ M : U.toScheme.Modules, M.IsQuasicoherent ∧
      ∃ f : M ⟶ (Scheme.Modules.restrictFunctor U.ι).obj
        ((DerivedCategory.homologyFunctor
          (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace) m).obj E), Epi f := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  obtain ⟨V, hxV, P, hP, α, _, hα⟩ := hK x
  let U : X.Opens := V
  let eU := restrictComplexHomologyIsoRestrictFunctor X U K m ≪≫
    (Scheme.Modules.restrictFunctor U.ι).mapIso (homologyIsoOfIso X K E e m)
  exact ⟨U, hxV, P.homology m, isQuasicoherent_homology_of_isStrictlyPerfect U.toScheme P hP m,
    HomologicalComplex.homologyMap α m ≫ eU.hom,
    epi_comp' hα (@IsIso.epi_of_iso _ _ _ _ eU.hom eU.isIso_hom)⟩

/-- A pseudo-coherent object of `D(𝒪_X)` on a scheme has quasi-coherent cohomology in every
degree, that is, it belongs to `D_QCoh(𝒪_X)`. -/
public theorem isQuasicoherentDerived_of_isPseudoCoherent (X : Scheme.{u})
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace)]
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent
        (StrictlyPerfect.structureSheafOfRings X.toRingedSpace)) E := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  change ∀ i : ℤ, ((DerivedCategory.homologyFunctor
    (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace) i).obj E).IsQuasicoherent
  exact fun i ↦ isQuasicoherent_homology_of_isPseudoCoherentFrom X E (i - 1) i
    ⟨K, hK (i - 1), ⟨e⟩⟩ (by lia)

/-- Let `X` be a scheme. If `E` is an `m`-pseudo-coherent object of `D(𝒪_X)`, then `H^i(E)` is a
quasi-coherent `𝒪_X`-module for `i > m`, and every point of `X` has an open neighbourhood `U` on
which `H^m(E)` is a quotient of a quasi-coherent `𝒪_U`-module. If `E` is pseudo-coherent, then `E`
is an object of `D_QCoh(𝒪_X)`.

The three clauses are `isQuasicoherent_homology_of_isPseudoCoherentFrom`,
`exists_local_epi_homology_of_isPseudoCoherentFrom` and
`isQuasicoherentDerived_of_isPseudoCoherent`.

**Stacks erratum.** The source states the degree-`m` clause globally, that `H^m(E)` is a quotient
of a quasi-coherent module on all of `X`; that is false (see the counterexample in the docstring
of `exists_local_epi_homology_of_isPseudoCoherentFrom`), and the corrected clause is the local
one stated here. -/
@[stacks 08E5]
public theorem isQuasicoherent_homology_of_isPseudoCoherent_scheme (X : Scheme.{u})
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace)] :
    (∀ (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace)) (m : ℤ),
      RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace) E m →
        (∀ i : ℤ, m < i → ((DerivedCategory.homologyFunctor
          (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace) i).obj E).IsQuasicoherent) ∧
        ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ M : U.toScheme.Modules, M.IsQuasicoherent ∧
          ∃ f : M ⟶ (Scheme.Modules.restrictFunctor U.ι).obj
            ((DerivedCategory.homologyFunctor
              (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace) m).obj E), Epi f) ∧
    ∀ E : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace),
      RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E →
        DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent
            (StrictlyPerfect.structureSheafOfRings X.toRingedSpace)) E :=
  ⟨fun E m hE ↦ ⟨fun i hi ↦ isQuasicoherent_homology_of_isPseudoCoherentFrom X E m i hE hi,
      exists_local_epi_homology_of_isPseudoCoherentFrom X E m hE⟩,
    fun E hE ↦ isQuasicoherentDerived_of_isPseudoCoherent X E hE⟩

end AlgebraicGeometry

end
