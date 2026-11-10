module

public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Comparison
public import StacksFrontier.AlgebraicGeometry.Perfect.Approximation.OpenSubscheme
public import StacksFrontier.Topology.Sheaves.Cohomology.TransportAlongAnIsomorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineTilde
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.ExtensionByZeroBaseChange

/-!
# Approximation by perfect complexes on an affine scheme

[Stacks, Tag 08EQ] is stated for an affine scheme, and
`StacksFrontier/AlgebraicGeometry/Perfect/PerfectApproximation/Affine.lean` proves its second
assertion, and its first for a closed subset cut out by `r` equations, for `Spec R`. This file
carries these statements to an arbitrary affine scheme along `X ≅ Spec Γ(X, 𝒪_X)`.

## Main results

* `AlgebraicGeometry.PerfectApproximation.approximationHolds_derivedPullback`: approximation
  for a triple is carried along an isomorphism of schemes by derived pullback.
* `AlgebraicGeometry.PerfectApproximation.approximationByPerfectComplexes_of_iso`: so is
  approximation by perfect complexes.
* `AlgebraicGeometry.PerfectApproximation.approximationByPerfectComplexes_of_isAffine` and
  `AlgebraicGeometry.PerfectApproximation.hasApproximationByPerfectComplexes_of_isAffine`:
  the second assertion of Tag 08EQ, for an arbitrary affine scheme.
* `AlgebraicGeometry.PerfectApproximation.approximationHolds_of_zeroLocus_of_isAffine`:
  approximation for a triple on an arbitrary affine scheme, with the closed subset presented as
  the zero locus of `r` global functions. The first assertion of Tag 08EQ, for a closed subset
  whose complement is a union of `r` affine opens, is
  `AlgebraicGeometry.PerfectApproximation.approximationHolds_of_affineCover` in
  `StacksFrontier/AlgebraicGeometry/Perfect/PerfectApproximation/AffineCover.lean`.

## Implementation notes

Everything is read at `CategoryTheory.HasDerivedCategory.standard`, selected at raised
priority as in `StacksFrontier/AlgebraicGeometry/Perfect/PerfectApproximation/Affine.lean`, and
the derived pullback used is therefore the ringed-space one,
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback`, applied to the underlying
morphism of ringed spaces. `Stacks.Duality.derivedPullback` is the same functor for schemes but
is pinned at the locally small model, where none of the statements of Tag 08EQ live; the
crossing between the scheme spelling `X.Modules` and the ringed-space spelling of the category
happens in term position, where it is `rfl`. For the same reason
`AlgebraicGeometry.PerfectApproximation.homologyDerivedPullbackIsoOfExact` below is not a
duplicate of `Stacks.Duality.homologyDerivedPullbackIso`: it is the same identification at the
ringed-space spelling and at a free model, which is the only form that reaches the model these
statements live at.

Along an isomorphism every input transports:

* perfectness by `Stacks.Cohomology.TransportAlongIso.isPerfect_derivedPullback_scheme_iff`;
* `m`-pseudo-coherence by
  `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPseudoCoherentFrom_derivedPullback`,
  which needs no hypothesis on the morphism;
* quasi-coherence of the cohomology by
  `Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel`, which is the one form of
  [Stacks, Tag 08DW] part (1) stated at a free model binder;
* the support condition, degree by degree, by
  `AlgebraicGeometry.PerfectApproximation.isZero_stalk_homology_derivedPullback` below. The
  support hypothesis of [Stacks, Tag 08EN] is restricted to the degrees `≥ m - r`, so the
  all-degrees statement
  `Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_derivedPullback` cannot be
  used for it; the degreewise form is read off the stalk formula of [Stacks, Tag 0098] through
  the identification of the cohomology of a derived pullback along an exact pullback with the
  pullback of the cohomology.

The map `α` of the approximation is carried by functoriality, and that it remains an
isomorphism on cohomology above `m` and an epimorphism in degree `m` is
`CategoryTheory.Functor.isIso_homologyFunctor_map_mapDerivedCategory_map` and its companion
for epimorphisms, transported along
`AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso`: pullback along an isomorphism is an
equivalence, hence exact, so the derived pullback is degreewise pullback.

## References

* [Stacks Project, Tag 08EQ](https://stacks.math.columbia.edu/tag/08EQ)
* [Stacks Project, Tag 08EM](https://stacks.math.columbia.edu/tag/08EM)
* [Stacks Project, Tag 08EN](https://stacks.math.columbia.edu/tag/08EN)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.TransportAlongIso (ringedSpaceIsoOfSchemeIso)

namespace AlgebraicGeometry.PerfectApproximation

universe u

attribute [local instance 10000] HasDerivedCategory.standard

section Transport

variable {X Y : RingedSpace.{u, u}} (g : X ⟶ Y)
  [PreservesFiniteLimits (modulePullback g)]

/-- **The cohomology of a derived pullback along an exact pullback is the pullback of the
cohomology.** There the derived pullback is degreewise pullback,
`AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso`, and the identification is
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`. -/
def homologyDerivedPullbackIsoOfExact
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (i : ℤ) :
    (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) i).obj
        ((derivedPullback g).obj E) ≅
      (modulePullback g).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) i).obj E) :=
  letI := preservesFiniteColimits_modulePullback g
  (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) i).mapIso
      ((AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso g).app E) ≪≫
    ((modulePullback g).mapDerivedCategoryHomologyIso i).app E

/-- **The support condition transports, degree by degree.** If the stalk of `H^i(E)` vanishes
at `g x` then the stalk of `H^i(Lg^*E)` vanishes at `x`: the stalk of a pullback at `x` is the
base change of the stalk at `g x`, [Stacks, Tag 0098]. -/
theorem isZero_stalk_homology_derivedPullback
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (i : ℤ) (x : X.carrier)
    (hE : IsZero (TopCat.Presheaf.stalk
      (((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) i).obj
        E).val.presheaf) (g.hom.base x))) :
    IsZero (TopCat.Presheaf.stalk
      (((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) i).obj
        ((derivedPullback g).obj E)).val.presheaf) x) := by
  have h₁ : IsZero ((SheafOfModules.stalkFunctor (structureSheafRing X) x).obj
      ((modulePullback g).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) i).obj E))) :=
    (AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff (structureSheafRing X) x _).2
      (Stacks.Cohomology.ExtensionByZeroBaseChange.isZero_stalk_modulePullback_obj g _ x hE)
  exact (AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff (structureSheafRing X) x _).1
    (h₁.of_iso ((SheafOfModules.stalkFunctor (structureSheafRing X) x).mapIso
      (homologyDerivedPullbackIsoOfExact g E i)))

/-- The derived pullback of a morphism, written through the degreewise pullback it is. -/
private theorem map_derivedPullback_eq
    {P E : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))} (α : P ⟶ E) :
    letI := preservesFiniteColimits_modulePullback g
    (derivedPullback g).map α =
      (AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso g).hom.app P ≫
        (modulePullback g).mapDerivedCategory.map α ≫
          (AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso g).inv.app E := by
  let := preservesFiniteColimits_modulePullback g
  rw [← Category.assoc,
    ← (AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso g).hom.naturality α, Category.assoc,
    Iso.hom_inv_id_app, Category.comp_id]

/-- **A cohomology isomorphism stays one after an exact derived pullback.** -/
theorem isIso_homology_map_derivedPullback
    {P E : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))} (α : P ⟶ E) (i : ℤ)
    (h : IsIso
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) i).map α)) :
    IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) i).map
      ((derivedPullback g).map α)) := by
  let := preservesFiniteColimits_modulePullback g
  rw [map_derivedPullback_eq g α, Functor.map_comp, Functor.map_comp]
  have := Functor.isIso_homologyFunctor_map_mapDerivedCategory_map (modulePullback g) α i h
  infer_instance

/-- **A cohomology epimorphism stays one after an exact derived pullback.** -/
theorem epi_homology_map_derivedPullback
    {P E : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))} (α : P ⟶ E) (i : ℤ)
    (h : Epi
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) i).map α)) :
    Epi ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) i).map
      ((derivedPullback g).map α)) := by
  let := preservesFiniteColimits_modulePullback g
  rw [map_derivedPullback_eq g α, Functor.map_comp, Functor.map_comp]
  have := Functor.epi_homologyFunctor_map_mapDerivedCategory_map (modulePullback g) α i h
  infer_instance

end Transport

/-- Degreewise pullback along an isomorphism of schemes is exact: it is an equivalence. -/
theorem preservesFiniteLimits_modulePullback_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] : PreservesFiniteLimits (modulePullback f.toLRSHom.toShHom) :=
  inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.pullback f))

/-- Approximation for a triple only depends on the isomorphism class of the object. -/
theorem ApproximationHolds.of_iso {X : Scheme.{u}} {T : Set X}
    {E E' : DerivedCategory.{u + 1} X.Modules} {m : ℤ}
    (h : ApproximationHolds X T E m) (θ : E ≅ E') : ApproximationHolds X T E' m := by
  obtain ⟨P, hP, hsupp, α, hiso, hepi⟩ := h
  refine ⟨P, hP, hsupp, α ≫ θ.hom, fun i hi => ?_, ?_⟩
  · rw [Functor.map_comp]
    have := hiso i hi
    infer_instance
  · rw [Functor.map_comp]
    have := hepi
    infer_instance

/-- **Approximation for a triple is carried along an isomorphism of schemes.** -/
theorem approximationHolds_derivedPullback {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (T : Set Y) (E : DerivedCategory.{u + 1} Y.Modules) (m : ℤ)
    (h : ApproximationHolds Y T E m) :
    ApproximationHolds X (f.base ⁻¹' T) ((derivedPullback f.toLRSHom.toShHom).obj E) m := by
  let := preservesFiniteLimits_modulePullback_of_isIso f
  obtain ⟨P, hP, hsupp, α, hiso, hepi⟩ := h
  refine ⟨(derivedPullback f.toLRSHom.toShHom).obj P, ?_, ?_,
    (derivedPullback f.toLRSHom.toShHom).map α, fun i hi => ?_, ?_⟩
  · exact (Stacks.Cohomology.TransportAlongIso.isPerfect_derivedPullback_scheme_iff
      (asIso f) P).2 hP
  · exact fun i x hx =>
      isZero_stalk_homology_derivedPullback f.toLRSHom.toShHom P i x (hsupp i _ hx)
  · exact isIso_homology_map_derivedPullback f.toLRSHom.toShHom α i (hiso i hi)
  · exact epi_homology_map_derivedPullback f.toLRSHom.toShHom α m hepi

/-- Approximation on `Y` for the pullback along `e.inv` gives approximation on `X` for a set whose
image under `e.hom` is the given one. -/
private theorem approximationHolds_of_iso_derivedPullback {X Y : Scheme.{u}} (e : X ≅ Y)
    {T : Set X} {Z : Set Y} (hZ : e.hom.base ⁻¹' Z = T)
    {E : DerivedCategory.{u + 1} X.Modules} {m : ℤ}
    (h : ApproximationHolds Y Z ((derivedPullback e.inv.toLRSHom.toShHom).obj E) m) :
    ApproximationHolds X T E m := by
  let := preservesFiniteLimits_modulePullback_of_isIso e.inv
  rw [← hZ]
  exact (approximationHolds_derivedPullback e.hom Z _ m h).of_iso
    ((Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackInvHomIso
      (ringedSpaceIsoOfSchemeIso e)).app E)

/-- **Approximation by perfect complexes is carried along an isomorphism of schemes.** -/
theorem approximationByPerfectComplexes_of_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (h : ApproximationByPerfectComplexes Y) : ApproximationByPerfectComplexes X := by
  intro T hT hTc
  have hclosed : IsClosed (e.inv.base ⁻¹' T) :=
    hT.preimage (Scheme.homeoOfIso e).symm.continuous
  have hretro : IsRetrocompact ((e.inv.base ⁻¹' T)ᶜ : Set Y) := by
    rw [← Set.preimage_compl]
    exact IsRetrocompact.preimage_of_isOpenEmbedding
      (Scheme.homeoOfIso e).symm.isOpenEmbedding hTc
  obtain ⟨r, hr⟩ := h (e.inv.base ⁻¹' T) hclosed hretro
  let := preservesFiniteLimits_modulePullback_of_isIso e.inv
  refine ⟨r, fun E m hqc hpc hsupp => ?_⟩
  set E' := (derivedPullback e.inv.toLRSHom.toShHom).obj E with hE'
  have hbase : ∀ x : X, e.inv.base (e.hom.base x) = x := fun x => by
    simp
  have happ : ApproximationHolds Y (e.inv.base ⁻¹' T) E' m := by
    refine hr E' m (fun i => ?_) ?_ (fun i y hi hy => ?_)
    · exact Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel e.inv E hqc i
    · exact AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPseudoCoherentFrom_derivedPullback
        e.inv.toLRSHom.toShHom E (m - r) hpc
    · exact isZero_stalk_homology_derivedPullback e.inv.toLRSHom.toShHom E i y
        (hsupp i _ hi hy)
  refine approximationHolds_of_iso_derivedPullback e ?_ happ
  ext x
  simp [Set.mem_preimage, hbase x]

/-- **Approximation by perfect complexes holds on an affine scheme.** This is the second
assertion of [Stacks, Tag 08EQ]: the case of `Spec R`,
`AlgebraicGeometry.PerfectApproximation.approximationByPerfectComplexes_spec`, transported
along `AlgebraicGeometry.Scheme.isoSpec`. -/
@[stacks 08EQ "second assertion: approximation by perfect complexes on an affine scheme"]
theorem approximationByPerfectComplexes_of_isAffine (X : Scheme.{u}) [IsAffine X] :
    ApproximationByPerfectComplexes X :=
  approximationByPerfectComplexes_of_iso X.isoSpec
    (approximationByPerfectComplexes_spec Γ(X, ⊤))

/-- **Approximation by perfect complexes holds on an affine scheme**, in the encoding of
`AlgebraicGeometry.HasApproximationByPerfectComplexes`. -/
@[stacks 08EQ "second assertion: approximation by perfect complexes on an affine scheme"]
theorem hasApproximationByPerfectComplexes_of_isAffine (X : Scheme.{u}) [IsAffine X] :
    HasApproximationByPerfectComplexes X :=
  (approximationByPerfectComplexes_iff X).1 (approximationByPerfectComplexes_of_isAffine X)

/-- **Approximation on an affine scheme for a closed subset cut out by `r` equations.** Let `X` be
an affine scheme, let `f₁, …, f_r ∈ Γ(X, 𝒪_X)` and let `T` be their common zero locus, so that
`X ∖ T` is the union of the `r` basic opens they define. Approximation holds for every triple
`(T, E, m)` with `E` of quasi-coherent cohomology such that `E` is `m`-pseudo-coherent and the
cohomology of `E` is supported on `T` in all degrees `≥ m - r + 1`. -/
theorem approximationHolds_of_zeroLocus_of_isAffine (X : Scheme.{u}) [IsAffine X] {r : ℕ}
    (f : Fin r → Γ(X, ⊤)) (E : DerivedCategory.{u + 1} X.Modules) (m : ℤ)
    (hqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (hpc : RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace) E m)
    (hsupp : ∀ i : ℤ, m - (r : ℤ) + 1 ≤ i → ∀ x : X,
      X.isoSpec.hom.base x ∉ PrimeSpectrum.zeroLocus (Set.range f) →
      IsZero (TopCat.Presheaf.stalk (X := X)
        (((DerivedCategory.homologyFunctor X.Modules i).obj E).val.presheaf) x)) :
    ApproximationHolds X
      (X.isoSpec.hom.base ⁻¹' PrimeSpectrum.zeroLocus (Set.range f)) E m := by
  set e := X.isoSpec with he
  let := preservesFiniteLimits_modulePullback_of_isIso e.inv
  set E' := (derivedPullback e.inv.toLRSHom.toShHom).obj E with hE'
  have hbase : ∀ y : Spec Γ(X, ⊤), e.hom.base (e.inv.base y) = y := fun y => by
    simp
  have happ : ApproximationHolds (Spec Γ(X, ⊤))
      (PrimeSpectrum.zeroLocus (Set.range f)) E' m := by
    refine approximationHolds_of_zeroLocus Γ(X, ⊤) f E' m (fun i => ?_) ?_ (fun i hi y hy => ?_)
    · exact Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel e.inv E hqc i
    · exact AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPseudoCoherentFrom_derivedPullback
        e.inv.toLRSHom.toShHom E m hpc
    · refine isZero_stalk_homology_derivedPullback e.inv.toLRSHom.toShHom E i y
        (hsupp i hi _ ?_)
      change e.hom.base (e.inv.base y) ∉ PrimeSpectrum.zeroLocus (Set.range f)
      rw [hbase y]
      exact hy
  exact approximationHolds_of_iso_derivedPullback e rfl happ

end AlgebraicGeometry.PerfectApproximation

end
