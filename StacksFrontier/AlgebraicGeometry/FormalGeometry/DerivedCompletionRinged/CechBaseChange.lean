module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwayKFlat
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwayTensorNaturality
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CechContractible
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ExtendedCech
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ExtendedCechFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleLeftComplex

/-!
# Base change of the extended alternating Čech complex

Let `(𝒞, 𝒪)` be a ringed site, let `f_1, …, f_r` and `g` be global sections of `𝒪` and write
`Č(f)` for the extended alternating Čech complex of `f_1, …, f_r`. The proof of
[Stacks, Tag 099B] needs `𝒪_g ⊗^𝐋_𝒪 Č(f)` to vanish when `g` is a product `f_S` containing some
`f_j`, because `Č(f)` becomes the Čech complex of `f_1, …, f_r` over `𝒪_g`, in which `f_j` is a
unit. This file reduces that vanishing to a single statement about localizations, and proves
everything else it needs.

The reduction rests on a general fact, which the library already has: an additive
finite-product-preserving functor `G : 𝒜 ⥤ ℬ` commutes with the alternating Čech complex,

`G(Č(F)) ≅ Č(F ⋙ G)` for `F : Finset (Fin r) ⥤ 𝒜`,

which is `CategoryTheory.AlternatingCech.mapComplexIso` of `ExtendedCechFunctoriality.lean`,
built from the degreewise comparison `CategoryTheory.AlternatingCech.mapTermIso`. The terms
correspond because `G` preserves the finite product over
`CategoryTheory.AlternatingCech.Idx r p`, and the differentials correspond because the
alternating differential is a `ℤ`-linear combination of projections composed with transition
maps, all three of which `G` preserves. Nothing about localization, sheaves or tensor products
enters.

Applied to `G = 𝒪_g ⊗_𝒪 -` this says that `𝒪_g ⊗_𝒪 Č(f)` is the alternating complex of the
system `S ↦ 𝒪_g ⊗_𝒪 𝒪_{f_S}`; and since `𝒪_g` in degree zero is K-flat
(`AlgebraicGeometry.RingedSite.isKFlat_awayComplex`) the derived tensor product is that ordinary
one, so the vanishing in `D(𝒪)` follows from the contracting homotopy of
`CategoryTheory.AlternatingCech.homotopyIdZero`.

## Main definitions

* `AlgebraicGeometry.RingedSite.awayTensorCechIso`: **the complex-level base change**,
  `𝒪_g ⊗_𝒪 Č(f) ≅ Č(S ↦ 𝒪_g ⊗_𝒪 𝒪_{f_S})`.
* `AlgebraicGeometry.RingedSite.derivedTensorAwayCechIso`: `𝒪_g ⊗^𝐋_𝒪 Č(f)` is the class of
  that complex.

## Main results

* `AlgebraicGeometry.RingedSite.homotopyIdZero_awayTensorCech`: `𝒪_g ⊗_𝒪 Č(f)` is contractible.
* `AlgebraicGeometry.RingedSite.isZero_derivedTensor_awayComplex_extendedAlternatingCech`:
  **`𝒪_g ⊗^𝐋_𝒪 Č(f) = 0`**.
* `AlgebraicGeometry.RingedSite.isIso_awayTensorFunctor_map_awayModuleTransition`: tensoring
  with `𝒪_g` inverts the transition maps adjoining only `j`, when `f_j` is invertible in `𝒪_g`.
* `isZero_derivedTensor_awayComplex_extendedAlternatingCech_of_isUnit` and
  `isZero_derivedTensor_awayComplex_extendedAlternatingCech_prodGlobalSection`, both in the
  namespace `AlgebraicGeometry.RingedSite`: **the same vanishing with no hypothesis carried.**

## The base change of the terms, and why the vanishing is unconditional

Making the vanishing hold outright needs one input: `𝒪_g ⊗_𝒪 𝒪_h ≅ 𝒪_{g h}` **naturally in
`h`**. The isomorphism itself is `AlgebraicGeometry.RingedSite.awayTensorSheafIso` of
`AwayTensorSheaf.lean`; its naturality in the second section is
`AlgebraicGeometry.RingedSite.awayTensorSheafIso_naturality_right` of
`AwayTensorNaturality.lean`. With it the map `𝒪_g ⊗_𝒪 𝒪_{f_S} ⟶ 𝒪_g ⊗_𝒪 𝒪_{f_T}` *is* the
transition map `𝒪_{g f_S} ⟶ 𝒪_{g f_T}`, which is invertible as soon as `f_T / f_S` is already a
unit on `𝒪_{g f_S}` — and for `S ⊆ T ⊆ S ∪ {j}` that quotient is `1` or `f_j`, so it suffices
that `f_j` be invertible in `𝒪_g`. That is
`AlgebraicGeometry.RingedSite.isIso_awayTensorFunctor_map_awayModuleTransition`, and it
discharges `hiso`.

Two unconditional forms of the vanishing follow. The first,
`isZero_derivedTensor_awayComplex_extendedAlternatingCech_of_isUnit`, assumes only that `f_j`
becomes invertible in `𝒪_g`, which is a property of `g` and is exactly what the source uses.
The second, `isZero_derivedTensor_awayComplex_extendedAlternatingCech_prodGlobalSection`,
specialises it to `g = f_V` for a subset `V` containing `j` and assumes nothing: these are the
sections at which [Stacks, Tag 099B] needs the vanishing, since they are the ones indexing the
terms of the Čech complex.

The `hiso` forms are kept as engines, for an arbitrary `g` and an arbitrary index `j`; they are
unregistered lemmas and carry the hypothesis explicitly rather than as an instance argument.

### Why the ring-level route to the naturality does *not* work

One might hope to obtain naturality cheaply at the level of sheaves of **rings**, where
`AlgebraicGeometry.RingedSite.existsUnique_lift_toAwaySheaf` makes any two maps over `𝒪` out of a
localization equal. **That does not work**, for the following reasons:

* The uniqueness speaks about maps of sheaves of *rings* out of `awaySheaf h`. In this tree
  `𝒪_g ⊗_𝒪 𝒪_h` exists only as a sheaf of *modules* — `tensorSheafBifunctor`, built through
  sheafification — so it is not an object the uniqueness can be applied to at all.
* There is no tensor product of two `𝒪`-algebras as a sheaf of rings on a general site. The only
  construction is the generic coproduct in `Under 𝒪` (`Stacks.UnderCoproducts.coprodPt`,
  `StacksFrontier/AlgebraicGeometry/FiniteTypeSubalgebra/Coproducts.lean`), which needs
  `HasPushouts (Sheaf X.J CommRingCat)` and is never instantiated there.
* Even granting it, the route would be strictly worse: identifying the underlying module of such
  a pushout with the tensor product is precisely the comparison that
  `StacksFrontier/AlgebraicGeometry/FlatBaseChangeCohomology/AffineDegreeZero/AlgebraPushout.lean`
  leaves **unproved**, taking it as an `IsIso` hypothesis.

What *does* work, and is what `AwayTensorNaturality.lean` does, is to prove the naturality where
the comparison is built — on pure tensors at presheaf level, where uniqueness of `𝒪(U)`-algebra
maps out of a localization applies — and then push it along sheafification, whose compatibility
with tensor products is a natural isomorphism of bifunctors (Stacks 0GMW).

## References

* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 0662](https://stacks.math.columbia.edu/tag/0662)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RingedSite

universe u

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  {r : ℕ} (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (g : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- `𝒪_g`, as a complex of `𝒪`-modules concentrated in degree zero. This is the spelling
`AlgebraicGeometry.RingedSite.isKFlat_awayComplex` is stated at; it agrees with
`AlgebraicGeometry.RingedSite.awayComplex` of `AwayInternalHomMul.lean`, which is not imported
here. -/
abbrev awaySingleComplex :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  (CochainComplex.singleFunctor
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj (awayModule X g)

/-- Tensoring a sheaf of `𝒪`-modules with `𝒪_g`. -/
abbrev awayTensorFunctor :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj (awayModule X g)

/-- **Tensoring with `𝒪_g` commutes with the extended alternating Čech complex**: applying
`𝒪_g ⊗_𝒪 -` degreewise to `Č(f_1, …, f_r)` gives the alternating complex of the system
`S ↦ 𝒪_g ⊗_𝒪 𝒪_{f_S}`. This is the complex-level base change, and it is
`CategoryTheory.AlternatingCech.mapComplexIso` at the tensor functor: nothing about
localization enters, only that `𝒪_g ⊗_𝒪 -` is additive and preserves the finite products over
`CategoryTheory.AlternatingCech.Idx r p`. -/
def awayTensorCechIso :
    ((awayTensorFunctor X g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (extendedAlternatingCech X f) ≅
      AlternatingCech.complex (awayLocalizationFunctor X f ⋙ awayTensorFunctor X g) :=
  AlternatingCech.mapComplexIso _ _

section Discharge

omit [HasWeakSheafify X.J CommRingCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive] in
/-- For `S ⊆ T` the value of `f_S` divides that of `f_T` over every object. -/
theorem dvd_globalSectionVal_prodGlobalSection {S T : Finset (Fin r)} (hST : S ⊆ T)
    (U : X.Cᵒᵖ) :
    globalSectionVal (prodGlobalSection f S) U ∣
      globalSectionVal (prodGlobalSection f T) U := by
  rw [globalSectionVal_prodGlobalSection, globalSectionVal_prodGlobalSection]
  exact Finset.prod_dvd_prod_of_subset _ _ _ hST

/-- If the values of `h` divide those of `h'`, the canonical map `𝒪 ⟶ 𝒪_{h'}` factors through
`𝒪_h`. -/
private theorem exists_toAwaySheaf_comp_eq_of_dvd (Y : RingedSite.{u, u, u})
    [HasWeakSheafify Y.J CommRingCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {h h' : Presheaf.globalSections (Y.O.obj ⋙ forget CommRingCat.{u})}
    (hd : ∀ U : Y.Cᵒᵖ, globalSectionVal h U ∣ globalSectionVal h' U) :
    ∃ φ : awaySheaf h ⟶ awaySheaf h', toAwaySheaf h ≫ φ = toAwaySheaf h' := by
  obtain ⟨φ, hφ, -⟩ := existsUnique_lift_toAwaySheaf h (awaySheaf h') (toAwaySheaf h')
    fun U n => isUnit_toAwaySheaf_of_dvd Y U (hd U) n
  exact ⟨φ, hφ⟩

omit [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive] in
/-- The quotient `f_T / f_S` for `S ⊆ T ⊆ S ∪ {j}` becomes invertible in `𝒪_{g f_S}` when `f_j`
is already invertible in `𝒪_g`: it is `1` or `f_j`, and the canonical map `𝒪 ⟶ 𝒪_{g f_S}`
factors through `𝒪_g`. -/
theorem isUnit_toAwaySheaf_mulProdGlobalSection_sdiff (j : Fin r)
    (hj : ∀ (U : X.Cᵒᵖ) (n : ℕ),
      IsUnit (((toAwaySheaf g).hom.app U).hom (globalSectionVal (f j) U ^ n)))
    {S T : Finset (Fin r)} (hTS : T ⊆ insert j S) (U : X.Cᵒᵖ) (n : ℕ) :
    IsUnit (((toAwaySheaf (mulGlobalSection X g (prodGlobalSection f S))).hom.app U).hom
      ((∏ i ∈ T \ S, globalSectionVal (f i) U) ^ n)) := by
  obtain ⟨ψ, hψ⟩ := exists_toAwaySheaf_comp_eq_of_dvd X (h := g)
    (h' := mulGlobalSection X g (prodGlobalSection f S)) fun V => by
      rw [globalSectionVal_mulGlobalSection]; exact dvd_mul_right _ _
  have hTS' : T \ S ⊆ {j} := fun x hx ↦ by
    rcases Finset.mem_insert.mp (hTS (Finset.mem_sdiff.mp hx).1) with hc | hc
    · exact Finset.mem_singleton.mpr hc
    · exact absurd hc (Finset.mem_sdiff.mp hx).2
  rcases Finset.subset_singleton_iff.mp hTS' with hc | hc
  · rw [hc, Finset.prod_empty, one_pow, map_one]
    exact isUnit_one
  · rw [hc, Finset.prod_singleton]
    exact isUnit_toAwaySheaf_of_comp X ψ hψ U n (hj U n)

omit [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive] in
/-- Every power of `g f_T` becomes invertible in `𝒪_{g f_S}` for `S ⊆ T ⊆ S ∪ {j}` and `f_j`
invertible in `𝒪_g`. -/
theorem isUnit_toAwaySheaf_mulProdGlobalSection (j : Fin r)
    (hj : ∀ (U : X.Cᵒᵖ) (n : ℕ),
      IsUnit (((toAwaySheaf g).hom.app U).hom (globalSectionVal (f j) U ^ n)))
    {S T : Finset (Fin r)} (hST : S ⊆ T) (hTS : T ⊆ insert j S) (U : X.Cᵒᵖ) (n : ℕ) :
    IsUnit (((toAwaySheaf (mulGlobalSection X g (prodGlobalSection f S))).hom.app U).hom
      (globalSectionVal (mulGlobalSection X g (prodGlobalSection f T)) U ^ n)) := by
  have hsplit : globalSectionVal (mulGlobalSection X g (prodGlobalSection f T)) U ^ n =
      (∏ i ∈ T \ S, globalSectionVal (f i) U) ^ n *
        globalSectionVal (mulGlobalSection X g (prodGlobalSection f S)) U ^ n := by
    rw [globalSectionVal_mulGlobalSection, globalSectionVal_mulGlobalSection,
      globalSectionVal_prodGlobalSection, globalSectionVal_prodGlobalSection, ← mul_pow]
    refine congrArg (fun z => z ^ n) ?_
    rw [← Finset.prod_sdiff hST]
    ring
  rw [hsplit, map_mul]
  exact (isUnit_toAwaySheaf_mulProdGlobalSection_sdiff X f g j hj hTS U n).mul
    (isUnit_toAwaySheaf (mulGlobalSection X g (prodGlobalSection f S)) U n)

omit [HasSheafify X.J AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive] in
/-- **Tensoring with `𝒪_g` inverts the transition maps that adjoin only the index `j`**, as soon
as `f_j` is invertible in `𝒪_g`. This is the hypothesis `hiso` below, discharged: by
`AlgebraicGeometry.RingedSite.awayTensorSheafIso_naturality_right` the transported map is the
transition map `𝒪_{g f_S} ⟶ 𝒪_{g f_T}`, which is invertible because `f_T / f_S` is already a
unit there. -/
theorem isIso_awayTensorFunctor_map_awayModuleTransition (j : Fin r)
    (hj : ∀ (U : X.Cᵒᵖ) (n : ℕ),
      IsUnit (((toAwaySheaf g).hom.app U).hom (globalSectionVal (f j) U ^ n)))
    {S T : Finset (Fin r)} (hST : S ⊆ T) (hTS : T ⊆ insert j S) :
    IsIso ((awayTensorFunctor X g).map (awayModuleTransition X f hST)) := by
  have hd := dvd_globalSectionVal_prodGlobalSection X f hST
  have hdM := fun U => dvd_globalSectionVal_mulGlobalSection X g U (hd U)
  obtain ⟨φM, hφM⟩ := exists_toAwaySheaf_comp_eq_of_dvd X hdM
  have hσ : IsIso (awayModuleMapOfComp X φM hφM) :=
    isIso_awayModuleMapOfComp X φM hφM
      (isUnit_toAwaySheaf_mulProdGlobalSection X f g j hj hST hTS)
  rw [awayModuleTransition_eq_awayModuleMapOfComp]
  exact isIso_sheafTensor_map_awayModuleMapOfComp X g
    (fun U n => isUnit_toAwayPresheaf_of_dvd X U (hd U) n)
    (fun U n => isUnit_toAwayPresheaf_of_dvd X U (hdM U) n) hd
    (toAwaySheaf_comp_awayTransition f hST) hφM hσ

end Discharge

section Contractible

variable (j : Fin r)
  (hiso : ∀ {S T : Finset (Fin r)} (hST : S ⊆ T), T ⊆ insert j S →
    IsIso ((awayTensorFunctor X g).map (awayModuleTransition X f hST)))

include hiso

/-- **`𝒪_g ⊗_𝒪 Č(f)` is contractible** when tensoring with `𝒪_g` inverts every transition map
adjoining only the index `j`. The hypothesis is what the source gets from `f_j` becoming a unit
after inverting `g`; it is stated here as an input because the identification
`𝒪_g ⊗_𝒪 𝒪_{f_S} = 𝒪_{g f_S}` is not available naturally in `S` — see the implementation
notes. -/
def homotopyIdZero_awayTensorCech :
    Homotopy (𝟙 (AlternatingCech.complex
      (awayLocalizationFunctor X f ⋙ awayTensorFunctor X g))) 0 :=
  AlternatingCech.homotopyIdZero _ j hiso

end Contractible

section Derived

attribute [local instance] HasDerivedCategory.standard

variable [∀ (K₁ K₂ : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
  HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
    (ComplexShape.up ℤ)]

/-- **`𝒪_g ⊗^𝐋_𝒪 Č(f)` is the class of `𝒪_g ⊗_𝒪 -` applied degreewise to `Č(f)`.** The derived
tensor product is the ordinary one because `𝒪_g` in degree zero is K-flat
(`AlgebraicGeometry.RingedSite.isKFlat_awayComplex`), and the total tensor complex of a complex
concentrated in degree zero with `Č(f)` is the degreewise tensor
(`HomologicalComplex.mapBifunctorSingleLeftIso`). -/
def derivedTensorAwayCechIso :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (DerivedCategory.Q.obj (awaySingleComplex X g))).obj
        (DerivedCategory.Q.obj (extendedAlternatingCech X f)) ≅
      DerivedCategory.Q.obj (AlternatingCech.complex
        (awayLocalizationFunctor X f ⋙ awayTensorFunctor X g)) :=
  (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft
      (awaySingleComplex X g) (extendedAlternatingCech X f) (isKFlat_awayComplex X g) ≪≫
    DerivedCategory.Q.mapIso (HomologicalComplex.mapBifunctorSingleLeftIso
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (awayModule X g)
        (extendedAlternatingCech X f)) ≪≫
      DerivedCategory.Q.mapIso (awayTensorCechIso X f g)

/-- **`𝒪_g ⊗^𝐋_𝒪 Č(f) = 0`** when tensoring with `𝒪_g` inverts every transition map adjoining
only the index `j`. This is the vanishing that the derived completeness of `K^∧` and the
invertibility of `Φ η_K` both reduce to, through the tensor–internal-Hom adjunction of
[Stacks, Tag 08J9]. -/
theorem isZero_derivedTensor_awayComplex_extendedAlternatingCech (j : Fin r)
    (hiso : ∀ {S T : Finset (Fin r)} (hST : S ⊆ T), T ⊆ insert j S →
      IsIso ((awayTensorFunctor X g).map (awayModuleTransition X f hST))) :
    IsZero (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
      (DerivedCategory.Q.obj (awaySingleComplex X g))).obj
      (DerivedCategory.Q.obj (extendedAlternatingCech X f))) :=
  IsZero.of_iso
    (AlternatingCech.isZero_Q_obj_of_homotopy_id_zero _
      (homotopyIdZero_awayTensorCech X f g j hiso))
    (derivedTensorAwayCechIso X f g)

/-- **`𝒪_g ⊗^𝐋_𝒪 Č(f) = 0` whenever `f_j` becomes invertible in `𝒪_g`.** The hypothesis `hiso`
of the previous statement is discharged by
`AlgebraicGeometry.RingedSite.isIso_awayTensorFunctor_map_awayModuleTransition`, so nothing is
assumed here beyond what [Stacks, Tag 099B] uses: that the section one inverts is divisible by
one of the `f_i`. -/
theorem isZero_derivedTensor_awayComplex_extendedAlternatingCech_of_isUnit (j : Fin r)
    (hj : ∀ (U : X.Cᵒᵖ) (n : ℕ),
      IsUnit (((toAwaySheaf g).hom.app U).hom (globalSectionVal (f j) U ^ n))) :
    IsZero (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
      (DerivedCategory.Q.obj (awaySingleComplex X g))).obj
      (DerivedCategory.Q.obj (extendedAlternatingCech X f))) :=
  isZero_derivedTensor_awayComplex_extendedAlternatingCech X f g j
    fun hST hTS => isIso_awayTensorFunctor_map_awayModuleTransition X f g j hj hST hTS

/-- **`𝒪_{f_V} ⊗^𝐋_𝒪 Č(f) = 0` for every subset `V` containing some index `j`.** This is the
vanishing in the form the proof of [Stacks, Tag 099B] uses it, with no hypothesis at all: the
terms of the Čech complex are the `𝒪_{f_S}`, and tensoring the complex with any one of them
kills it. -/
theorem isZero_derivedTensor_awayComplex_extendedAlternatingCech_prodGlobalSection
    (V : Finset (Fin r)) (j : Fin r) (hjV : j ∈ V) :
    IsZero (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
      (DerivedCategory.Q.obj (awaySingleComplex X (prodGlobalSection f V)))).obj
      (DerivedCategory.Q.obj (extendedAlternatingCech X f))) :=
  isZero_derivedTensor_awayComplex_extendedAlternatingCech_of_isUnit X f
    (prodGlobalSection f V) j fun U n => by
      rw [← prodGlobalSection_singleton X f j]
      exact isUnit_toAwaySheaf_prodGlobalSection_of_subset f
        (Finset.singleton_subset_iff.mpr hjV) U n

end Derived

end AlgebraicGeometry.RingedSite

end
