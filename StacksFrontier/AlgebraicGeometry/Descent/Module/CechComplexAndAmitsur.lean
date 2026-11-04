module

public import StacksFrontier.AlgebraicGeometry.Descent.Module.AmitsurAcyclic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.CoproductRefinement

/-!
# The Čech complex of a covering and the Amitsur complex `s((A/R)_• ⊗_R M)`

Let `R → A` be a map of commutative rings and let `M` be an `R`-module. The complex
`s((A/R)_• ⊗_R M)` of Stacks Section 023F is the alternating coface map complex of the
cosimplicial module `(A/R)_• ⊗_R M`, that is, the Amitsur cochain complex
`A ⊗_R M → A ⊗_R A ⊗_R M → ⋯` *without* the augmentation term `M`. The extended complex
`AlgebraicTopology.amitsurExtendedCochainComplex` is its augmentation by `M`, so the acyclicity of
the extended complex says exactly that `s((A/R)_• ⊗_R M)` is exact in every *positive* degree when
`R → A` is faithfully flat.

This file proves the two steps of Stacks 03FJ which do not depend on the geometry of a site of
schemes:

* the reduction of the Čech complex of a finite family `{U_i → U}` to the Čech complex of the
  one-element family `{∐ U_i → U}`, the abstract form of Stacks 03FI (3), as an isomorphism of
  complexes; and
* the passage from an isomorphism `Č^•(𝒰, ℱ) ≅ s((A/R)_• ⊗_R M)` to the vanishing
  `Ȟ^p(𝒰, ℱ) = 0` for `p ≥ 1`.

The identification of `Γ(V ×_U ⋯ ×_U V, ℱ^a)` with `A ⊗_R ⋯ ⊗_R A ⊗_R M`, compatibly with the
differentials, is taken as a hypothesis: either as an isomorphism of complexes or as an
isomorphism of cosimplicial objects for the one-element family.

## Main definitions

* `Stacks.Descent.amitsurCochainComplex` is `s((A/R)_• ⊗_R M)`.
* `Stacks.CechSite.cechComplexIsoCoproduct` is the isomorphism of complexes
  `Č^•({∐ U_i → U}, ℱ) ≅ Č^•({U_i → U}, ℱ)` of Stacks 03FI (3).
* `Stacks.CechSite.cechCosimplicialObject` is the cosimplicial object whose alternating coface
  map complex is the Čech complex.
* `Stacks.CechSite.cechComplexIsoOfCosimplicialIso` is the isomorphism of complexes induced by
  an isomorphism of cosimplicial objects.
* `Stacks.Descent.cechComplexIsoAmitsurOfSingleton` and
  `Stacks.Descent.cechComplexIsoAmitsurOfSingletonCosimplicial` are the isomorphisms of complexes
  `Č^•({U_i → U}, ℱ) ≅ s((A/R)_• ⊗_R M)` obtained from the corresponding isomorphism for the
  one-element family `{∐ U_i → U}`.

## Main results

* `Stacks.Descent.exactAt_amitsurCochainComplex_succ` and
  `Stacks.Descent.isZero_homology_amitsurCochainComplex_succ`: for `A` faithfully flat over
  `R`, the complex `s((A/R)_• ⊗_R M)` is exact in every positive degree.
* `Stacks.CechSite.isZero_cechCohomology_of_iso_of_exactAt`: Čech cohomology vanishes in the
  degrees where a complex isomorphic to the Čech complex is exact.
* `Stacks.Descent.isZero_cechCohomology_succ_of_singletonIso` and
  `Stacks.Descent.isZero_cechCohomology_succ_of_singletonCosimplicialIso`: `Ȟ^p(𝒰, ℱ) = 0` for
  `p ≥ 1`, from an identification of the Čech complex (respectively the Čech cosimplicial object)
  of `{∐ U_i → U}` with `s((A/R)_• ⊗_R M)` (respectively `(A/R)_• ⊗_R M`) for a faithfully flat
  `R → A`.
* `Stacks.Descent.isZero_cechCohomology_singleton_succ`: the same for a one-element family.

## Implementation notes

The Čech complex of a `PreZeroHypercover.{w}` is formed in a category with `w`-indexed products,
so the coefficient category of the statements combining the two sides is
`ModuleCat.{max u v w} R` for `R : Type u`, `A : Type v` and `M : Type w`, with the family indexed
in `Type (max u v w)`. The purely Čech-theoretic statements leave the coefficient category
arbitrary.

## References

* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 03FI](https://stacks.math.columbia.edu/tag/03FI)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe w v v' u u'

namespace Stacks.Descent

variable (R : Type u) (A : Type v) (M : Type w) [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M]

/-- The complex `s((A/R)_• ⊗_R M)` of Stacks Section 023F: the alternating coface map complex
of the cosimplicial module `(A/R)_• ⊗_R M`, indexed so that its degree-`p` term is
`(A/R)_p ⊗_R M`, i.e. the `(p + 1)`-fold tensor power of `A` over `R` tensored with `M`. -/
noncomputable def amitsurCochainComplex : CochainComplex (ModuleCat.{max u v w} R) ℕ :=
  (alternatingCofaceMapComplex (ModuleCat.{max u v w} R)).obj (amitsurAugmentation R A M).right

/-- **The complex `s((A/R)_• ⊗_R M)` is exact in every positive degree** when `A` is a
faithfully flat `R`-algebra. -/
theorem exactAt_amitsurCochainComplex_succ [Module.FaithfullyFlat R A] (p : ℕ) :
    (amitsurCochainComplex R A M).ExactAt (p + 1) := by
  have h := (HomologicalComplex.acyclic_iff _).1
    (amitsurExtendedCochainComplex_acyclic_of_faithfullyFlat R A M) (p + 2)
  rw [HomologicalComplex.exactAt_iff' _ (p + 1) (p + 2) (p + 3) (by simp) (by simp)] at h
  rwa [HomologicalComplex.exactAt_iff' _ p (p + 1) (p + 2) (by simp) (by simp)]

/-- **The cohomology of `s((A/R)_• ⊗_R M)` vanishes in positive degrees** when `A` is a
faithfully flat `R`-algebra. -/
theorem isZero_homology_amitsurCochainComplex_succ [Module.FaithfullyFlat R A] (p : ℕ) :
    IsZero ((amitsurCochainComplex R A M).homology (p + 1)) :=
  (exactAt_amitsurCochainComplex_succ R A M p).isZero_homology

end Stacks.Descent

namespace Stacks.CechSite

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C] [FinitaryExtensive C] {T : C}
  (E : PreZeroHypercover.{w} T) [Finite E.I₀]
  {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]
  (F : Cᵒᵖ ⥤ A) [PreservesFiniteProducts F]

/-- **Stacks 03FI (3) for a finitary extensive category, as an isomorphism of complexes.**
For a finite
family `{U_i → T}` in a finitary extensive category and a finite-product preserving presheaf
`ℱ`, the Čech complex of the one-element family `{∐ U_i → T}` is isomorphic to the Čech complex
of `{U_i → T}`, by the map of complexes of Stacks 03F4 attached to the refinement
`Stacks.CechSite.coproductRefinement`. -/
noncomputable def cechComplexIsoCoproduct :
    cechComplex (PreZeroHypercover.singleton.{w} (Sigma.desc E.f)) F ≅ cechComplex E F :=
  @asIso _ _ _ _ _ (isIso_cechComplexMap_of_preservesFiniteProducts E F)

end Stacks.CechSite

namespace Stacks.CechSite

section Cosimplicial

variable {C : Type u} [Category.{v} C] {T : C} (E : PreZeroHypercover.{w} T)
  {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  (F : Cᵒᵖ ⥤ A)

/-- The cosimplicial object whose alternating coface map complex is the Čech complex of a
family of morphisms with fixed target: in degree `p` it is the product, over all
`(p + 1)`-tuples `(i_0, …, i_p)` of indices, of the value of `ℱ` on
`U_{i_0} ×_T ⋯ ×_T U_{i_p}`. -/
noncomputable abbrev cechCosimplicialObject : CosimplicialObject A :=
  (Limits.FormalCoproduct.cosimplicialObjectFunctor (cechSimplicialObject E)).obj
    ((Over.forget T).op ⋙ F)

/-- The Čech complex is the alternating coface map complex of
`Stacks.CechSite.cechCosimplicialObject`. -/
theorem cechComplex_eq_alternatingCofaceMapComplex :
    cechComplex E F = (alternatingCofaceMapComplex A).obj (cechCosimplicialObject E F) :=
  rfl

/-- **A comparison of Čech complexes from a comparison of cosimplicial objects.** An
isomorphism of `Stacks.CechSite.cechCosimplicialObject` with a cosimplicial object `D`
induces an isomorphism of the Čech complex with the alternating coface map complex of `D`,
by functoriality of the alternating coface map complex. -/
noncomputable def cechComplexIsoOfCosimplicialIso {D : CosimplicialObject A}
    (η : cechCosimplicialObject E F ≅ D) :
    cechComplex E F ≅ (alternatingCofaceMapComplex A).obj D :=
  (alternatingCofaceMapComplex A).mapIso η

end Cosimplicial

variable {C : Type u} [Category.{v} C] {T : C} (E : PreZeroHypercover.{w} T)
  {A : Type u'} [Category.{v'} A] [Abelian A] [HasProducts.{w} A]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  (F : Cᵒᵖ ⥤ A)

/-- **Čech cohomology vanishes where an isomorphic complex is exact.** If the Čech complex of a
family with coefficients in `ℱ` is isomorphic to a complex which is exact in degree `n`, then
`Ȟ^n({U_i → T}, ℱ) = 0`. -/
theorem isZero_cechCohomology_of_iso_of_exactAt {K : CochainComplex A ℕ}
    (e : cechComplex E F ≅ K) {n : ℕ} (hK : K.ExactAt n) :
    IsZero (cechCohomology E F n) :=
  (hK.isZero_homology).of_iso ((HomologicalComplex.homologyFunctor A _ n).mapIso e)

end Stacks.CechSite

namespace Stacks.Descent

open Stacks.CechSite

variable {R : Type u} {A : Type v} {M : Type w} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M]
  {C : Type u'} [Category.{v'} C] [HasFiniteLimits C] [FinitaryExtensive C] {T : C}
  (E : PreZeroHypercover.{max u v w} T) [Finite E.I₀]
  (F : Cᵒᵖ ⥤ ModuleCat.{max u v w} R) [PreservesFiniteProducts F]

/-- **The isomorphism of complexes of Stacks 03FJ, given its one-element case.** If the Čech
complex of the one-element family `{∐ U_i → T}` with coefficients in `ℱ` is isomorphic to
`s((A/R)_• ⊗_R M)`, then so is the Čech complex of the family `{U_i → T}` itself; the two Čech
complexes agree by Stacks 03FI (3). -/
noncomputable def cechComplexIsoAmitsurOfSingleton
    (e : cechComplex (PreZeroHypercover.singleton.{max u v w} (Sigma.desc E.f)) F ≅
      amitsurCochainComplex R A M) :
    cechComplex E F ≅ amitsurCochainComplex R A M :=
  (cechComplexIsoCoproduct E F).symm ≪≫ e

/-- **The vanishing of the higher Čech cohomology of Stacks 03FJ, given the isomorphism of
complexes in its one-element case.** For `A` a faithfully flat `R`-algebra, an isomorphism of
the Čech complex of `{∐ U_i → T}` with `s((A/R)_• ⊗_R M)` forces
`Ȟ^p({U_i → T}, ℱ) = 0` for every `p ≥ 1`. -/
theorem isZero_cechCohomology_succ_of_singletonIso [Module.FaithfullyFlat R A]
    (e : cechComplex (PreZeroHypercover.singleton.{max u v w} (Sigma.desc E.f)) F ≅
      amitsurCochainComplex R A M) (p : ℕ) :
    IsZero (cechCohomology E F (p + 1)) :=
  isZero_cechCohomology_of_iso_of_exactAt E F (cechComplexIsoAmitsurOfSingleton E F e)
    (exactAt_amitsurCochainComplex_succ R A M p)

/-- **The isomorphism of complexes of Stacks 03FJ, from the degreewise identification of the
one-element case.** Given an isomorphism of *cosimplicial objects* between the Čech
cosimplicial object of `{∐ U_i → T}` with coefficients in `ℱ` and the cosimplicial module
`(A/R)_• ⊗_R M`, which is the degreewise identification `Γ(V ×_T ⋯ ×_T V, ℱ) ≅ A ⊗_R ⋯ ⊗_R A ⊗_R M`
together with its naturality in the simplex category, the Čech complex of `{U_i → T}` is
isomorphic to `s((A/R)_• ⊗_R M)`. -/
noncomputable def cechComplexIsoAmitsurOfSingletonCosimplicial
    (η : cechCosimplicialObject (PreZeroHypercover.singleton.{max u v w} (Sigma.desc E.f)) F ≅
      (amitsurAugmentation R A M).right) :
    cechComplex E F ≅ amitsurCochainComplex R A M :=
  cechComplexIsoAmitsurOfSingleton E F
    (cechComplexIsoOfCosimplicialIso (PreZeroHypercover.singleton.{max u v w} (Sigma.desc E.f))
      F η)

/-- **The vanishing of the higher Čech cohomology of Stacks 03FJ, from the degreewise
identification of the one-element case.** For `A` faithfully flat over
`R`, the degreewise identification of the Čech cosimplicial object of `{∐ U_i → T}` with
`(A/R)_• ⊗_R M` forces `Ȟ^p({U_i → T}, ℱ) = 0` for every `p ≥ 1`. -/
theorem isZero_cechCohomology_succ_of_singletonCosimplicialIso [Module.FaithfullyFlat R A]
    (η : cechCosimplicialObject (PreZeroHypercover.singleton.{max u v w} (Sigma.desc E.f)) F ≅
      (amitsurAugmentation R A M).right) (p : ℕ) :
    IsZero (cechCohomology E F (p + 1)) :=
  isZero_cechCohomology_of_iso_of_exactAt E F
    (cechComplexIsoAmitsurOfSingletonCosimplicial E F η)
    (exactAt_amitsurCochainComplex_succ R A M p)

end Stacks.Descent

namespace Stacks.Descent

open Stacks.CechSite

variable {R : Type u} {A : Type v} {M : Type w} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M]
  {C : Type u'} [Category.{v'} C] [HasFiniteLimits C] {T V : C} (h : V ⟶ T)
  (F : Cᵒᵖ ⥤ ModuleCat.{max u v w} R)

/-- **Stacks 03FJ for a one-element covering, given the degreewise identification.** For a
single morphism `V → T` and coefficients `ℱ` whose Čech cosimplicial object is identified with
`(A/R)_• ⊗_R M` for a faithfully flat `R → A`, the Čech complex of `{V → T}` is
`s((A/R)_• ⊗_R M)` and its cohomology vanishes in every positive degree. -/
theorem isZero_cechCohomology_singleton_succ [Module.FaithfullyFlat R A]
    (η : cechCosimplicialObject (PreZeroHypercover.singleton.{max u v w} h) F ≅
      (amitsurAugmentation R A M).right) (p : ℕ) :
    IsZero (cechCohomology (PreZeroHypercover.singleton.{max u v w} h) F (p + 1)) :=
  isZero_cechCohomology_of_iso_of_exactAt (PreZeroHypercover.singleton.{max u v w} h) F
    (cechComplexIsoOfCosimplicialIso (PreZeroHypercover.singleton.{max u v w} h) F η)
    (exactAt_amitsurCochainComplex_succ R A M p)

end Stacks.Descent

end
