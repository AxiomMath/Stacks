module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsUniversalModel

/-!
# The universal finite projective model as data, and the single identification it comes from

Let `A` be a Noetherian ring, `f : X ⟶ Spec A` a proper morphism and `F` a coherent
`𝒪_X`-module flat over `A`. [Stacks, Tag 07VL] asserts that there is a finite complex `M` of
finite projective `A`-modules with

`Hⁱ(X_{A'}, F_{A'}) = Hⁱ(M ⊗_A A')`  functorially in `A'`.

`StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatGlobalSectionsUniversalModel.lean` states this
for each base change separately, and only as `Nonempty` of an isomorphism: the identification is
asserted to exist but is not available as a datum, so nothing can be said about how the
identifications for two different `A'` are related. This file removes that obstruction.

`UniversalModelData f F` is the model as **data**: the finite affine cover, the complex `M`, its
bounds, the finiteness and projectivity of its terms, and *one* isomorphism

`RΓ(X, F) ≅ Q M`  in  `D(A)`.

From such a datum the comparison for every base change is **determined**, not chosen:
`UniversalModelData.comparison` and `UniversalModelData.homologyComparison` are functions of the
datum, and `UniversalModelData.counit_comp_comparisonInv` says what they are — the base change
along `φ` of the single isomorphism `iso`, read through the base-change map of
[Stacks, Tag 07VK] (2). So all the identifications of the remark have one common origin over
`A`; they are not an unrelated choice per `A'`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.UniversalModelData`: the model as data.
* `…UniversalModelData.comparisonInv` and `…UniversalModelData.comparison`: the determined
  isomorphism `RΓ(X', g^* F) ≅ Q (M ⊗_A A')` in `D(A')`, for every ring map `φ : A ⟶ A'` and
  every cartesian square exhibiting `X'` as the base change of `X`.
* `…UniversalModelData.homologyComparison`: the degreewise identification
  `Hⁱ(X', g^* F) ≅ Hⁱ(M ⊗_A A')` of [Stacks, Tag 07VL], as a datum.
* `…extendScalarsComplexCompIso` and `…extendScalarsComplexComp`: termwise extension of scalars
  composes, `(M ⊗_{A} A') ⊗_{A'} A'' ≅ M ⊗_A A''`. This is what the right-hand side of the
  remark needs before a naturality square in `A'` can even be stated.

## Main results

* `…nonempty_universalModelData`: such a datum exists.
* `…UniversalModelData.counit_comp_comparisonInv`: the comparison is the base change along `φ`
  of the single identification over `A`.
* `…UniversalModelData.isIso_comparisonInv`: it is an isomorphism, by [Stacks, Tag 07VK] (2).
* `…UniversalModelData.exists_finiteProjectiveModel_homology_iso`: the statement of
  `ProperFlatGlobalSectionsUniversalModel.lean` is recovered from the datum, so nothing is lost
  by working with the datum instead.

## Functoriality in `A'`

`counit_comp_comparisonInv` says that the family of identifications has a single origin: each
one is the base change of `iso` along `φ`. The naturality squares for a second ring map
`ψ : A' ⟶ A''`, the functoriality in `A'` of [Stacks, Tag 07VL], are
`exists_finiteProjectiveModel_homology_iso_functorial` of
`StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatGlobalSectionsFunctorialModel.lean`, stated at
the level of a chain-level comparison with the alternating Čech complex, where the cocycle
identity of the Čech base-change isomorphism and `extendScalarsComplexComp` above make the square
commute.

## References

* [Stacks Project, Tag 07VL](https://stacks.math.columbia.edu/tag/07VL)
* [Stacks Project, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)
* [Stacks Project, Tag 06XY](https://stacks.math.columbia.edu/tag/06XY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.ProperFlatGlobalSections

attribute [local instance 10000] HasDerivedCategory.standard

section Composition

variable {A₁ A₂ A₃ : Type u} [CommRing A₁] [CommRing A₂] [CommRing A₃]
  (φ : A₁ →+* A₂) (ψ : A₂ →+* A₃)

/-- **Termwise extension of scalars composes**, as functors on complexes:
`(- ⊗_{A₁} A₂) ⊗_{A₂} A₃ ≅ - ⊗_{A₁} A₃`. It is `ModuleCat.extendScalarsComp` read on complexes
through `CategoryTheory.Functor.mapHomologicalComplexCompIso`.

This is the comparison the right-hand side `Hⁱ(M ⊗_A A')` of [Stacks, Tag 07VL] needs before a
naturality square in `A'` can be written down at all; see the module docstring for the two
further ingredients, which are missing. -/
def extendScalarsComplexCompIso :
    (ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (ModuleCat.extendScalars.{u, u, u} (ψ.comp φ)).mapHomologicalComplex
        (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp φ ψ).symm (ComplexShape.up ℤ)

/-- **`(M ⊗_{A₁} A₂) ⊗_{A₂} A₃ ≅ M ⊗_{A₁} A₃`**, the composition isomorphism of
`extendScalarsComplexCompIso` at a complex. -/
def extendScalarsComplexComp (M : CochainComplex (ModuleCat.{u} A₁) ℤ) :
    extendScalarsComplex ψ (extendScalarsComplex φ M) ≅ extendScalarsComplex (ψ.comp φ) M :=
  (extendScalarsComplexCompIso φ ψ).app M

end Composition

variable {A : Type u} [CommRing A] {X : Scheme.{u}}

/-- **A universal finite projective model of `RΓ(X, F)`, as data.** It carries the finite affine
open cover through which the base-change map of [Stacks, Tag 07VK] (2) is written, the bounded
complex `M` of finite projective `A`-modules of [Stacks, Tag 07VK] (1), and *one* isomorphism
`RΓ(X, F) ≅ Q M` in `D(A)`.

Everything [Stacks, Tag 07VL] asserts is a function of this datum: see
`UniversalModelData.comparison` and `UniversalModelData.homologyComparison`. -/
structure UniversalModelData (f : X ⟶ Spec (.of A)) (F : X.Modules) where
  /-- The index type of the finite affine open cover through which the base-change comparison is
  written. -/
  ι : Type u
  /-- The cover is finite. -/
  finite_ι : Finite ι
  /-- The index type is linearly ordered, as the alternating Čech complex requires. -/
  linearOrder_ι : LinearOrder ι
  /-- The members of the cover. -/
  cover : ι → X.Opens
  /-- They cover `X`. -/
  cover_top : (⊤ : X.Opens) = ⨆ i, cover i
  /-- Each member is affine. -/
  cover_isAffineOpen : ∀ i, IsAffineOpen (cover i)
  /-- Every finite intersection of members is affine. -/
  inter_isAffineOpen : ∀ (r : ℕ) (s : Fin (r + 1) → ι), IsAffineOpen (⨅ k, cover (s k))
  /-- The model: a complex of `A`-modules. -/
  cplx : CochainComplex (ModuleCat.{u} A) ℤ
  /-- A degree below which the model vanishes. -/
  lo : ℤ
  /-- A degree above which the model vanishes. -/
  hi : ℤ
  /-- The model vanishes below `lo`. -/
  isStrictlyGE : cplx.IsStrictlyGE lo
  /-- The model vanishes above `hi`. -/
  isStrictlyLE : cplx.IsStrictlyLE hi
  /-- The terms of the model are finite `A`-modules. -/
  finite_cplx : ∀ i : ℤ, Module.Finite A (cplx.X i)
  /-- The terms of the model are projective `A`-modules. -/
  projective_cplx : ∀ i : ℤ, Module.Projective A (cplx.X i)
  /-- **The single identification over `A`** from which every base-change comparison below is
  induced. -/
  iso : derivedGlobalSectionsOverBase f F ≅ DerivedCategory.Q.obj cplx

namespace UniversalModelData

variable {f : X ⟶ Spec (.of A)} {F : X.Modules}

attribute [local instance] UniversalModelData.finite_ι UniversalModelData.linearOrder_ι
  UniversalModelData.isStrictlyLE UniversalModelData.isStrictlyGE
  UniversalModelData.finite_cplx

/-- The terms of the model are flat, being projective. This is what makes the derived extension
of scalars of the model agree with the termwise one ([Stacks, Tag 06XY]). -/
local instance flat_cplx (D : UniversalModelData f F) (n : ℤ) : Module.Flat A (D.cplx.X n) :=
  have := D.projective_cplx n
  Module.Flat.of_projective

/-- A coherent module is quasi-coherent; seated as an instance so that the Čech comparisons
below elaborate without a local `have`. -/
local instance isQuasicoherent_of_isCoherent' (F : X.Modules) [F.IsCoherent] :
    F.IsQuasicoherent :=
  isQuasicoherent_of_isCoherent F

section BaseChange

variable (D : UniversalModelData f F) [IsProper f] [F.IsCoherent]
  {A' : Type u} [CommRing A'] (φ : A →+* A') {X' : Scheme.{u}}
  {f' : X' ⟶ Spec (.of A')} {g : X' ⟶ X}
  (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))

/-- **The comparison `Q (M ⊗_A A') ⟶ RΓ(X', g^* F)` determined by the datum**: the base change
along `φ` of the single isomorphism `D.iso`, read through the comparison of derived with
termwise extension of scalars ([Stacks, Tag 06XY], invertible because the terms of `M` are
projective hence flat) and the base-change map of [Stacks, Tag 07VK] (2). -/
def comparisonInv :
    DerivedCategory.Q.obj (extendScalarsComplex φ D.cplx) ⟶
      derivedGlobalSectionsOverBase f' ((Scheme.Modules.pullback g).obj F) :=
  (StacksDraft.PseudoCoherence.extendScalarsDerivedIsoOfFlat φ D.cplx D.hi).inv ≫
    (StacksDraft.PseudoCoherence.extendScalarsDerived φ).map D.iso.inv ≫
      derivedGlobalSectionsBaseChangeMap φ hsq F D.cover D.cover_top D.cover_isAffineOpen
      D.inter_isAffineOpen

/-- **The comparison is the base change of the single identification over `A`.** Precomposing
with the counit of derived extension of scalars — which is the [Stacks, Tag 06XY] comparison
`M ⊗^L_A A' ⟶ M ⊗_A A'`, an isomorphism here — turns `comparisonInv` into the base change of
`D.iso.inv` followed by the base-change map of [Stacks, Tag 07VK] (2). This is what makes the
family of identifications of [Stacks, Tag 07VL] one family and not a choice per `A'`. -/
theorem counit_comp_comparisonInv :
    (StacksDraft.PseudoCoherence.extendScalarsDerivedCounit φ).app D.cplx ≫
        D.comparisonInv φ hsq =
      (StacksDraft.PseudoCoherence.extendScalarsDerived φ).map D.iso.inv ≫
        derivedGlobalSectionsBaseChangeMap φ hsq F D.cover D.cover_top D.cover_isAffineOpen
          D.inter_isAffineOpen := by
  have h : (StacksDraft.PseudoCoherence.extendScalarsDerivedCounit φ).app D.cplx =
      (StacksDraft.PseudoCoherence.extendScalarsDerivedIsoOfFlat φ D.cplx D.hi).hom := rfl
  rw [comparisonInv, h, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- **The comparison is invertible.** Its three factors are: the [Stacks, Tag 06XY] comparison,
invertible on a bounded above termwise flat complex; the base change of the isomorphism `D.iso`;
and the base-change map of [Stacks, Tag 07VK] (2). -/
theorem isIso_comparisonInv (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    IsIso (D.comparisonInv φ hsq) :=
  have := isIso_derivedGlobalSectionsBaseChangeMap φ hsq F D.cover D.cover_top
    D.cover_isAffineOpen D.inter_isAffineOpen hflat
  by rw [comparisonInv]; infer_instance

/-- **The identification `RΓ(X', g^* F) ≅ Q (M ⊗_A A')` of [Stacks, Tag 07VK] (2) determined by
the datum**, for every ring map `φ : A ⟶ A'` and every cartesian square exhibiting `X'` as the
base change of `X` along `Spec A' ⟶ Spec A`. Unlike the `Nonempty` of
`exists_finiteProjectiveModel_derivedIso`, this is a function of the datum. -/
def comparison (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    derivedGlobalSectionsOverBase f' ((Scheme.Modules.pullback g).obj F) ≅
      DerivedCategory.Q.obj (extendScalarsComplex φ D.cplx) :=
  have := D.isIso_comparisonInv φ hsq hflat
  (asIso (D.comparisonInv φ hsq)).symm

/-- The inverse of `comparison` is `comparisonInv`. -/
@[simp]
theorem comparison_inv (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    (D.comparison φ hsq hflat).inv = D.comparisonInv φ hsq :=
  rfl

/-- **[Stacks, Tag 07VL], degreewise, as a datum.** The identification
`Hⁱ(X', g^* F) ≅ Hⁱ(M ⊗_A A')` for every base change and every degree, obtained from
`comparison` by applying the homology functor of `D(A')` and reading the homology of a complex
through `DerivedCategory.homologyFunctorFactors`. -/
def homologyComparison (hflat : IsFlatOver f.toLRSHom.toShHom F) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A') i).obj
        (derivedGlobalSectionsOverBase f' ((Scheme.Modules.pullback g).obj F)) ≅
      (extendScalarsComplex φ D.cplx).homology i :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A') i).mapIso (D.comparison φ hsq hflat) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A') i).app
      (extendScalarsComplex φ D.cplx)

end BaseChange

end UniversalModelData

/-- **The universal model exists.** Let `A` be a Noetherian ring, `f : X ⟶ Spec A` proper and `F`
a coherent `𝒪_X`-module flat over `A`. Then there is a datum `UniversalModelData f F`: a bounded
complex `M` of finite projective `A`-modules together with one isomorphism `RΓ(X, F) ≅ Q M` in
`D(A)`, from which the identification

`Hⁱ(X', g^* F) ≅ Hⁱ(M ⊗_A A')`

of the remark is *determined* for every ring map `φ : A ⟶ A'` and every cartesian square
exhibiting `X'` as the base change of `X` — it is
`UniversalModelData.homologyComparison`, and `UniversalModelData.counit_comp_comparisonInv`
identifies it as the base change of the single isomorphism along `φ`.

The complex and the isomorphism are [Stacks, Tag 07VK] (1); the cover is supplied by
`exists_finiteAffineCover_of_isProper`, so the datum needs no cover as input. -/
theorem nonempty_universalModelData (f : X ⟶ Spec (.of A)) (F : X.Modules)
    [IsNoetherianRing A] [IsProper f] [F.IsCoherent]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    Nonempty (UniversalModelData f F) := by
  classical
  obtain ⟨I, hI, hIlin, U, hU, hUaff, haff⟩ := exists_finiteAffineCover_of_isProper f
  obtain ⟨M, a, b, hGE, hLE, hfin, hproj, ⟨e⟩⟩ := isPerfect_derivedGlobalSections f F hflat
  exact ⟨{ ι := I
           finite_ι := Finite.of_fintype I
           linearOrder_ι := hIlin
           cover := U
           cover_top := hU
           cover_isAffineOpen := hUaff
           inter_isAffineOpen := haff
           cplx := M
           lo := a
           hi := b
           isStrictlyGE := hGE
           isStrictlyLE := hLE
           finite_cplx := hfin
           projective_cplx := hproj
           iso := e }⟩

namespace UniversalModelData

variable {f : X ⟶ Spec (.of A)} {F : X.Modules} (D : UniversalModelData f F)
  [IsProper f] [F.IsCoherent]

attribute [local instance] UniversalModelData.isStrictlyLE UniversalModelData.isStrictlyGE

/-- **The statement of `ProperFlatGlobalSectionsUniversalModel.lean` is recovered from the
datum**, so nothing is lost by working with the datum: the existential there is this datum with
its comparison isomorphisms forgotten down to `Nonempty`. -/
theorem exists_finiteProjectiveModel_homology_iso
    (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    ∃ (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ),
      M.IsStrictlyGE a ∧ M.IsStrictlyLE b ∧
        (∀ i : ℤ, Module.Finite A (M.X i)) ∧ (∀ i : ℤ, Module.Projective A (M.X i)) ∧
        ∀ {A' : Type u} [CommRing A'] (φ : A →+* A') {X' : Scheme.{u}}
          {f' : X' ⟶ Spec (.of A')} {g : X' ⟶ X}
          (_hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) (i : ℤ),
          Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') i).obj
              (derivedGlobalSectionsOverBase f' ((Scheme.Modules.pullback g).obj F)) ≅
            (extendScalarsComplex φ D.cplx).homology i) := by
  refine ⟨D.cplx, D.lo, D.hi, D.isStrictlyGE, D.isStrictlyLE, D.finite_cplx,
    D.projective_cplx, ?_⟩
  intro A' _ φ X' f' g hsq i
  exact ⟨D.homologyComparison φ hsq hflat i⟩

end UniversalModelData

end Stacks.AlgebraicGeometry.ProperFlatGlobalSections

end
