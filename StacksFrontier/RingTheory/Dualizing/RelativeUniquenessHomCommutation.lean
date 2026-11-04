module

public import StacksFrontier.RingTheory.Dualizing.RelativeProjectionFormula
public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality

/-!
# Step 1 of the duality route: the diagonal functor against derived Hom

Let `R → A` be flat, put `B = A ⊗[R] A`, write `p₁ : A → B` for the left coprojection and
`Δ : B → A` for the multiplication map.  The module documentation of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality` describes a route to [stacks 0E2D]
whose first step concerns the functor

`T(X) = Δ^!(p₁^*X) = RHom_B(A_B, p₁^*X)`

of the defining condition of [stacks 0E2C], and asks for `T(RHom_A(M, N)) ≅ RHom_A(M, T(N))`
for `M` pseudo-coherent and `N` bounded below.  It names four ingredients: flat base change for
derived Hom [stacks 0A6A], the currying isomorphism [stacks 0A65], the unrestricted projection
formula at the diagonal, and the adjunction `Δ_* ⊣ Δ^!` of [stacks 0A70].

This file composes those ingredients as far as they go.

## The shape of what is proved

Derived restriction of scalars along `p₁` undoes derived restriction along `Δ`, because `p₁` is
a section of `Δ`: that is `Dualizing.derivedRestrictScalarsSectionIso`.  Composed with the
identification of internal derived Hom out of the diagonal with restricted derived coextension
(`Dualizing.nonempty_modelHomIsoRestrictScalarsDerivedHom`), it rewrites `Δ^!` entirely inside
`D(B)`:

`Δ^!(Z) ≅ p₁_* RHom_B(A_B, Z)`,  hence  `T(X) ≅ p₁_* RHom_B(A_B, p₁^*X)`.

In that form the currying isomorphism moves `A_B` across and the projection formula replaces
`A_B ⊗ᴸ_B p₁^*M` by `Δ_*M`, which is
`Dualizing.nonempty_derivedHom_modelHom_iso_restrictScalars_modelHom`:

`Δ^!(RHom_B(p₁^*M, Y)) ≅ p₁_* RHom_B(Δ_*M, Y)`,

with no hypothesis on `M` or `Y` at all — three of the four ingredients, composed.  The fourth,
flat base change, is proved separately in the route's vocabulary as
`Dualizing.nonempty_diagonalDerivedExtension_derivedHom_iso`:

`p₁^* RHom_A(M, N) ≅ RHom_B(p₁^*M, p₁^*N)`   for `M` pseudo-coherent and `N` bounded below,

and `Dualizing.nonempty_relativeDualizingDiagonalHom_iso` records its image under `Δ^!`, which is
`T(RHom_A(M, N)) ≅ Δ^!(RHom_B(p₁^*M, p₁^*N))`.

## Why the two halves do not join here, and what the gap is

They are stated in the library's **two spellings of internal derived Hom**.

* The projection formula and the diagonal-Hom identification are phrased with
  `StacksDraft.DerivedHom.DerivedInternalHom.Model.hom`, the same-universe model bifunctor.
* [stacks 0A6A] is phrased with
  `Stacks.DerivedHom.ScalarTransportedInternalHom.hom`, which
  `Stacks.DerivedHom.ScalarTransportedInternalHom.hom_eq` identifies on the nose with
  `(StacksDraft.DerivedHom.derivedHomAdjunctionOverRing _).hom` — the model bifunctor over
  `ULift R` conjugated by `StacksDraft.DerivedHom.derivedScalarEquivalence`.

**That spelling gap is closed**, in
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessInternalHomCompare`, and the two fragments of
this module are joined there as `Dualizing.nonempty_relativeDualizingDiagonalHom_modelHom_iso`.
The route is the one `Dualizing.homIsoOfTensorIsoLeft` below makes available: the two bifunctors
are the internal Homs of two tensor--Hom adjunctions of [stacks 0A63] on one category, so adjoint
uniqueness identifies them as soon as their *tensors* are compared naturally in the first
variable.  Each of the two tensor bifunctors was already compared, naturally in both variables,
to a canonical derived tensor product of [stacks 068I] —
`Dualizing.derivedHomAdjunctionTensorNatIso` to the same-universe one and
`Dualizing.derivedHomAdjunctionTensorNatIsoGeneral` to the one in an independent module universe
— and what was missing was a comparison of those two canonical data carrying any naturality:
`Stacks.Duality.derivedTensorGeneralCompare` reads both off *chosen* K-flat resolutions.  It is
supplied by `Dualizing.uniqueDerivedTensorGeneralNatIso` of
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBifunctorCompare`, which is the
uniqueness of the derived tensor product of [stacks 068I] as a bifunctor.

Before that, no comparison of the two internal-Hom bifunctors existed at a general first
argument: the only ones were at the first argument `A_B`, where
`Dualizing.modelHomIsoRestrictScalarsDerivedHom` and
`Dualizing.restrictScalarsDerivedHomIso` both compute `Δ_*Δ^!` — the first for the model
bifunctor and with no hypothesis, the second for the transported one and only for an object with
a bounded-below representative by injectives — and `Dualizing.scalarDerivedHomIso`, which goes
only as far as the lifted ring.  Adjoint uniqueness, the one route that does not need the
K-injective model construction again, was unavailable exactly because the tensor comparison
carried no naturality.

Beyond that spelling gap there was a mathematical one, and **it is now closed as well**.  Even
with the two halves in one
spelling, the remaining step

`p₁_* RHom_B(Δ_*M, Y) ≅ RHom_A(M, Δ^!Y)`

is the *enriched* form of `Δ_* ⊣ Δ^!` — true at `M = A[0]`, where it is exactly
`Dualizing.nonempty_derivedHom_iso_restrictScalars_modelHom` below, and a separate theorem for
general `M`.  Its Yoneda reduction needs the projection formula
`Δ_*(Z ⊗ᴸ_A M) ≅ Δ_*Z ⊗ᴸ_B p₁^*M` *naturally in `Z`*, whereas
`Dualizing.nonempty_tensor_diagonalObject_iso_restrictScalars_lmul` supplies it pointwise, as a
`Nonempty`, each component being read off a separately chosen K-flat representative.  That
naturality is `Dualizing.diagonalProjectionNatIso` of
`StacksFrontier.RingTheory.Dualizing.RelativeProjectionFormulaNatural`, which descends the
chain-level projection formula at a retraction to an isomorphism of functors `D(A) ⥤ D(B)`; the
enriched adjunction it buys is `Dualizing.enrichedDiagonalHomIso`, and Step 1 is
`Dualizing.nonempty_relativeDualizingFunctor_modelHom_commutation`, both in
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessEnrichedAdjunction`.

## Main results

* `Dualizing.derivedRestrictScalarsSectionIso` — derived restriction of scalars along a ring map
  undoes derived restriction along a section of it.
* `Dualizing.nonempty_derivedHom_iso_restrictScalars_modelHom` — **`Δ^!` read inside `D(B)`**:
  `Δ^!(Z) ≅ p₁_* RHom_B(A_B, Z)`.
* `Dualizing.nonempty_relativeDualizingFunctor_iso_restrictScalars_modelHom` — the same at the
  functor `T` of the defining condition of [stacks 0E2C]: `T(X) ≅ p₁_* RHom_B(A_B, p₁^*X)`.
* `Dualizing.nonempty_derivedHom_modelHom_iso_restrictScalars_modelHom` — **the currying
  isomorphism, the projection formula and the adjunction composed**:
  `Δ^!(RHom_B(p₁^*M, Y)) ≅ p₁_* RHom_B(Δ_*M, Y)`, for arbitrary `M` and `Y`.
* `Dualizing.nonempty_diagonalDerivedExtension_derivedHom_iso` — **flat base change in the
  route's vocabulary**: `p₁^* RHom_A(M, N) ≅ RHom_B(p₁^*M, p₁^*N)` for `M` pseudo-coherent and
  `N` bounded below.
* `Dualizing.nonempty_relativeDualizingDiagonalHom_iso` — its image under `Δ^!`:
  `T(RHom_A(M, N)) ≅ Δ^!(RHom_B(p₁^*M, p₁^*N))`.
* `Dualizing.homIsoOfTensorIsoLeft` — **adjoint uniqueness in the first variable**: two
  tensor--Hom adjunctions of [stacks 0A63] on one derived category whose tensors agree at `L`
  naturally in the other variable have the same internal Hom out of `L`.  This is what reduces
  the spelling gap above to a comparison of the two *tensors*, and it is applied in
  `StacksFrontier.RingTheory.Dualizing.RelativeUniquenessInternalHomCompare`.

## References

* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
* [Stacks Project, Tag 0A65](https://stacks.math.columbia.edu/tag/0A65)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

noncomputable section

section Section

variable {A B : Type u} [CommRing A] [CommRing B]

/-- An isomorphism of exact functors of modules descends to their functors of derived
categories. -/
noncomputable def derivedMapNatIso {C D : Type*} [Category C] [Category D] [Abelian C]
    [Abelian D] (F G : C ⥤ D) [F.Additive] [G.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G] (e : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ F.mapDerivedCategory)
    (DerivedCategory.Q ⋙ G.mapDerivedCategory)
    F.mapDerivedCategory G.mapDerivedCategory
    (F.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ))
        DerivedCategory.Q ≪≫ G.mapDerivedCategoryFactors.symm)

/-- The identity functor induces the identity on derived categories. -/
noncomputable def derivedMapIdIso (C : Type*) [Category C] [Abelian C] :
    (𝟭 C).mapDerivedCategory ≅ 𝟭 (DerivedCategory C) :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (𝟭 C).mapDerivedCategory) (DerivedCategory.Q ⋙ 𝟭 _)
    (𝟭 C).mapDerivedCategory (𝟭 (DerivedCategory C))
    ((𝟭 C).mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ)) DerivedCategory.Q ≪≫
      Functor.leftUnitor DerivedCategory.Q ≪≫ (Functor.rightUnitor DerivedCategory.Q).symm)

/-- Derived restriction of scalars along the identity ring map is the identity. -/
noncomputable def derivedRestrictScalarsIdIso (A : Type u) [CommRing A] :
    (ModuleCat.restrictScalars.{u} (RingHom.id A)).mapDerivedCategory ≅
      𝟭 (DerivedCategory (ModuleCat.{u} A)) :=
  derivedMapNatIso (ModuleCat.restrictScalars.{u} (RingHom.id A)) (𝟭 (ModuleCat.{u} A))
      (ModuleCat.restrictScalarsId.{u} A) ≪≫
    derivedMapIdIso (ModuleCat.{u} A)

/-- **Derived restriction of scalars along a section undoes derived restriction along the map.**
If `g : B → A` has the section `f : A → B`, then restricting an object of `D(A)` along `g` and
then along `f` returns it, restriction of scalars being functorial and exact.

At the coprojection `f = p₁` and the multiplication map `g = Δ` of `B = A ⊗[R] A` this is what
lets the derived coextension `Δ^!` of [stacks 0A70] be read inside `D(B)`. -/
noncomputable def derivedRestrictScalarsSectionIso (f : A →+* B) (g : B →+* A)
    (h : g.comp f = RingHom.id A) :
    (ModuleCat.restrictScalars.{u} g).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{u} f).mapDerivedCategory ≅
      𝟭 (DerivedCategory (ModuleCat.{u} A)) := by
  have e := StacksDraft.Perfect.derivedRestrictScalarsComp.{u, u} f g
  rw [h] at e
  exact e ≪≫ derivedRestrictScalarsIdIso A

end Section

section Diagonal

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- **The derived coextension `Δ^!` of [stacks 0A70] read inside `D(B)`.**  For `B = A ⊗[R] A`
with multiplication map `Δ : B → A` and left coprojection `p₁ : A → B`,

`Δ^!(Z) ≅ p₁_* RHom_B(A_B, Z)`,

where `RHom_B` is the internal derived Hom of [stacks 0A63] and `A_B` is the diagonal.  The
internal Hom out of the diagonal is the restriction along `Δ` of `Δ^!` by
`Dualizing.nonempty_modelHomIsoRestrictScalarsDerivedHom`, and restriction along `p₁` undoes
restriction along `Δ` because `p₁` is a section of `Δ`. -/
theorem nonempty_derivedHom_iso_restrictScalars_modelHom
    (Z : DerivedCategory (ModuleCat.{u} (A ⊗[R] A))) :
    Nonempty
      ((derivedHom.{u, u, u}
            (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj Z ≅
        (ModuleCat.restrictScalars.{u}
            (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).mapDerivedCategory.obj
          ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom (A ⊗[R] A)).obj
            (Opposite.op (diagonalObject R A), Z))) := by
  have e := (nonempty_modelHomIsoRestrictScalarsDerivedHom
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom Z).some
  exact ⟨((derivedRestrictScalarsSectionIso
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)
        (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom
        (lmul'_comp_includeLeftRingHom R A)).app _).symm ≪≫
    (ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).mapDerivedCategory.mapIso
        e.symm⟩

end Diagonal

section Flat

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]

/-- **The functor `T` of the defining condition of [stacks 0E2C], read inside `D(B)`.**  For
`T(X) = Δ^!(p₁^*X)`,

`T(X) ≅ p₁_* RHom_B(A_B, p₁^*X)`.

This is `Dualizing.nonempty_derivedHom_iso_restrictScalars_modelHom` at the derived base change
of `X` along the left coprojection. -/
theorem nonempty_relativeDualizingFunctor_iso_restrictScalars_modelHom
    (X : DerivedCategory (ModuleCat.{u} A)) :
    Nonempty
      ((derivedHom.{u, u, u}
            (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
            ((diagonalDerivedExtension R A).obj X) ≅
        (ModuleCat.restrictScalars.{u}
            (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).mapDerivedCategory.obj
          ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom (A ⊗[R] A)).obj
            (Opposite.op (diagonalObject R A), (diagonalDerivedExtension R A).obj X))) :=
  nonempty_derivedHom_iso_restrictScalars_modelHom R A ((diagonalDerivedExtension R A).obj X)

/-- **The currying isomorphism of [stacks 0A65], the unrestricted projection formula at the
diagonal and the adjunction `Δ_* ⊣ Δ^!` of [stacks 0A70], composed.**  For every object `M` of
`D(A)` and every object `Y` of `D(B)`,

`Δ^!(RHom_B(p₁^*M, Y)) ≅ p₁_* RHom_B(Δ_*M, Y)`,

with no pseudo-coherence, flatness or boundedness hypothesis on `M` or `Y`.

The proof reads `Δ^!` inside `D(B)` by
`Dualizing.nonempty_derivedHom_iso_restrictScalars_modelHom`, turning the left-hand side into
`p₁_* RHom_B(A_B, RHom_B(p₁^*M, Y))`; the currying isomorphism `Dualizing.homCurryIso` rewrites
that as `p₁_* RHom_B(A_B ⊗ᴸ_B p₁^*M, Y)`; and
`Dualizing.nonempty_tensor_diagonalObject_iso_restrictScalars_lmul` identifies
`A_B ⊗ᴸ_B p₁^*M` with `Δ_*M`.

Three of the four ingredients the duality route of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality` names for its Step 1 are composed
here; the fourth, flat base change, is
`Dualizing.nonempty_diagonalDerivedExtension_derivedHom_iso` below. -/
theorem nonempty_derivedHom_modelHom_iso_restrictScalars_modelHom
    (M : DerivedCategory (ModuleCat.{u} A))
    (Y : DerivedCategory (ModuleCat.{u} (A ⊗[R] A))) :
    Nonempty
      ((derivedHom.{u, u, u}
            (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
            ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom (A ⊗[R] A)).obj
              (Opposite.op ((diagonalDerivedExtension R A).obj M), Y)) ≅
        (ModuleCat.restrictScalars.{u}
            (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).mapDerivedCategory.obj
          ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom (A ⊗[R] A)).obj
            (Opposite.op ((ModuleCat.restrictScalars.{u}
              (Algebra.TensorProduct.lmul' R :
                A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory.obj M), Y))) := by
  let d := (StacksDraft.DerivedHom.derivedHomAdjunction
    (R := A ⊗[R] A)).toDerivedHomAdjunction
  have hproj := (nonempty_tensor_diagonalObject_iso_restrictScalars_lmul R A M).some
  have hcurry := (homCurryIso d (diagonalObject R A)
    ((diagonalDerivedExtension R A).obj M) Y).symm
  have hhom := d.hom.mapIso (hproj.symm.op.prod (Iso.refl Y))
  have hD := (nonempty_derivedHom_iso_restrictScalars_modelHom R A
    ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom (A ⊗[R] A)).obj
      (Opposite.op ((diagonalDerivedExtension R A).obj M), Y))).some
  exact ⟨hD ≪≫ (ModuleCat.restrictScalars.{u}
    (Algebra.TensorProduct.includeLeftRingHom :
      A →+* A ⊗[R] A)).mapDerivedCategory.mapIso (hcurry ≪≫ hhom)⟩

/-- **Flat base change for derived Hom along the left coprojection, in the route's vocabulary.**
For `M` pseudo-coherent and `N` bounded below,

`p₁^* RHom_A(M, N) ≅ RHom_B(p₁^*M, p₁^*N)`,

the internal derived Hom being that of [stacks 0A63] and `p₁^*` the derived base change
`Dualizing.diagonalDerivedExtension` used in the definition of a relative dualizing complex.

This is the third case of [stacks 0A6A], `p₁` being flat by
`Dualizing.includeLeftRingHom_flat`; the comparison morphism of [stacks 0E1X] is read at the
total derived extension of scalars and transported to `Dualizing.diagonalDerivedExtension` along
`Dualizing.diagonalDerivedExtensionIsoTotalDerived`. -/
theorem nonempty_diagonalDerivedExtension_derivedHom_iso
    (M N : DerivedCategory (ModuleCat.{u} A))
    (hM : StacksDraft.PseudoCoherence.IsPseudoCoherent M) (b : ℤ) (hN : N.IsGE b) :
    Nonempty
      ((diagonalDerivedExtension R A).obj
          ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A).hom.obj
            (Opposite.op M, N)) ≅
        (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing (A ⊗[R] A)).hom.obj
          (Opposite.op ((diagonalDerivedExtension R A).obj M),
            (diagonalDerivedExtension R A).obj N)) := by
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)
  have hiso : IsIso (@Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, u, u}
      A (A ⊗[R] A) _ _ (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)
      D.functor D.comparison D.isLeftDerived M N) :=
    @Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange.{u, u, u}
      A (A ⊗[R] A) _ _ (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)
      D.functor D.comparison D.isLeftDerived M N
      (.inr (.inr (.inl ⟨includeLeftRingHom_flat R A, hM, ⟨b, hN⟩⟩)))
  have t := diagonalDerivedExtensionIsoTotalDerived R A
  have hT := (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing (A ⊗[R] A)).hom.mapIso
    ((t.app M).symm.op.prod (t.app N))
  exact ⟨(t.app _).symm ≪≫ @asIso _ _ _ _ _ hiso ≪≫ hT⟩

/-- **Flat base change applied inside the functor `T` of [stacks 0E2C].**  For `M`
pseudo-coherent and `N` bounded below,

`T(RHom_A(M, N)) ≅ Δ^!(RHom_B(p₁^*M, p₁^*N))`.

This is the first step of Step 1 of the duality route of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality`, and it is where the only hypotheses
of that step are consumed: the remaining steps, composed in
`Dualizing.nonempty_derivedHom_modelHom_iso_restrictScalars_modelHom`, need none. -/
theorem nonempty_relativeDualizingDiagonalHom_iso
    (M N : DerivedCategory (ModuleCat.{u} A))
    (hM : StacksDraft.PseudoCoherence.IsPseudoCoherent M) (b : ℤ) (hN : N.IsGE b) :
    Nonempty
      ((derivedHom.{u, u, u}
            (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
            ((diagonalDerivedExtension R A).obj
              ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing A).hom.obj
                (Opposite.op M, N))) ≅
        (derivedHom.{u, u, u}
            (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
            ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing (A ⊗[R] A)).hom.obj
              (Opposite.op ((diagonalDerivedExtension R A).obj M),
                (diagonalDerivedExtension R A).obj N))) :=
  ⟨(derivedHom.{u, u, u}
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapIso
      (nonempty_diagonalDerivedExtension_derivedHom_iso R A M N hM b hN).some⟩

end Flat

section AdjointUniqueness

universe u₀ v₀ w₀

variable {S : Type u₀} [CommRing S] [HasDerivedCategory.{w₀} (ModuleCat.{v₀} S)]

/-- **Adjoint uniqueness in the first variable.**  Let `d₁` and `d₂` be two tensor--Hom
adjunctions of [stacks 0A63] on one and the same derived category, and fix an object `L`.  If the
two tensor products agree at `L` *naturally in the other variable* — an isomorphism
`d₂(K, L) ≅ d₁(K, L)` for every `K`, compatible with the maps `K' ⟶ K` — then the two internal
Homs out of `L` agree:

`RHom₁(L, M) ≅ RHom₂(L, M)`   for every `M`.

Both sides represent the same functor `K ↦ Hom(d(K, L), M)` of the first variable, so this is the
Yoneda argument and nothing else; no naturality in `L` or in `M` is used, and none is produced.

This is the step that the spelling gap of this module's documentation used to block.  The two
spellings of internal derived Hom at one universe —
`StacksDraft.DerivedHom.DerivedInternalHom.Model.hom` and
`(StacksDraft.DerivedHom.derivedHomAdjunctionOverRing _).hom` — are both the Hom of such an
adjunction, so an isomorphism of their *tensors*, natural in the first variable alone, already
reconciles them object by object and joins the two halves of Step 1.  That isomorphism is
`Dualizing.derivedHomAdjunctionTensorNatIsoCompare` of
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBifunctorCompare`, and the
reconciliation it yields is
`Dualizing.modelHomIsoDerivedHomAdjunctionOverRing` of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessInternalHomCompare`. -/
noncomputable def homIsoOfTensorIsoLeft
    (d₁ d₂ : StacksDraft.DerivedHom.DerivedHomAdjunction (R := S))
    (L M : DerivedCategory (ModuleCat.{v₀} S))
    (τ : ∀ K : DerivedCategory (ModuleCat.{v₀} S),
      d₂.tensor.obj (K, L) ≅ d₁.tensor.obj (K, L))
    (hτ : ∀ (K K' : DerivedCategory (ModuleCat.{v₀} S)) (f : K' ⟶ K),
      d₂.tensor.map ((f, 𝟙 L) : ((K', L) : _ × _) ⟶ (K, L)) ≫ (τ K).hom =
        (τ K').hom ≫ d₁.tensor.map ((f, 𝟙 L) : ((K', L) : _ × _) ⟶ (K, L))) :
    d₁.hom.obj (Opposite.op L, M) ≅ d₂.hom.obj (Opposite.op L, M) := by
  -- The two representable functors of the first variable are identified by `τ`.
  let e : ∀ K : DerivedCategory (ModuleCat.{v₀} S),
      (K ⟶ d₁.hom.obj (Opposite.op L, M)) ≃ (K ⟶ d₂.hom.obj (Opposite.op L, M)) := fun K =>
    { toFun := fun a => (d₂.homEquiv K L M).symm ((τ K).hom ≫ d₁.homEquiv K L M a)
      invFun := fun b => (d₁.homEquiv K L M).symm ((τ K).inv ≫ d₂.homEquiv K L M b)
      left_inv := fun a => by
        change (d₁.homEquiv K L M).symm ((τ K).inv ≫ d₂.homEquiv K L M
          ((d₂.homEquiv K L M).symm ((τ K).hom ≫ d₁.homEquiv K L M a))) = a
        rw [AddEquiv.apply_symm_apply, Iso.inv_hom_id_assoc, AddEquiv.symm_apply_apply]
      right_inv := fun b => by
        change (d₂.homEquiv K L M).symm ((τ K).hom ≫ d₁.homEquiv K L M
          ((d₁.homEquiv K L M).symm ((τ K).inv ≫ d₂.homEquiv K L M b))) = b
        rw [AddEquiv.apply_symm_apply, Iso.hom_inv_id_assoc, AddEquiv.symm_apply_apply] }
  have hnat : ∀ (K K' : DerivedCategory (ModuleCat.{v₀} S)) (f : K' ⟶ K)
      (a : K ⟶ d₁.hom.obj (Opposite.op L, M)), e K' (f ≫ a) = f ≫ e K a := by
    intro K K' f a
    have key : (τ K').hom ≫ d₁.homEquiv K' L M (f ≫ a) =
        d₂.tensor.map ((f, 𝟙 L) : ((K', L) : _ × _) ⟶ (K, L)) ≫
          d₂.homEquiv K L M (e K a) := by
      rw [d₁.homEquiv_naturality_left, ← Category.assoc, ← hτ K K' f, Category.assoc]
      change _ = _ ≫ d₂.homEquiv K L M ((d₂.homEquiv K L M).symm _)
      rw [AddEquiv.apply_symm_apply]
    change (d₂.homEquiv K' L M).symm _ = _
    rw [key, ← d₂.homEquiv_naturality_left, AddEquiv.symm_apply_apply]
  have hnat' : ∀ (K K' : DerivedCategory (ModuleCat.{v₀} S)) (f : K' ⟶ K)
      (b : K ⟶ d₂.hom.obj (Opposite.op L, M)),
      (e K').symm (f ≫ b) = f ≫ (e K).symm b := by
    intro K K' f b
    apply (e K').injective
    rw [Equiv.apply_symm_apply, hnat, Equiv.apply_symm_apply]
  refine
    { hom := e _ (𝟙 (d₁.hom.obj (Opposite.op L, M)))
      inv := (e _).symm (𝟙 (d₂.hom.obj (Opposite.op L, M)))
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · have h := hnat' (d₂.hom.obj (Opposite.op L, M)) (d₁.hom.obj (Opposite.op L, M))
      (e _ (𝟙 (d₁.hom.obj (Opposite.op L, M)))) (𝟙 (d₂.hom.obj (Opposite.op L, M)))
    rw [Category.comp_id, Equiv.symm_apply_apply] at h
    exact h.symm
  · have h := hnat (d₁.hom.obj (Opposite.op L, M)) (d₂.hom.obj (Opposite.op L, M))
      ((e _).symm (𝟙 (d₂.hom.obj (Opposite.op L, M)))) (𝟙 (d₁.hom.obj (Opposite.op L, M)))
    rw [Category.comp_id, Equiv.apply_symm_apply] at h
    exact h.symm

/-- **The comparison of `Dualizing.homIsoOfTensorIsoLeft`, computed.** It is the transpose
through the second adjunction of evaluation for the first, precomposed with the comparison of
the two tensor products at the internal-Hom object. Everything below is proved from this
formula and the three naturality fields of
`StacksDraft.DerivedHom.DerivedHomAdjunction`. -/
theorem homIsoOfTensorIsoLeft_hom
    (d₁ d₂ : StacksDraft.DerivedHom.DerivedHomAdjunction (R := S))
    (L M : DerivedCategory (ModuleCat.{v₀} S))
    (τ : ∀ K : DerivedCategory (ModuleCat.{v₀} S),
      d₂.tensor.obj (K, L) ≅ d₁.tensor.obj (K, L))
    (hτ : ∀ (K K' : DerivedCategory (ModuleCat.{v₀} S)) (f : K' ⟶ K),
      d₂.tensor.map ((f, 𝟙 L) : ((K', L) : _ × _) ⟶ (K, L)) ≫ (τ K).hom =
        (τ K').hom ≫ d₁.tensor.map ((f, 𝟙 L) : ((K', L) : _ × _) ⟶ (K, L))) :
    (homIsoOfTensorIsoLeft d₁ d₂ L M τ hτ).hom =
      (d₂.homEquiv (d₁.hom.obj (Opposite.op L, M)) L M).symm
        ((τ (d₁.hom.obj (Opposite.op L, M))).hom ≫ d₁.evaluation L M) :=
  rfl

/-- The family `K ↦ σ.app (K, L)` cut out of an isomorphism of tensor bifunctors satisfies the
first-variable naturality that `Dualizing.homIsoOfTensorIsoLeft` asks for. -/
theorem tensorIsoLeft_naturality
    (d₁ d₂ : StacksDraft.DerivedHom.DerivedHomAdjunction (R := S))
    (σ : d₂.tensor ≅ d₁.tensor) (L : DerivedCategory (ModuleCat.{v₀} S))
    (K K' : DerivedCategory (ModuleCat.{v₀} S)) (f : K' ⟶ K) :
    d₂.tensor.map ((f, 𝟙 L) : ((K', L) : _ × _) ⟶ (K, L)) ≫ (σ.app (K, L)).hom =
      (σ.app (K', L)).hom ≫ d₁.tensor.map ((f, 𝟙 L) : ((K', L) : _ × _) ⟶ (K, L)) :=
  σ.hom.naturality ((f, 𝟙 L) : ((K', L) : _ × _) ⟶ (K, L))

/-- **The comparison is natural in the internal-Hom target.** Transposing through the second
adjunction turns the two sides into evaluation for the first adjunction composed with a
morphism, which is `StacksDraft.DerivedHom.DerivedHomAdjunction.evaluation_naturality_right`. -/
theorem homIsoOfTensorIsoLeft_naturality_right
    (d₁ d₂ : StacksDraft.DerivedHom.DerivedHomAdjunction (R := S))
    (L M M' : DerivedCategory (ModuleCat.{v₀} S)) (g : M ⟶ M')
    (τ : ∀ K : DerivedCategory (ModuleCat.{v₀} S),
      d₂.tensor.obj (K, L) ≅ d₁.tensor.obj (K, L))
    (hτ : ∀ (K K' : DerivedCategory (ModuleCat.{v₀} S)) (f : K' ⟶ K),
      d₂.tensor.map ((f, 𝟙 L) : ((K', L) : _ × _) ⟶ (K, L)) ≫ (τ K).hom =
        (τ K').hom ≫ d₁.tensor.map ((f, 𝟙 L) : ((K', L) : _ × _) ⟶ (K, L))) :
    (homIsoOfTensorIsoLeft d₁ d₂ L M τ hτ).hom ≫
        d₂.hom.map ((𝟙 (Opposite.op L), g) :
          ((Opposite.op L, M) : _ × _) ⟶ (Opposite.op L, M')) =
      d₁.hom.map ((𝟙 (Opposite.op L), g) :
          ((Opposite.op L, M) : _ × _) ⟶ (Opposite.op L, M')) ≫
        (homIsoOfTensorIsoLeft d₁ d₂ L M' τ hτ).hom := by
  apply (d₂.homEquiv (d₁.hom.obj (Opposite.op L, M)) L M').injective
  rw [d₂.homEquiv_naturality_right, d₂.homEquiv_naturality_left,
    homIsoOfTensorIsoLeft_hom, homIsoOfTensorIsoLeft_hom,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
    reassoc_of% (hτ (d₁.hom.obj (Opposite.op L, M')) (d₁.hom.obj (Opposite.op L, M))
      (d₁.hom.map ((𝟙 (Opposite.op L), g) :
        ((Opposite.op L, M) : _ × _) ⟶ (Opposite.op L, M')))),
    d₁.evaluation_naturality_right, Category.assoc]

/-- **The comparison is dinatural in the internal-Hom source.** This is the half that
`Dualizing.homIsoOfTensorIsoLeft` does not produce from its own hypotheses: the family `τ` there
is attached to one `L`, and relating two of them needs the comparison of the tensors to be
natural in the *second* variable as well, which an isomorphism of bifunctors supplies. The
remaining identity is
`StacksDraft.DerivedHom.DerivedHomAdjunction.evaluation_naturality_left`. -/
theorem homIsoOfTensorIsoLeft_naturality_left
    (d₁ d₂ : StacksDraft.DerivedHom.DerivedHomAdjunction (R := S))
    (σ : d₂.tensor ≅ d₁.tensor) (L L' M : DerivedCategory (ModuleCat.{v₀} S)) (h : L' ⟶ L) :
    (homIsoOfTensorIsoLeft d₁ d₂ L M (fun K => σ.app (K, L))
          (tensorIsoLeft_naturality d₁ d₂ σ L)).hom ≫
        d₂.hom.map ((h.op, 𝟙 M) : ((Opposite.op L, M) : _ × _) ⟶ (Opposite.op L', M)) =
      d₁.hom.map ((h.op, 𝟙 M) : ((Opposite.op L, M) : _ × _) ⟶ (Opposite.op L', M)) ≫
        (homIsoOfTensorIsoLeft d₁ d₂ L' M (fun K => σ.app (K, L'))
          (tensorIsoLeft_naturality d₁ d₂ σ L')).hom := by
  apply (d₂.homEquiv (d₁.hom.obj (Opposite.op L, M)) L' M).injective
  rw [d₂.homEquiv_dinaturality, d₂.homEquiv_naturality_left,
    homIsoOfTensorIsoLeft_hom, homIsoOfTensorIsoLeft_hom,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  simp only [Iso.app_hom]
  rw [reassoc_of% (σ.hom.naturality ((𝟙 (d₁.hom.obj (Opposite.op L, M)), h) :
      ((d₁.hom.obj (Opposite.op L, M), L') : _ × _) ⟶ (d₁.hom.obj (Opposite.op L, M), L))),
    reassoc_of% (σ.hom.naturality ((d₁.hom.map ((h.op, 𝟙 M) :
        ((Opposite.op L, M) : _ × _) ⟶ (Opposite.op L', M)), 𝟙 L') :
      ((d₁.hom.obj (Opposite.op L, M), L') : _ × _) ⟶
        (d₁.hom.obj (Opposite.op L', M), L'))),
    d₁.evaluation_naturality_left]

/-- **Two tensor--Hom adjunctions on one derived category have isomorphic internal Homs**, as
bifunctors, as soon as their tensor products are isomorphic as bifunctors. Each component is
`Dualizing.homIsoOfTensorIsoLeft`; naturality in a general morphism of `D(S)ᵒᵖ × D(S)` is the
two halves `Dualizing.homIsoOfTensorIsoLeft_naturality_left` and
`Dualizing.homIsoOfTensorIsoLeft_naturality_right`, applied to the factorization of that
morphism through the two one-variable ones. -/
noncomputable def homNatIsoOfTensorNatIso
    (d₁ d₂ : StacksDraft.DerivedHom.DerivedHomAdjunction (R := S))
    (σ : d₂.tensor ≅ d₁.tensor) : d₁.hom ≅ d₂.hom :=
  NatIso.ofComponents
    (fun X => homIsoOfTensorIsoLeft d₁ d₂ X.1.unop X.2 (fun K => σ.app (K, X.1.unop))
      (tensorIsoLeft_naturality d₁ d₂ σ X.1.unop))
    (by
      intro X Y φ
      let Z : (DerivedCategory (ModuleCat.{v₀} S))ᵒᵖ × DerivedCategory (ModuleCat.{v₀} S) :=
        (Y.1, X.2)
      have hsplit : φ = ((φ.1, 𝟙 X.2) : X ⟶ Z) ≫ ((𝟙 Y.1, φ.2) : Z ⟶ Y) := by
        refine Prod.ext ?_ ?_ <;> simp [Z]
      have hr := homIsoOfTensorIsoLeft_naturality_right d₁ d₂ Y.1.unop X.2 Y.2 φ.2
        (fun K => σ.app (K, Y.1.unop)) (tensorIsoLeft_naturality d₁ d₂ σ Y.1.unop)
      have hl := homIsoOfTensorIsoLeft_naturality_left d₁ d₂ σ X.1.unop Y.1.unop X.2 φ.1.unop
      simp only [Opposite.op_unop, Quiver.Hom.op_unop] at hr hl
      rw [hsplit, d₁.hom.map_comp, d₂.hom.map_comp, Category.assoc, ← hr, ← Category.assoc,
        ← hl, Category.assoc])

end AdjointUniqueness

end

end Dualizing

end
