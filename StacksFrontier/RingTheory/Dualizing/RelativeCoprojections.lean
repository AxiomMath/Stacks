module

public import StacksFrontier.Homology.Perfect.DerivedReduction
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso
public import StacksFrontier.RingTheory.Dualizing.Relative
public import StacksFrontier.RingTheory.PseudoCoherentMap.Surjection

/-!
# The coprojections and the diagonal of `A ⊗[R] A`

Let `R → A` be a ring map and put `S = A ⊗[R] A`.  There are two coprojections
`p₁, p₂ : A → S`, namely `a ↦ a ⊗ 1` and `a ↦ 1 ⊗ a`, and the multiplication map
`Δ : S → A`, `a ⊗ b ↦ a * b`.  Both coprojections are sections of `Δ`, and the flip
automorphism of `S` interchanges them while fixing `Δ`.  These identities are the algebraic
substance of the symmetry between the two factors of `S`.

Derived extension of scalars is only functorial up to canonical isomorphism, so the identity
`Δ ∘ pᵢ = id` does not immediately say that derived base change to `S` along a coprojection,
followed by derived base change back along `Δ`, is the identity on `D(A)`.  That statement is
obtained here from the comparison isomorphism for a composite of derived extensions and the
computation of derived extension along the identity ring map: for every object `K` of `D(A)`,
`A ⊗ᴸ_S (K ⊗ᴸ_A S) ≅ K`.

When `A` is flat over `R` the left coprojection is flat, and `Dualizing.diagonalDerivedExtension`
is extension of scalars along it read directly on derived categories.  That functor is identified
below with the total left derived functor, which is what makes the retraction statement available
in the form used by the diagonal condition defining a relative dualizing complex.

The flip also makes the diagonal condition defining a relative dualizing complex symmetric in the
two coprojections: derived Hom from the diagonal into the derived base change along the right
coprojection is the same object as derived Hom from the diagonal into the derived base change
along the left one.  Restriction of scalars along the flip is its own left adjoint, and composing
it with restriction along the diagonal returns restriction along the diagonal; so derived Hom from
the diagonal, being the right adjoint of the latter, does not see the flip.

## Main results

* `Dualizing.lmul'_comp_includeLeftRingHom`, `Dualizing.lmul'_comp_includeRight` — each
  coprojection is a section of the multiplication map.
* `Dualizing.comm_comp_includeLeftRingHom`, `Dualizing.lmul'_comp_comm`,
  `Dualizing.comm_comp_comm` — the flip automorphism of `A ⊗[R] A` is an involution which
  carries the left coprojection to the right one and fixes the multiplication map.
* `Dualizing.diagonalDerivedExtensionIsoTotalDerived` — the exact extension of scalars along the
  left coprojection, read on derived categories, is the total left derived functor of termwise
  extension of scalars.
* `Dualizing.derivedExtensionScalarsRetractionIso` — derived extension of scalars along a ring
  map and then along a retraction of it is the identity.
* `Dualizing.diagonalDerivedExtensionRetractionIso`,
  `Dualizing.rightCoprojectionRetractionIso` — the two instances of the previous isomorphism at
  the coprojections of `A ⊗[R] A`, the first phrased for the functor used in the definition of a
  relative dualizing complex.
* `Dualizing.derivedHomFlipIso`, `Dualizing.flipDerivedExtensionIso`,
  `Dualizing.derivedHomIncludeRightIso` — derived Hom from the diagonal is insensitive to the
  flip, derived extension along the flip is restriction along it, and consequently the two
  coprojections give the same derived Hom object.
* `Dualizing.IsRelativeDualizingComplex.diagonalDerivedHom_includeRight` — the diagonal condition
  of a relative dualizing complex, stated for the right coprojection.
* `Dualizing.isPseudoCoherent_diagonal` — for `R → A` flat of finite presentation, `A` is
  pseudo-coherent as a module over `A ⊗[R] A` along the multiplication map.

## Implementation notes

The identification of `Dualizing.diagonalDerivedExtension` with the total left derived functor
reconstructs the exactness instances in the order used by its definition, so that the two
functors are the same term; uniqueness of left derived functors then supplies the isomorphism,
the degreewise functor being its own left derived functor because it inverts
quasi-isomorphisms.

Derived extension of scalars along the flip is compared with restriction of scalars along it by
instantiating `StacksDraft.DerivedRingIso.derivedExtensionScalarsRestrictIso` at the identity
homomorphism and then using that derived extension along the identity is the identity, which is
available objectwise rather than as a natural isomorphism; the comparisons depending on it are
therefore stated at an object.

Pseudo-coherence of `A` over `A ⊗[R] A` is read off from Stacks 0E1T at the surjection
`A ⊗[R] A → A`: the algebra `A ⊗[R] A` is flat and of finite presentation over `R` because `A`
is, and `A` is trivially pseudo-coherent over itself, so the equivalence of absolute
pseudo-coherence in `D(A)` with absolute pseudo-coherence after restriction of scalars gives the
statement. The multiplication map is used as the structure map `A ⊗[R] A → A` only inside the
proof, so that the statement itself mentions no auxiliary algebra instance.

## References

* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
* [Stacks Project, Tag 0E1T](https://stacks.math.columbia.edu/tag/0E1T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- The left coprojection `a ↦ a ⊗ 1` is a section of multiplication `a ⊗ b ↦ a * b`. -/
theorem lmul'_comp_includeLeftRingHom (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A) = RingHom.id A := by
  ext a
  simp

/-- The right coprojection `a ↦ 1 ⊗ a` is a section of multiplication `a ⊗ b ↦ a * b`. -/
theorem lmul'_comp_includeRight (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom.comp
      (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom = RingHom.id A := by
  ext a
  simp

/-- The flip automorphism of `A ⊗[R] A` carries the left coprojection to the right one. -/
theorem comm_comp_includeLeftRingHom (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    (Algebra.TensorProduct.comm R A A).toRingEquiv.toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A) =
      (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom := by
  ext a
  simp

/-- The flip of `A ⊗[R] A` is an involution. -/
theorem comm_comp_comm (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    (Algebra.TensorProduct.comm R A A).toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.comm R A A).toRingEquiv.toRingHom = RingHom.id (A ⊗[R] A) := by
  ext a <;> simp

/-- The flip automorphism of `A ⊗[R] A` fixes the multiplication map, because `A` is
commutative. -/
theorem lmul'_comp_comm (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom.comp
        (Algebra.TensorProduct.comm R A A).toRingEquiv.toRingHom =
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom := by
  ext a <;> simp [mul_comm]

noncomputable section

/-- Extension of scalars along the left coprojection `A → A ⊗[R] A`, read on derived categories,
is the total left derived functor of termwise extension of scalars along it.  The coprojection is
flat, so the degreewise functor is exact and inverts quasi-isomorphisms, hence is its own total
left derived functor; uniqueness of left derived functors gives the comparison. -/
noncomputable def diagonalDerivedExtensionIsoTotalDerived (R A : Type u) [CommRing R]
    [CommRing A] [Algebra R A] [Module.Flat R A] :
    (totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).functor ≅
      diagonalDerivedExtension R A := by
  let F := ModuleCat.extendScalars.{u, u, u}
    (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)
  let : Limits.PreservesFiniteLimits F :=
    extendScalars_preservesFiniteLimits_of_flat' _ (includeLeftRingHom_flat R A)
  let : Limits.PreservesColimitsOfSize.{0, 0} F :=
    (ModuleCat.extendRestrictScalarsAdj
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).leftAdjoint_preservesColimits
  let : Limits.PreservesFiniteColimits F :=
    Limits.PreservesColimitsOfSize.preservesFiniteColimits F
  let : F.Additive := Functor.additive_of_preserves_binary_products F
  let D := totalDerivedExtensionScalars.{u, u, u}
    (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)
  have := Functor.isLeftDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
    F.mapDerivedCategory F.mapDerivedCategoryFactors
  exact Functor.leftDerivedNatIso D.functor F.mapDerivedCategory
    D.comparison F.mapDerivedCategoryFactors.hom
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) (Iso.refl _)

/-- If `g : S → A` is a retraction of `f : A → S`, then derived extension of scalars along `f`
followed by derived extension of scalars along `g` is the identity: `A ⊗ᴸ_S (K ⊗ᴸ_A S) ≅ K`. -/
noncomputable def derivedExtensionScalarsRetractionIso {A S : Type u} [CommRing A] [CommRing S]
    (f : A →+* S) (g : S →+* A) (h : g.comp f = RingHom.id A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (totalDerivedExtensionScalars.{u, u, u} g).functor.obj
      ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj K) ≅ K := by
  have e := (StacksDraft.Perfect.derivedExtensionScalarsComp.{u, u} f g).app K
  rw [h] at e
  exact e ≪≫ StacksDraft.Perfect.derivedExtensionScalarsId.{u, u} K

/-- Derived base change of `K` along the left coprojection `A → A ⊗[R] A`, followed by derived
base change along multiplication `A ⊗[R] A → A`, returns `K`. -/
noncomputable def diagonalDerivedExtensionRetractionIso (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] (K : DerivedCategory (ModuleCat.{u} A)) :
    (totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).functor.obj
      ((diagonalDerivedExtension R A).obj K) ≅ K :=
  (totalDerivedExtensionScalars.{u, u, u}
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).functor.mapIso
    (((diagonalDerivedExtensionIsoTotalDerived R A).app K).symm) ≪≫
  derivedExtensionScalarsRetractionIso _ _ (lmul'_comp_includeLeftRingHom R A) K

/-- Derived base change of `K` along the right coprojection `A → A ⊗[R] A`, followed by derived
base change along multiplication `A ⊗[R] A → A`, returns `K`. -/
noncomputable def rightCoprojectionRetractionIso (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (K : DerivedCategory (ModuleCat.{u} A)) :
    (totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).functor.obj
      ((totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom).functor.obj K) ≅ K :=
  derivedExtensionScalarsRetractionIso _ _ (lmul'_comp_includeRight R A) K

/-- Derived Hom from the diagonal `A ⊗[R] A → A` is unchanged by transporting its argument along
the flip of `A ⊗[R] A`.  Restriction of scalars along the flip is left adjoint to itself, and
restricting along the diagonal and then along the flip is restricting along the diagonal, because
the flip fixes the diagonal; so both functors are right adjoint to derived restriction of scalars
along the diagonal. -/
noncomputable def derivedHomFlipIso (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    derivedHom.{u, u} (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom ≅
      (ModuleCat.restrictScalars.{u, u, u}
          (Algebra.TensorProduct.comm R A A).toRingEquiv.toRingHom).mapDerivedCategory ⋙
        derivedHom.{u, u} (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom := by
  classical
  have hinv : ∀ x : A ⊗[R] A,
      (Algebra.TensorProduct.comm R A A).toRingEquiv.toRingHom
        ((Algebra.TensorProduct.comm R A A).toRingEquiv.toRingHom x) = x :=
    fun x => DFunLike.congr_fun (comm_comp_comm R A) x
  have a₁ := Classical.choice (restrictScalarsDerived_adj_derivedHom.{u, u}
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom)
  have aσ := CategoryTheory.Adjunction.mapDerivedCategory
    (StacksDraft.DerivedRingIso.adjRestrictScalarsOfInv
      (Algebra.TensorProduct.comm R A A).toRingEquiv.toRingHom
      (Algebra.TensorProduct.comm R A A).toRingEquiv.toRingHom hinv hinv)
  exact Adjunction.rightAdjointUniq a₁ ((a₁.comp aσ).ofNatIsoLeft
    (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u}
      (Algebra.TensorProduct.comm R A A).toRingEquiv.toRingHom
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom
      (lmul'_comp_comm R A).symm))

/-- Derived extension of scalars along the flip of `A ⊗[R] A` is restriction of scalars along the
flip, the flip being its own inverse. -/
noncomputable def flipDerivedExtensionIso (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (Y : DerivedCategory (ModuleCat.{u} (A ⊗[R] A))) :
    (totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.comm R A A).toRingEquiv.toRingHom).functor.obj Y ≅
      (ModuleCat.restrictScalars.{u, u, u}
        (Algebra.TensorProduct.comm R A A).toRingEquiv.toRingHom).mapDerivedCategory.obj Y := by
  have hinv : ∀ x : A ⊗[R] A,
      (Algebra.TensorProduct.comm R A A).toRingEquiv.toRingHom
        ((Algebra.TensorProduct.comm R A A).toRingEquiv.toRingHom x) = x :=
    fun x => DFunLike.congr_fun (comm_comp_comm R A) x
  have e := StacksDraft.DerivedRingIso.derivedExtensionScalarsRestrictIso.{u}
    (Algebra.TensorProduct.comm R A A).toRingEquiv.toRingHom
    (Algebra.TensorProduct.comm R A A).toRingEquiv.toRingHom hinv hinv
    (RingHom.id (A ⊗[R] A))
  rw [RingHom.id_comp] at e
  exact (e.app Y).symm ≪≫ StacksDraft.Perfect.derivedExtensionScalarsId.{u, u} _

/-- **Symmetry of the diagonal condition in the two coprojections.**  Derived Hom from the
diagonal into the derived base change of `L` along the *right* coprojection agrees with derived
Hom from the diagonal into the derived base change of `L` along the *left* coprojection.  The
right coprojection is the left one followed by the flip, derived extension along the flip is
restriction along it, and derived Hom from the diagonal does not see that restriction. -/
noncomputable def derivedHomIncludeRightIso (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] (L : DerivedCategory (ModuleCat.{u} A)) :
    (derivedHom.{u, u} (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
        ((totalDerivedExtensionScalars.{u, u, u}
          (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom).functor.obj L) ≅
      (derivedHom.{u, u} (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
        ((diagonalDerivedExtension R A).obj L) := by
  have cc := (StacksDraft.Perfect.derivedExtensionScalarsComp.{u, u}
    (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)
    (Algebra.TensorProduct.comm R A A).toRingEquiv.toRingHom).app L
  rw [comm_comp_includeLeftRingHom] at cc
  refine (derivedHom.{u, u}
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapIso cc.symm ≪≫
    (derivedHom.{u, u}
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapIso
        (flipDerivedExtensionIso R A _) ≪≫
    ((derivedHomFlipIso R A).app ((totalDerivedExtensionScalars.{u, u, u}
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).functor.obj L)).symm ≪≫
    (derivedHom.{u, u}
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapIso
        ((diagonalDerivedExtensionIsoTotalDerived R A).app L)

/-- The diagonal condition defining a relative dualizing complex holds for the right
coprojection as well as for the left one: this is the symmetry invoked when the uniqueness
argument transposes the two factors of `A ⊗[R] A`. -/
theorem IsRelativeDualizingComplex.diagonalDerivedHom_includeRight {R A : Type u} [CommRing R]
    [CommRing A] [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    {L : DerivedCategory (ModuleCat.{u} A)} (hL : IsRelativeDualizingComplex R A L) :
    Nonempty
      ((derivedHom.{u, u} (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
          ((totalDerivedExtensionScalars.{u, u, u}
            (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom).functor.obj L) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) :=
  ⟨derivedHomIncludeRightIso R A L ≪≫ hL.diagonalDerivedHom.some⟩

/-- For a flat ring map `R → A` of finite presentation, the `A ⊗[R] A`-module obtained from `A`
by restriction of scalars along the multiplication map `A ⊗[R] A → A` is pseudo-coherent. -/
theorem isPseudoCoherent_diagonal (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A] :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))) := by
  let : Algebra (A ⊗[R] A) A :=
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom.toAlgebra
  let : IsScalarTower R (A ⊗[R] A) A := IsScalarTower.of_algebraMap_eq (fun r => by
    show _ = (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A) _
    simp)
  let : Algebra.FinitePresentation A (A ⊗[R] A) :=
    Algebra.FinitePresentation.baseChange (R := R) (A := A) A
  let : Algebra.FinitePresentation R (A ⊗[R] A) :=
    Algebra.FinitePresentation.trans R A (A ⊗[R] A)
  have hsurj : Function.Surjective (algebraMap (A ⊗[R] A) A) := fun a =>
    ⟨a ⊗ₜ[R] 1, by
      show (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A) (a ⊗ₜ[R] 1) = a
      simp⟩
  have hA : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) := by
    refine ⟨(HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of A A), ⟨⟨0, inferInstance⟩, fun i => ?_⟩, ⟨Iso.refl _⟩⟩
    by_cases hi : i = 0
    · subst i
      show Module.Finite A A ∧ Module.Free A A
      exact ⟨inferInstance, inferInstance⟩
    · have : Subsingleton
          (((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
            (ModuleCat.of A A)).X i) :=
        ModuleCat.subsingleton_of_isZero
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of A A) i hi)
      exact ⟨Module.Finite.of_finite, Module.Free.of_subsingleton A _⟩
  have h3 := ((PseudoCoherence.pseudoCoherent_tfae_of_surjective (R := R) (B := A ⊗[R] A) (A := A)
    hsurj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) 0).1.out
      1 4).mp hA
  have halg : (algebraMap (A ⊗[R] A) A) =
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom := rfl
  rw [← halg]
  exact h3

end

end Dualizing
