module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.GaloisFieldExtension
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact

/-!
# Galois descent of an invertible module

Let `f : X ⟶ Y` be a surjective finite étale morphism with an action of a finite group `G` whose
cover comparison is an isomorphism. Every Galois descent datum for `f` is the pullback of a
quasi-coherent module on `Y`, and one whose underlying module is invertible is the pullback of an
invertible module on `Y`.

## Main definitions

* `Stacks.Descent.galoisDescentComparison`: the comparison functor taking a quasi-coherent module
  `N` on `Y` to `f^* N` with its canonical Galois isomorphisms.
* `Stacks.Descent.galoisModuleIso`: the isomorphism of underlying modules induced by an
  isomorphism of Galois descent data.
* `Stacks.Descent.galoisFpqcCover`: a surjective finite étale `f : X ⟶ Y` as a one-element fpqc
  covering of `Y`.

## Main results

* `Stacks.Descent.galoisDescentComparison_obj_module`: the module underlying the value of the
  comparison functor at `N` is `f^* N`.
* `Stacks.Descent.exists_isQuasicoherent_pullback_iso_of_galoisDescentData`: every Galois descent
  datum is the pullback of a quasi-coherent module on `Y`.
* `Stacks.Descent.exists_isInvertible_pullback_iso_of_galoisDescentData`: a Galois descent datum
  whose underlying module is invertible is the pullback of an invertible module on `Y`.
* `Stacks.Descent.exists_isInvertible_pullback_iso_of_galoisDescentData_baseChange`: the same for
  the base change of a scheme along a finite Galois field extension.

## References

* [Stacks Project, Tag 0CDR](https://stacks.math.columbia.edu/tag/0CDR)
* [Stacks Project, Tag 0D1V](https://stacks.math.columbia.edu/tag/0D1V)
* [Stacks Project, Tag 023D](https://stacks.math.columbia.edu/tag/023D)
* [Stacks Project, Tag 05B2](https://stacks.math.columbia.edu/tag/05B2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

namespace Stacks.Descent

variable {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}} (f : X ⟶ Y)
  (a : Gᵐᵒᵖ →* Aut (Over.mk f))

/-- The comparison functor taking a quasi-coherent module `N` on `Y` to the pullback `f^* N`
equipped with the canonical isomorphisms `f^* N ≅ f_σ^* f^* N`. -/
def galoisDescentComparison :
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory ⥤ GaloisDescentData G f a :=
  canonicalDescentFunctor (galoisFamily f) ⋙ galoisDescentFunctor G f a

omit [Finite G] in
/-- The module underlying the value of `Stacks.Descent.galoisDescentComparison f a` at `N` is the
pullback `f^* N`. -/
@[simp]
theorem galoisDescentComparison_obj_module
    (N : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory) :
    ((galoisDescentComparison f a).obj N).module = (Scheme.Modules.pullback f).obj N.obj := rfl

/-- An isomorphism of Galois descent data induces an isomorphism of the underlying modules. -/
def galoisModuleIso {A B : GaloisDescentData G f a} (e : A ≅ B) : A.module ≅ B.module where
  hom := e.hom.hom
  inv := e.inv.hom
  hom_inv_id := congrArg GaloisDescentData.Hom.hom e.hom_inv_id
  inv_hom_id := congrArg GaloisDescentData.Hom.hom e.inv_hom_id

/-- For `f` surjective finite étale with cover comparison an isomorphism, the comparison functor
`Stacks.Descent.galoisDescentComparison f a` is an equivalence of categories. -/
instance galoisDescentComparison_isEquivalence [IsFinite f] [Etale f] [Surjective f]
    [IsIso (galoisCoverComparison f a)] : (galoisDescentComparison f a).IsEquivalence := by
  have := isEquivalence_canonicalDescentFunctor_galoisFamily f
  exact inferInstanceAs ((canonicalDescentFunctor (galoisFamily f) ⋙
    galoisDescentFunctor G f a).IsEquivalence)

/-- Every Galois descent datum for a surjective finite étale `f : X ⟶ Y` carrying an action of a
finite group `G` whose cover comparison is an isomorphism is the pullback of a quasi-coherent
module on `Y`. -/
theorem exists_isQuasicoherent_pullback_iso_of_galoisDescentData
    [IsFinite f] [Etale f] [Surjective f] [IsIso (galoisCoverComparison f a)]
    (A : GaloisDescentData G f a) :
    ∃ N : Y.Modules, N.IsQuasicoherent ∧
      Nonempty ((Scheme.Modules.pullback f).obj N ≅ A.module) :=
  ⟨((galoisDescentComparison f a).objPreimage A).obj,
    ((galoisDescentComparison f a).objPreimage A).property,
    ⟨galoisModuleIso f a ((galoisDescentComparison f a).objObjPreimageIso A)⟩⟩

/-- A surjective finite étale morphism, as a one-element fpqc covering of its target. -/
def galoisFpqcCover [IsFinite f] [Etale f] [Surjective f] :
    Y.Cover.{0} Scheme.fpqcPrecoverage where
  I₀ := PUnit.{1}
  X _ := X
  f := galoisFamily f
  mem₀ := ofArrows_galoisFamily_mem_fpqcPrecoverage f

/-- A Galois descent datum whose underlying module is invertible is the pullback of an
invertible quasi-coherent module on `Y`. -/
theorem exists_isInvertible_pullback_iso_of_galoisDescentData
    [IsFinite f] [Etale f] [Surjective f] [IsIso (galoisCoverComparison f a)]
    (A : GaloisDescentData G f a)
    (hA : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A.module) :
    ∃ N : Y.Modules, N.IsQuasicoherent ∧
      Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N ∧
        Nonempty ((Scheme.Modules.pullback f).obj N ≅ A.module) := by
  obtain ⟨N, hN, ⟨e⟩⟩ := exists_isQuasicoherent_pullback_iso_of_galoisDescentData f a A
  exact ⟨N, hN, Stacks.Picard.isInvertible_of_pullback_fpqcCover N hN (galoisFpqcCover f)
    fun _ ↦ Stacks.Picard.isInvertible_of_iso e.symm hA, ⟨e⟩⟩

/-- Let `K/k` be a finite Galois extension and let `Z` be a scheme over `k`. A Galois descent
datum on the base change `Z_K` whose underlying module is invertible is the pullback of an
invertible quasi-coherent module on `Z`. -/
theorem exists_isInvertible_pullback_iso_of_galoisDescentData_baseChange (k K : Type u) [Field k]
    [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (Z : Over (Spec (.of k)))
    (A : GaloisDescentData (K ≃ₐ[k] K) (baseChangeProjection k K Z)
      (baseChangeOverAction k K Z))
    (hA : Stacks.SheafOfModules.IsInvertible (SchemeOver.baseChange k K Z).presheaf
      (SchemeOver.baseChange k K Z).ringCatSheaf.2 A.module) :
    ∃ N : Z.left.Modules, N.IsQuasicoherent ∧
      Stacks.SheafOfModules.IsInvertible Z.left.presheaf Z.left.ringCatSheaf.2 N ∧
        Nonempty ((Scheme.Modules.pullback (baseChangeProjection k K Z)).obj N ≅ A.module) := by
  have := isFinite_baseChangeProjection k K Z
  have := etale_baseChangeProjection k K Z
  have := surjective_baseChangeProjection k K Z
  have := isIso_galoisCoverComparison_baseChange k K Z
  exact exists_isInvertible_pullback_iso_of_galoisDescentData (baseChangeProjection k K Z)
    (baseChangeOverAction k K Z) A hA

end Stacks.Descent

end
