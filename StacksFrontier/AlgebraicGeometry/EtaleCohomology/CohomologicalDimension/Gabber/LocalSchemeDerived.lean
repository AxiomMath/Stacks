module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.LocalSchemeSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationStalkReduction
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.PullbackSystemCohomologyColimit
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictHenselizationStalkCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedGeometricStalkSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleBaseChange

/-!
# The derived functors of the sections over the local scheme at a point

Let `X` be a scheme, `η` a point and `g : Spec 𝒪_{X,η} ⟶ X`. The functor
`Ψ = Γ(Spec 𝒪_{X,η}, g⁻¹ -)` of `AlgebraicGeometry.Scheme.localSchemeSections` is the composite of
the exact functor `g⁻¹` with global sections, and `g⁻¹` carries injective abelian sheaves to
sheaves acyclic for global sections: a class of `H^p(Spec 𝒪_{X,η}, g⁻¹I)` comes from some affine
open neighbourhood `V` of `η` ([Stacks, Tag 09YQ],
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.exists_eq_etaleCohomologyMapTo_of_isLimit`),
where the restriction of `I` is again injective. Hence

`R^pΨ(𝓖) = H^p(Spec 𝒪_{X,η}, g⁻¹𝓖)`.

## Main results

* `CategoryTheory.Functor.rightDerivedCompObjIsoOfExact`: for an exact `α` carrying injectives to
  `T`-acyclic objects, `R^n(α ⋙ T)(X) ≅ R^nT(αX)`.
* `AlgebraicGeometry.Scheme.rightAcyclic_localSchemePullback`: the acyclicity of `g⁻¹I`.
* `AlgebraicGeometry.Scheme.localSchemeSectionsRightDerivedIso`: `R^pΨ(𝓖) ≅ R^pΓ(g⁻¹𝓖)`.
* `AlgebraicGeometry.Scheme.isZero_rightDerived_localSchemeSections_of_subsingleton`: the
  vanishing of `R^pΨ(𝓖)` from that of `H^p(Spec 𝒪_{X,η}, g⁻¹𝓖)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Stacks.EtaleCohomology

universe u

namespace CategoryTheory.Functor

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A B E : Type*} [Category* A] [Category* B] [Category* E] [Abelian A] [Abelian B]
  [Abelian E] [EnoughInjectives A] [EnoughInjectives B]
  (α : A ⥤ B) [α.Additive] [PreservesFiniteLimits α] [PreservesFiniteColimits α]
  (T : B ⥤ E) [T.Additive]

/-- **The derived functors of a composite with an exact functor** ([Stacks, Tag 015M]): if `α`
is exact and carries injective objects to objects right acyclic for `T`, then
`R^n(α ⋙ T)(X) ≅ R^nT(α X)`. -/
def rightDerivedCompObjIsoOfExact (hacyc : ∀ I : A, Injective I → T.rightAcyclic (α.obj I))
    (X : A) (n : ℕ) :
    ((α ⋙ T).rightDerived n).obj X ≅ (T.rightDerived n).obj (α.obj X) :=
  (rightDerivedPlusObjIso (α ⋙ T) X n).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor E (n : ℤ)).mapIso
      ((rightDerivedFunctorPlusCompIsoOfRightAcyclic α T hacyc).app _ ≪≫
        T.rightDerivedFunctorPlus.mapIso
          ((rightDerivedFunctorPlusIsoMapDerivedCategoryPlus α).app _ ≪≫
            (α.mapDerivedCategoryPlusSingleFunctorIso 0).app X)) ≪≫
    rightDerivedPlusObjIso T (α.obj X) n

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X : Scheme.{u}} (η : X)

/-- **The inverse image of an injective sheaf to the local scheme is acyclic.** For an injective
abelian sheaf `I` on `X_ét`, `H^p(Spec 𝒪_{X,η}, g⁻¹I) = 0` for `p > 0`: every class comes from an
affine open neighbourhood `V` of `η` (Stacks 09YQ), where the restriction of `I` is injective. -/
theorem subsingleton_sheafH_localSchemePullback_of_injective
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hI : Injective I) (p : ℕ)
    (hp : 0 < p) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} ((smallEtalePullbackAb (X.fromSpecStalk η)).obj I) p) := by
  obtain ⟨V₀, -⟩ := exists_affineOpenNhds_le X η ⊤
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  let W := localAffineEtaleDiagram η V₀
  let D := W ⋙ Scheme.Etale.forget X ⋙ Over.forget X
  let s : ∀ i, D.obj i ⟶ X := fun i => (W.obj i).hom
  have hs : ∀ {i j : (LocalAffineIndex η V₀)ᵒᵖ} (a : i ⟶ j), s i = D.map a ≫ s j :=
    fun a => ((W.map a).w.trans (Category.comp_id _)).symm
  refine (subsingleton_H_iff_of_iso
    ((smallEtalePullbackAbIsoEtaleAbelianInverseImage (X.fromSpecStalk η)).app I) _).2 ?_
  suffices hz : ∀ z : Sheaf.H.{u + 1, u + 1}
      ((etaleAbelianInverseImage.{u, u + 1} (X.fromSpecStalk η)).obj I) (q + 1), z = 0 from
    ⟨fun x y => (hz x).trans (hz y).symm⟩
  intro z
  obtain ⟨i, x, hx⟩ := SmallEtaleLimitCohomology.exists_eq_etaleCohomologyMapTo_of_isLimit
    (D := D) I s hs (isLimitLocalAffineCone η V₀) (X.fromSpecStalk η)
    (fun i => (localAffineCone_π_app_comp η V₀ i).symm) (q + 1) z
  have : Subsingleton (Sheaf.H.{u + 1, u + 1}
      ((etaleAbelianInverseImage.{u, u + 1} (s i)).obj I) (q + 1)) := by
    have : Etale (s i) := (W.obj i).prop
    have hJ : Injective ((smallEtalePullbackAb (s i)).obj I) :=
      (smallEtalePullbackAb (s i)).injective_obj_of_injective hI
    refine (subsingleton_H_iff_of_iso
      ((smallEtalePullbackAbIsoEtaleAbelianInverseImage (s i)).app I) _).1 ?_
    exact (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{u + 1, u,
      u + 1} _ _ _).2 (Functor.isZero_rightDerived_obj_injective_succ _ q _)
  rw [← hx, Subsingleton.elim x 0]
  exact map_zero _

/-- **`g⁻¹` carries injective sheaves to sheaves acyclic for global sections.** -/
theorem rightAcyclic_localSchemePullback (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hI : Injective I) :
    (Sheaf.Γ (Spec (X.presheaf.stalk η)).smallEtaleTopology AddCommGrpCat.{u + 1}).rightAcyclic
      ((smallEtalePullbackAb (X.fromSpecStalk η)).obj I) := by
  rw [CategoryTheory.rightAcyclic_iff_isZero_rightDerived]
  intro p hp
  exact (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{u + 1, u,
    u + 1} _ _ _).1 (subsingleton_sheafH_localSchemePullback_of_injective η I hI p hp)

/-- **The derived functors of the sections over the local scheme**: `R^pΨ(𝓖) ≅ R^pΓ(g⁻¹𝓖)`. -/
def localSchemeSectionsRightDerivedIso (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (p : ℕ) :
    ((localSchemeSections η).rightDerived p).obj G ≅
      ((Sheaf.Γ (Spec (X.presheaf.stalk η)).smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived
        p).obj ((smallEtalePullbackAb (X.fromSpecStalk η)).obj G) :=
  Functor.rightDerivedCompObjIsoOfExact _ _ (rightAcyclic_localSchemePullback η) G p

/-- **Vanishing of `R^pΨ(𝓖)` from that of `H^p(Spec 𝒪_{X,η}, g⁻¹𝓖)`.** -/
theorem isZero_rightDerived_localSchemeSections_of_subsingleton
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℕ)
    (h : Subsingleton
      (Sheaf.H.{u + 1, u + 1} ((smallEtalePullbackAb (X.fromSpecStalk η)).obj G) p)) :
    IsZero (((localSchemeSections η).rightDerived p).obj G) :=
  ((Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{u + 1, u,
    u + 1} _ _ _).1 h).of_iso (localSchemeSectionsRightDerivedIso η G p)

end AlgebraicGeometry.Scheme

end
