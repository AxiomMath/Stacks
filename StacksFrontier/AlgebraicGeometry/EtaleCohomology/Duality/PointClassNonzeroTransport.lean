module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PointClassNonzeroPointwise
public import StacksFrontier.AlgebraicGeometry.Curves.PrescribedLowCohomologyBaseChangeGeneral
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingDivisorOneStepReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCompactSupportComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExt

/-!
# A point over a separably closed field is the spectrum of the field

Let `k` be separably closed and `P` irreducible and smooth of relative dimension zero over `k`.
Then `P → Spec k` has a section `s : Spec k → P` which is an isomorphism
(`AlgebraicGeometry.exists_isIso_section_of_smoothOfRelativeDimension_zero`): `P` has a `k`-point,
which is a closed immersion (a section over a point), surjective (`P` is a single point) onto the
reduced scheme `P`.

The class of a point is therefore unchanged when the point is replaced by `Spec k`
(`Stacks.EtaleCohomology.pointClassNonzeroAt_of_comp_isIso`), the direct image of the constant
sheaf along an isomorphism being the constant sheaf
(`Stacks.EtaleCohomology.unitSheafDirectImageIsoOfIsIso`). This reduces the class of a point,
in the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), to `k`-points
`Spec k → W`, whose fibres under an elementary fibration are curves over `k`.

## Main results

* `AlgebraicGeometry.exists_isIso_section_of_smoothOfRelativeDimension_zero`.
* `Stacks.EtaleCohomology.unitSheafDirectImageIsoOfIsIso`.
* `Stacks.EtaleCohomology.pointClassNonzeroAt_of_comp_isIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **A point over a separably closed field is the spectrum of the field**: an irreducible `P`
smooth of relative dimension zero over a separably closed `k` has a section `Spec k → P` of its
structure morphism which is an isomorphism. -/
theorem exists_isIso_section_of_smoothOfRelativeDimension_zero {k : Type u} [Field k]
    [IsSepClosed k] {P : Scheme.{u}} (π : P ⟶ Spec (.of k)) [SmoothOfRelativeDimension 0 π]
    [IrreducibleSpace P] : ∃ s : Spec (.of k) ⟶ P, s ≫ π = 𝟙 _ ∧ IsIso s := by
  have : Smooth π := SmoothOfRelativeDimension.smooth 0 π
  have : Nonempty P := IrreducibleSpace.toNonempty
  have := Stacks.EtaleCohomology.subsingleton_of_smoothOfRelativeDimension_zero π
  obtain ⟨s, hs, -⟩ := exists_section_of_isSepClosed π
  have : IsClosedImmersion s := isClosedImmersion_of_comp_eq_id π s hs
  have : Surjective s := ⟨fun x => ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩⟩
  have : IsReduced P := Stacks.SectionsVanishingOnSubscheme.isReduced_of_smooth_over_field k π
  exact ⟨s, hs, isIso_of_isClosedImmersion_of_surjective s⟩

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

open ExtensionTorsor

attribute [local instance] HasDerivedCategory.standard

-- `Stacks.EtaleCohomology.PointClassNonzeroAt` reads `ZMod ℓ` as a ring through `ZMod.commRing`.
attribute [-instance] ZMod.instField

/-- **Direct image along an isomorphism is inverse image along the inverse**: `e_*` and
`(e⁻¹)^{-1}` are both left adjoint to `(e⁻¹)_*`, the direct images along `e` and `e⁻¹` being
inverse equivalences. -/
def etaleModuleDirectImageIsoInverseImageOfIsIso (Λ : Type) [CommRing Λ] {A B : Scheme.{u}}
    (e : A ⟶ B) [IsIso e] :
    etaleModuleInverseImage.{u, 0} Λ (inv e) ≅ etaleModuleDirectImage.{u, 0} Λ e :=
  let E : EtaleModules.{u, 0} Λ A ≌ EtaleModules.{u, 0} Λ B :=
    CategoryTheory.Equivalence.mk (etaleModuleDirectImage.{u, 0} Λ e)
      (etaleModuleDirectImage.{u, 0} Λ (inv e))
      ((etaleModuleDirectImageIdIso Λ A).symm ≪≫
        (etaleModuleDirectImageComp Λ e (inv e) (𝟙 A) (IsIso.hom_inv_id e).symm).symm)
      (etaleModuleDirectImageComp Λ (inv e) e (𝟙 B) (IsIso.inv_hom_id e).symm ≪≫
        etaleModuleDirectImageIdIso Λ B)
  Adjunction.leftAdjointUniq (etaleModuleInverseImageAdj.{u, 0} Λ (inv e)) E.toAdjunction

/-- **The direct image of the constant sheaf along an isomorphism is the constant sheaf.** -/
def unitSheafDirectImageIsoOfIsIso (N : ℕ) {A B : Scheme.{u}} (e : A ⟶ B) [IsIso e] :
    (etaleModuleDirectImage.{u, 0} (ZMod N) e).obj (unitSheaf (X := A) N) ≅
      unitSheaf (X := B) N :=
  ((etaleModuleDirectImageIsoInverseImageOfIsIso (ZMod N) e).app _).symm ≪≫
    (etaleModuleInverseImageConstantIso.{u, 0} (ZMod N) (inv e)).app
      (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N)))

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]

/-- **The class of a point does not change along an isomorphism of the point**: for
`s : P' ≅ P`, if the class of `s ≫ i` is nonzero, so is the class of `i`. -/
theorem pointClassNonzeroAt_of_comp_isIso (e : ℕ) {W : Scheme.{u}} (f : W ⟶ Spec (.of k))
    (jc : CompactificationOf (Over.mk f)) {N P P' : Scheme.{u}} (n : N ⟶ W) [IsOpenImmersion n]
    (i : P ⟶ N) (s : P' ⟶ P) [IsIso s] (h : PointClassNonzeroAt ℓ e f jc n (s ≫ i)) :
    PointClassNonzeroAt ℓ e f jc n i := by
  have hℓ : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  obtain ⟨γ₀, z, hz⟩ := h
  let L := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)
  let φ : (etaleModuleDirectImage.{u, 0} (ZMod ℓ) (s ≫ i)).obj (unitSheaf (X := P') ℓ) ≅
      (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := P) ℓ) :=
    ((etaleModuleDirectImageComp (ZMod ℓ) s i (s ≫ i) rfl).app _).symm ≪≫
      (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).mapIso (unitSheafDirectImageIsoOfIsIso ℓ s)
  have key : ∀ {X₁ X₂ : EtaleModules.{u, 0} (ZMod ℓ) N} (a : X₁ ⟶ X₂)
      (γ : Ext X₂ ((etaleModuleRestriction.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
          (unitSheaf (X := W) ℓ))) (2 * e)),
      Stacks.ExtAdjunction.extMap (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ)
          (n ≫ jc.immersion)) _ _ (2 * e) ((Ext.mk₀ a).comp γ (zero_add _)) =
        (Ext.mk₀ (L.map a)).comp (Stacks.ExtAdjunction.extMap
          (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)) _ _ (2 * e) γ)
          (zero_add _) := by
    intro X₁ X₂ a γ
    rw [Stacks.ExtAdjunction.extMap_apply, Stacks.ExtAdjunction.extMap_apply,
      Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero]
  refine ⟨(Ext.mk₀ φ.inv).comp γ₀ (zero_add _), z.comp (Ext.mk₀ (L.map φ.hom)) (add_zero _), ?_⟩
  rw [key, Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀_assoc, ← Functor.map_comp,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Ext.mk₀_id_comp]
  exact hz

end Stacks.EtaleCohomology

end
