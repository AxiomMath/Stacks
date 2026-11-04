module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperModuleCohomologyFinite
public import StacksFrontier.CategoryTheory.Abelian.Injective.ExtFiniteFromResolution
public import StacksFrontier.CategoryTheory.Sites.Modules.GlobalSmulFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionLinear
public import StacksFrontier.CategoryTheory.Triangulated.HomModuleFiniteTwoOutOfThree
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubobjectDirectedSupremum
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardCoherentProperSupport
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations

/-!
# Finiteness of the morphisms out of the structure sheaf on a proper algebraic space

Let `A` be a Noetherian ring and `X` a proper algebraic space over `Spec A`.  The modules on the
small étale site of `X` carry the `A`-linear structure in which `a ∈ A` acts by multiplication by
its image in the global functions of `X` (`AlgebraicGeometry.Space.modulesLinear`), and so does
`D(𝒪_X)`.  This file shows that for every coherent `𝒪_X`-module `F` and every `n` the `A`-module
`Hom_{D(𝒪_X)}(𝒪_X, F[n])` is finite: it is `Ext^n(𝒪_X, F)`, which is an `A`-linear quotient of
the cohomology of `Γ(X, I^•)` for an injective resolution `I^•` of `F`, that is of `H^n(X, F)`,
finite by Stacks 08AS.

## Main definitions

* `AlgebraicGeometry.Space.modulesLinear`: the `A`-linear structure on `𝒪_X`-modules.

## Main results

* `AlgebraicGeometry.Space.moduleFinite_ext_unit_of_isProper`: `Ext^n(𝒪_X, F)` is finite.

## References

* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
* [Stacks Project, Tag 0D0T](https://stacks.math.columbia.edu/tag/0D0T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Abelian Stacks.Cohomology.SiteModules

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)

/-- **The `A`-linear structure on the modules over an algebraic space over `Spec A`**: `a ∈ A`
acts by multiplication by its image under the structure morphism in the global functions of
`X` (`AlgebraicGeometry.Space.baseRingHom`). -/
@[instance_reducible]
def modulesLinear : Linear A (Modules.{u, u} B (Spec (.of A)) hA X hX) :=
  Stacks.SheafOfModules.linearOver _ (baseRingHom A B hA X hX)

attribute [local instance] modulesLinear

/-- The `𝒪`-modules on the small étale site of an algebraic space, at the universe of the
structure rings, have enough injectives. -/
local instance (priority := 5000) enoughInjectives_modules_ext
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    EnoughInjectives (Modules.{u, u} B S hS F hF) :=
  enoughInjectives_modules B S hS F hF

/-- Morphisms out of the structure sheaf are global sections, `A`-linearly. -/
def unitHomLinearEquiv (M : Modules.{u, u} B (Spec (.of A)) hA X hX) :
    ((linearCoyoneda A (Modules.{u, u} B (Spec (.of A)) hA X hX)).obj
        (op (SheafOfModules.unit _))).obj M ≃ₗ[A]
      (ModuleCat.restrictScalars (baseRingHom A B hA X hX)).obj
        ((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)).obj M) :=
  { toFun := fun φ => M.unitHomEquiv φ
    invFun := fun s => M.unitHomEquiv.symm s
    left_inv := M.unitHomEquiv.left_inv
    right_inv := M.unitHomEquiv.right_inv
    map_add' := fun φ ψ => by
      apply Subtype.ext
      funext U
      rfl
    map_smul' := fun a φ => by
      apply Subtype.ext
      funext U
      change (globalSmul _ (baseRingHom A B hA X hX a) _ ≫ φ).val.app U
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O).obj.obj U) =
        (baseRingHom A B hA X hX a).1 U • φ.val.app U
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O).obj.obj U)
      change φ.val.app U ((baseRingHom A B hA X hX a).1 U •
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O).obj.obj U)) =
        (baseRingHom A B hA X hX a).1 U • φ.val.app U
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O).obj.obj U)
      let φ' : SheafOfModules.unit _ ⟶ M := φ
      exact (φ'.val.app U).hom.map_smul _ _ }

/-- Morphisms out of the structure sheaf are global sections, `A`-linearly and naturally in the
target. -/
def linearCoyonedaUnitIso :
    (linearCoyoneda A (Modules.{u, u} B (Spec (.of A)) hA X hX)).obj
        (op (SheafOfModules.unit _)) ≅
      globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O) ⋙
        ModuleCat.restrictScalars (baseRingHom A B hA X hX) :=
  NatIso.ofComponents (fun M => (unitHomLinearEquiv A B hA X hX M).toModuleIso)
    (fun _ => rfl)

attribute [local instance] hasInjectiveResolutions_modules in
/-- **`Ext^n(𝒪_X, F)` is a finite `A`-module** for a coherent module `F` on a proper algebraic
space over a Noetherian ring `A`: it is an `A`-linear quotient of the degree-`n` cohomology of
`Γ(X, I^•)` for an injective resolution `I^•` of `F`, which is `Hⁿ(X, F)`, finite by
Stacks 08AS. -/
theorem moduleFinite_ext_unit_of_isProper [IsNoetherianRing A]
    (f : X ⟶ yoneda.obj (baseObject A B hA)) (hf : IsProper B (Spec (.of A)) hA f)
    (F : Modules.{u, u} B (Spec (.of A)) hA X hX) [IsCoherent B (Spec (.of A)) hA X hX F]
    [HasExt.{u + 1} (Modules.{u, u} B (Spec (.of A)) hA X hX)] (n : ℕ) :
    Module.Finite A (Ext (SheafOfModules.unit _) F n) := by
  let I := injectiveResolution F
  refine I.moduleFinite_ext_of_moduleFinite_homology n ?_
  let Γ := globalSectionsFunctor.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
  let res := ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X hX)
  have : PreservesFiniteLimits res := ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have : PreservesFiniteColimits res := ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have : res.PreservesHomology := Functor.preservesHomologyOfExact _
  have h₀ := moduleFinite_cohomology_of_isProper X hX f hf F n
  have e₁ := (Functor.rightDerivedCompIso Γ res n).app F
  have e₂ := I.isoRightDerivedObj (Γ ⋙ res) n
  have e₃ := HomologicalComplex.homologyMapIso
    ((NatIso.mapHomologicalComplex (linearCoyonedaUnitIso A B hA X hX) _).app I.cocomplex) n
  have h₁ : Module.Finite A (((Γ ⋙ res).rightDerived n).obj F) :=
    @Module.Finite.equiv _ _ _ _ _ _ _ _ h₀ e₁.symm.toLinearEquiv
  have h₂ : Module.Finite A ((((Γ ⋙ res).mapHomologicalComplex _).obj I.cocomplex).homology n) :=
    Module.Finite.equiv e₂.toLinearEquiv
  exact Module.Finite.equiv e₃.symm.toLinearEquiv

section Hypercohomology

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] isGrothendieckAbelian_modules

variable {A B hA X hX}

/-- Morphisms in `D(𝒪_X)` from an object concentrated in degrees `≤ a` to one in degrees `≥ b`
with `a < b` form a finite `A`-module, since they vanish. -/
private theorem moduleFinite_hom_of_isLE_of_isGE [IsNoetherianRing A]
    (X' Y : DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X hX)) (a b : ℤ) (hab : a < b)
    [X'.IsLE a] [Y.IsGE b] : Module.Finite A (X' ⟶ Y) := by
  have : Subsingleton (X' ⟶ Y) :=
    ⟨fun x y => (DerivedCategory.TStructure.t.zero x a b hab).trans
      (DerivedCategory.TStructure.t.zero y a b hab).symm⟩
  infer_instance

/-- **The groups `Hom_{D(𝒪_X)}(𝒪_X, F[n])` are finite `A`-modules** for a coherent `F` on a proper
algebraic space over a Noetherian ring `A`: for `n ≥ 0` this is `Ext^n(𝒪_X, F)`, and for `n < 0`
it vanishes. -/
theorem moduleFinite_hom_unit_singleFunctor [IsNoetherianRing A]
    (f : X ⟶ yoneda.obj (baseObject A B hA)) (hf : IsProper B (Spec (.of A)) hA f)
    (F : Modules.{u, u} B (Spec (.of A)) hA X hX) (hF : IsCoherent B (Spec (.of A)) hA X hX F)
    (a : ℤ) :
    Module.Finite A ((DerivedCategory.singleFunctor (Modules.{u, u} B (Spec (.of A)) hA X hX) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)) ⟶
      (DerivedCategory.singleFunctor (Modules.{u, u} B (Spec (.of A)) hA X hX) a).obj F) := by
  by_cases ha : a ≤ 0
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = -a := ⟨(-a).toNat, by omega⟩
    have : HasExt.{u + 1} (Modules.{u, u} B (Spec (.of A)) hA X hX) := HasExt.standard _
    have := hF
    have := moduleFinite_ext_unit_of_isProper A B hA X hX f hf F m
    have e := Ext.homLinearEquiv (R := A) (X := SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O))
      (Y := F) (n := m)
    have e' : ((DerivedCategory.singleFunctor (Modules.{u, u} B (Spec (.of A)) hA X hX) 0).obj
        F)⟦(m : ℤ)⟧ ≅
        (DerivedCategory.singleFunctor (Modules.{u, u} B (Spec (.of A)) hA X hX) a).obj F :=
      ((DerivedCategory.singleFunctors (Modules.{u, u} B (Spec (.of A)) hA X hX)).shiftIso
        (m : ℤ) a 0 (by omega)).app F
    exact Module.Finite.equiv (e.trans (Linear.homCongr A (Iso.refl _) e'))
  · exact moduleFinite_hom_of_isLE_of_isGE _ _ 0 a (by omega)

/-- The truncation `τ_{< d} M` of an object with coherent cohomology has coherent cohomology. -/
private theorem isCoherent_homology_truncLT_obj
    (M : DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X hX)) (d q : ℤ)
    (hM : ∀ q : ℤ, IsCoherent B (Spec (.of A)) hA X hX
      ((DerivedCategory.homologyFunctor _ q).obj M)) :
    IsCoherent B (Spec (.of A)) hA X hX
      ((DerivedCategory.homologyFunctor _ q).obj
        ((DerivedCategory.TStructure.t.truncLT d).obj M)) := by
  have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished d M
  by_cases hqd : q < d
  · have : IsIso ((DerivedCategory.homologyFunctor _ q).map
        ((DerivedCategory.TStructure.t.truncLTι d).app M)) :=
      DerivedCategory.isIso_homologyMap_mor₁_of_isGE₃ _ hT q d inferInstance hqd
    exact isCoherent_of_iso B (Spec (.of A)) hA hX
      (asIso ((DerivedCategory.homologyFunctor _ q).map
        ((DerivedCategory.TStructure.t.truncLTι d).app M))).symm (hM q)
  · exact ObjectProperty.prop_of_isZero (isCoherent.{u, u} B (Spec (.of A)) hA X hX)
      (DerivedCategory.isZero_of_isLE _ (d - 1) q (by omega))

/-- The truncation `τ_{≥ d} M` of an object with coherent cohomology has coherent cohomology. -/
private theorem isCoherent_homology_truncGE_obj
    (M : DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X hX)) (d q : ℤ)
    (hM : ∀ q : ℤ, IsCoherent B (Spec (.of A)) hA X hX
      ((DerivedCategory.homologyFunctor _ q).obj M)) :
    IsCoherent B (Spec (.of A)) hA X hX
      ((DerivedCategory.homologyFunctor _ q).obj
        ((DerivedCategory.TStructure.t.truncGE d).obj M)) := by
  have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished d M
  by_cases hqd : d ≤ q
  · have : IsIso ((DerivedCategory.homologyFunctor _ q).map
        ((DerivedCategory.TStructure.t.truncGEπ d).app M)) :=
      DerivedCategory.isIso_homologyMap_mor₂_of_isLE₁ _ hT q (d - 1) inferInstance (by omega)
    exact isCoherent_of_iso B (Spec (.of A)) hA hX
      (asIso ((DerivedCategory.homologyFunctor _ q).map
        ((DerivedCategory.TStructure.t.truncGEπ d).app M))) (hM q)
  · exact ObjectProperty.prop_of_isZero (isCoherent.{u, u} B (Spec (.of A)) hA X hX)
      (DerivedCategory.isZero_of_isGE _ d q (by omega))

/-- **The groups `Hom_{D(𝒪_X)}(𝒪_X, M[n])` are finite `A`-modules for a bounded `M` with coherent
cohomology**, concentrated in degrees `[c, c + k]`, on a proper algebraic space over a Noetherian
ring `A`. -/
private theorem moduleFinite_hom_unit_shift_of_isGE_of_isLE [IsNoetherianRing A]
    (f : X ⟶ yoneda.obj (baseObject A B hA)) (hf : IsProper B (Spec (.of A)) hA f) (k : ℕ) :
    ∀ (M : DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X hX)) (c : ℤ),
      M.IsGE c → M.IsLE (c + k) →
      (∀ q : ℤ, IsCoherent B (Spec (.of A)) hA X hX
        ((DerivedCategory.homologyFunctor _ q).obj M)) →
      ∀ n : ℤ, Module.Finite A
        ((DerivedCategory.singleFunctor (Modules.{u, u} B (Spec (.of A)) hA X hX) 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)) ⟶ M⟦n⟧) := by
  induction k with
  | zero =>
    intro M c hGE hLE hq n
    have : M.IsLE c := by simpa using hLE
    obtain ⟨F, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE M c
    have hF : IsCoherent B (Spec (.of A)) hA X hX F :=
      isCoherent_of_iso B (Spec (.of A)) hA hX ((DerivedCategory.homologyFunctor _ c).mapIso e ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso _ c).app F) (hq c)
    have := moduleFinite_hom_unit_singleFunctor f hf F hF (c - n)
    have e' : M⟦n⟧ ≅ (DerivedCategory.singleFunctor
        (Modules.{u, u} B (Spec (.of A)) hA X hX) (c - n)).obj F :=
      (shiftFunctor _ n).mapIso e ≪≫ ((DerivedCategory.singleFunctors
        (Modules.{u, u} B (Spec (.of A)) hA X hX)).shiftIso n (c - n) c (by omega)).app F
    exact Module.Finite.equiv (Linear.homCongr A (Iso.refl _) e').symm
  | succ k ih =>
    intro M c hGE hLE hq n
    rw [show c + ((k + 1 : ℕ) : ℤ) = c + (k : ℤ) + 1 by push_cast; ring] at hLE
    set d := c + (k : ℤ) + 1 with hd
    have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished d M
    have := hGE
    have := hLE
    refine Pretriangulated.moduleFinite_hom_obj₂_of_distinguished _ _
      (Pretriangulated.Triangle.shift_distinguished _ hT n) ?_ ?_
    · exact ih _ c inferInstance
        (DerivedCategory.TStructure.t.isLE_truncLT_obj M d (c + (k : ℤ)) (by omega))
        (isCoherent_homology_truncLT_obj M d · hq) n
    · exact ih _ d inferInstance
        (DerivedCategory.TStructure.t.isLE_of_le ((DerivedCategory.TStructure.t.truncGE d).obj M)
          (c + (k : ℤ) + 1) (d + (k : ℤ)) (by omega))
        (isCoherent_homology_truncGE_obj M d · hq) n

/-- **The hypercohomology `Hom_{D(𝒪_X)}(𝒪_X, N[n])` of an object with coherent cohomology bounded
below is a finite `A`-module**, on a proper algebraic space over a Noetherian ring `A`: in degree
`n` only the truncation `τ_{≤ n} N` contributes, which is bounded, and along its truncation
triangles finiteness passes from the coherent modules placed in one degree
(`AlgebraicGeometry.Space.moduleFinite_hom_unit_singleFunctor`). -/
theorem moduleFinite_hom_unit_of_derivedCategoryBPlus [IsNoetherianRing A]
    (f : X ⟶ yoneda.obj (baseObject A B hA)) (hf : IsProper B (Spec (.of A)) hA f)
    (N : DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X hX))
    (hN : DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) N)
    (n : ℤ) :
    Module.Finite A ((DerivedCategory.singleFunctor (Modules.{u, u} B (Spec (.of A)) hA X hX) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)) ⟶ N⟦n⟧) := by
  let O := (DerivedCategory.singleFunctor (Modules.{u, u} B (Spec (.of A)) hA X hX) 0).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O))
  obtain ⟨a, ha⟩ := hN.1
  have hGE : N.IsGE a := (DerivedCategory.isGE_iff N a).2 ha
  have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished (n + 1) N
  refine Pretriangulated.moduleFinite_hom_obj₂_of_distinguished O _
    (Pretriangulated.Triangle.shift_distinguished _ hT n) ?_ ?_
  · let lo := min a n
    have hGE' : ((DerivedCategory.TStructure.t.truncLT (n + 1)).obj N).IsGE lo := by
      rw [DerivedCategory.isGE_iff]
      intro q hq
      have : IsIso ((DerivedCategory.homologyFunctor _ q).map
          ((DerivedCategory.TStructure.t.truncLTι (n + 1)).app N)) :=
        DerivedCategory.isIso_homologyMap_mor₁_of_isGE₃ _ hT q (n + 1) inferInstance (by omega)
      exact (ha q (by omega)).of_iso (asIso ((DerivedCategory.homologyFunctor _ q).map
        ((DerivedCategory.TStructure.t.truncLTι (n + 1)).app N)))
    have hLE' : ((DerivedCategory.TStructure.t.truncLT (n + 1)).obj N).IsLE
        (lo + ((n - lo).toNat : ℕ)) :=
      DerivedCategory.TStructure.t.isLE_truncLT_obj N (n + 1) _ (by omega)
    exact moduleFinite_hom_unit_shift_of_isGE_of_isLE f hf _ _ lo hGE' hLE'
      (isCoherent_homology_truncLT_obj N (n + 1) · hN.2) n
  · have : ((DerivedCategory.TStructure.t.truncGE (n + 1)).obj N)⟦n⟧.IsGE 1 :=
      DerivedCategory.TStructure.t.isGE_shift _ (n + 1) n 1 (by omega)
    exact moduleFinite_hom_of_isLE_of_isGE O
      (((DerivedCategory.TStructure.t.truncGE (n + 1)).obj N)⟦n⟧) 0 1 (by omega)

end Hypercohomology

end AlgebraicGeometry.Space

end
