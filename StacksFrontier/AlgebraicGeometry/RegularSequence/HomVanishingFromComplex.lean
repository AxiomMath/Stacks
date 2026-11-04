module

public import StacksFrontier.AlgebraicGeometry.RegularSequence.ExtLocalToGlobal
public import StacksFrontier.Algebra.Homology.DerivedCategory.HomVanishingFromCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedExtOnAnOpen

/-!
# Morphisms from a complex to a module, from local `Ext` vanishing of its cohomology

Let `X` be a scheme, `K` an object of `D(𝒪_X)` and `E` an `𝒪_X`-module.  Suppose that around
every point there are arbitrarily small opens `V` over which `K` has cohomology in a bounded range
`[a, a + d]` and each cohomology sheaf satisfies `Ext^k(H^q(K)|_V, E|_V) = 0` for `0 ≤ k ≤ q`.
Then `Hom_{D(𝒪_X)}(K, E[0]) = 0`.

This is the form in which [Stacks, Tag 0G5J] uses the vanishing of `Ext` along a regular
immersion ([Stacks, Tag 0G5I]): the cone of `Ω^a_{X/S} ⟶ Rb_*Ω^a_{X'/S}` is bounded only locally
on `X`, its cohomology sheaves are pushed forward from the centre, and the codimension of the
centre — which bounds both the cohomological range and the degrees of the vanishing — varies over
`X`.

## Main results

* `Stacks.SheafOfModules.subsingleton_hom_singleFunctor_of_locally_homology`: the statement
  above.

## Implementation notes

The argument is that of `Stacks.SheafOfModules.subsingleton_shiftedHom_single_of_locally_restrict`,
with a complex in place of a single sheaf: choose a complex representing `K` and a K-injective
resolution of `E`; the internal Hom complex between them has no cohomology in degrees `≤ 0`
locally, hence none at all there, hence no global morphisms
(`Stacks.SheafOfModules.subsingleton_shiftedHom_of_locally_subsingleton`).  The local statement is
proved on the slice site over `V`, where the restriction of the representing complex is bounded
with the restricted cohomology sheaves, by
`Stacks.DerivedCategoryHomVanishing.subsingleton_hom_shift_of_homology`; only the `Ext` groups
of the cohomology sheaves, which are single sheaves, are translated to the open subscheme `V`.

## References

* [Stacks Project, Tag 0G5J](https://stacks.math.columbia.edu/tag/0G5J)
* [Stacks Project, Tag 0G5I](https://stacks.math.columbia.edu/tag/0G5I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

-- `_root_` is needed: inside `namespace Stacks.SheafOfModules` an unqualified
-- `open AlgebraicGeometry` picks up `Stacks.AlgebraicGeometry` instead.
open _root_.AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

section Global

/-- If `A ≅ A'` and `B ≅ B'`, then `A ⟶ B` is a subsingleton as soon as `A' ⟶ B'` is. -/
private theorem subsingleton_hom_of_iso {C : Type*} [Category C] {A A' B B' : C}
    (eA : A ≅ A') (eB : B ≅ B') (h : Subsingleton (A' ⟶ B')) : Subsingleton (A ⟶ B) :=
  (Equiv.subsingleton_congr (Iso.homCongr eA eB)).mpr h

open Stacks.Cohomology.ModuleSections

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj A).Additive]
  [∀ K₁ K₂ : CochainComplex (_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ,
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- **Local to global for morphisms from a complex to a module, in the slice model.**  Let `K`
be a complex of `𝒪_X`-modules and `E` an `𝒪_X`-module.  Suppose that on a family of opens which
is a basis near every point, the restriction of `K` to the slice site has bounded cohomology, and
each of its cohomology sheaves `H^q` has no nonzero degree-`k` morphism to the restriction of
`E` for `k ≤ q`.  Then `K` has no nonzero morphism to `E[0]`. -/
theorem subsingleton_hom_singleFunctor_of_locally_homology_over
    (K : CochainComplex (StructureSheafModules Rc) ℤ) (E : StructureSheafModules Rc)
    (P : Opens X → Prop)
    (hP : ∀ (x : X) (U : Opens X), x ∈ U → ∃ V : Opens X, x ∈ V ∧ V ≤ U ∧ P V)
    (hlocal : ∀ U, P U → ∃ (a : ℤ) (d : ℕ),
      (DerivedCategory.Q.obj (restrictComplex Rc K U)).IsGE a ∧
      (DerivedCategory.Q.obj (restrictComplex Rc K U)).IsLE (a + d) ∧
      ∀ q : ℤ, a ≤ q → q ≤ a + d → ∀ k : ℤ, k ≤ q →
        Subsingleton (ShiftedHom
          ((DerivedCategory.singleFunctor _ 0).obj ((DerivedCategory.homologyFunctor _ q).obj
            (DerivedCategory.Q.obj (restrictComplex Rc K U))))
          ((DerivedCategory.singleFunctor _ 0).obj
            ((_root_.SheafOfModules.overFunctor (structureSheaf Rc) U).obj E)) k)) :
    Subsingleton (DerivedCategory.Q.obj K ⟶
      (DerivedCategory.singleFunctor (StructureSheafModules Rc) 0).obj E) := by
  obtain ⟨R, -, hRGE⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE (0 : ℤ)
    ((CochainComplex.singleFunctor (StructureSheafModules Rc) 0).obj E)
  have hinj : ∀ n, Injective (R.cocomplex.X n) := R.injective
  have hstrict : R.cocomplex.IsStrictlyGE 0 := hRGE
  have _ : R.cocomplex.IsKInjective := CochainComplex.isKInjective_of_injective R.cocomplex 0
  have _ : QuasiIso R.ι := R.quasiIso
  let eM : DerivedCategory.Q.obj R.cocomplex ≅
      (DerivedCategory.singleFunctor (StructureSheafModules Rc) 0).obj E :=
    (asIso (DerivedCategory.Q.map R.ι)).symm
  have hloc : ∀ U : Opens X, P U → ∀ n < (1 : ℤ),
      Subsingleton (ShiftedHom (DerivedCategory.Q.obj (restrictComplex Rc K U))
        (DerivedCategory.Q.obj (restrictComplex Rc (R.cocomplex⟦((0 : ℕ) : ℤ)⟧) U)) n) := by
    intro U hU n hn
    obtain ⟨a, d, hGE, hLE, hext⟩ := hlocal U hU
    let F := _root_.SheafOfModules.overFunctor (structureSheaf Rc) U
    let _ : PreservesFiniteLimits F := LocalCokernel.overFunctor_preservesFiniteLimits U
    let _ : PreservesFiniteColimits F := LocalCokernel.overFunctor_preservesFiniteColimits U
    let _ : F.Additive := ⟨fun {_ _} _ _ => rfl⟩
    let eI := mapComplexSingleIso F R.cocomplex E eM
    let eIq : DerivedCategory.Q.obj (restrictComplex Rc (R.cocomplex⟦((0 : ℕ) : ℤ)⟧) U) ≅
        ((DerivedCategory.singleFunctor _ 0).obj (F.obj E))⟦((0 : ℕ) : ℤ)⟧ :=
      DerivedCategory.Q.mapIso
          (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso ((0 : ℕ) : ℤ)).app
            R.cocomplex) ≪≫
        (DerivedCategory.Q.commShiftIso ((0 : ℕ) : ℤ)).app _ ≪≫
        (shiftFunctor _ ((0 : ℕ) : ℤ)).mapIso eI
    refine subsingleton_hom_of_iso (Iso.refl _)
      ((shiftFunctor _ n).mapIso eIq ≪≫
        ((shiftFunctorAdd' _ ((0 : ℕ) : ℤ) n n (by simp)).app
          ((DerivedCategory.singleFunctor _ 0).obj (F.obj E))).symm) ?_
    refine Stacks.DerivedCategoryHomVanishing.subsingleton_hom_shift_of_homology _ 0 d _ a
      hGE hLE (fun q hq₁ hq₂ m hm => ?_) n (by omega)
    rw [Stacks.DerivedCategoryHomVanishing.subsingleton_hom_singleFunctor_shift_iff]
    exact hext q hq₁ hq₂ (m + q) (by omega)
  have hglob := subsingleton_shiftedHom_of_locally_subsingleton Rc K R.cocomplex 0 P hP hloc
  exact subsingleton_hom_of_iso (Iso.refl _) eM.symm
    (subsingleton_hom_of_iso (Iso.refl _)
      ((shiftFunctorZero _ ℤ).app (DerivedCategory.Q.obj R.cocomplex)).symm hglob)

end Global

section SchemeCase

attribute [local instance]
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits

variable (X : Scheme.{u})

/-- **Local to global for morphisms from a complex to a module.**  Let `K` be an object of
`D(𝒪_X)` and `E` an `𝒪_X`-module.  Suppose the opens `V` with the following property form a
family which is a basis near every point: there are `a : ℤ` and `d : ℕ` such that the cohomology
sheaves of `K` vanish on `V` outside `[a, a + d]`, and for `q ∈ [a, a + d]` and `0 ≤ k ≤ q`,
`Ext^k(H^q(K)|_V, E|_V) = 0`.  Then there is no nonzero morphism `K ⟶ E[0]` in `D(𝒪_X)`. -/
theorem subsingleton_hom_singleFunctor_of_locally_homology
    (K : DerivedCategory X.Modules) (E : X.Modules) (P : X.Opens → Prop)
    (hP : ∀ (x : X) (U : X.Opens), x ∈ U → ∃ V : X.Opens, x ∈ V ∧ V ≤ U ∧ P V)
    (hlocal : ∀ U, P U → ∃ (a : ℤ) (d : ℕ),
      (∀ q : ℤ, (q < a ∨ a + d < q) →
        IsZero (((DerivedCategory.homologyFunctor X.Modules q).obj K).restrict U.ι)) ∧
      ∀ q : ℤ, a ≤ q → q ≤ a + d → ∀ k : ℕ, (k : ℤ) ≤ q →
        Subsingleton (ShiftedHom
          ((DerivedCategory.singleFunctor U.toScheme.Modules 0).obj
            (((DerivedCategory.homologyFunctor X.Modules q).obj K).restrict U.ι))
          ((DerivedCategory.singleFunctor U.toScheme.Modules 0).obj (E.restrict U.ι)) (k : ℤ))) :
    Subsingleton (K ⟶ (DerivedCategory.singleFunctor X.Modules 0).obj E) := by
  have _ : (Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).Additive :=
    Tensor.sheafTensor_additive.{u, u, u, u, u} (J := Opens.grothendieckTopology (X : TopCat.{u}))
      X.sheaf
  have _ : ∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj A).Additive :=
    Tensor.sheafTensor_obj_additive.{u, u, u, u, u}
      (J := Opens.grothendieckTopology (X : TopCat.{u})) X.sheaf
  have _ : ∀ K₁ K₂ : CochainComplex
      (_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} X.sheaf)) ℤ,
      HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor X.sheaf)
        (ComplexShape.up ℤ) := fun K₁ K₂ =>
    Tensor.hasMapBifunctor_sheafTensor (J := Opens.grothendieckTopology (X : TopCat.{u}))
      X.sheaf K₁ K₂
  let K' : CochainComplex X.Modules ℤ := DerivedCategory.Q.objPreimage K
  let eK : DerivedCategory.Q.obj K' ≅ K := DerivedCategory.Q.objObjPreimageIso K
  refine subsingleton_hom_of_iso eK.symm (Iso.refl _) ?_
  refine subsingleton_hom_singleFunctor_of_locally_homology_over X.sheaf K' E P hP ?_
  intro U hU
  obtain ⟨a, d, hzero, hext⟩ := hlocal U hU
  let F := _root_.SheafOfModules.overFunctor X.ringCatSheaf U
  let N : ℤ → X.Modules := fun q => (DerivedCategory.homologyFunctor X.Modules q).obj K
  let eH : ∀ q : ℤ, (DerivedCategory.homologyFunctor _ q).obj
      (DerivedCategory.Q.obj (restrictComplex X.sheaf K' U)) ≅ F.obj (N q) := fun q =>
    (DerivedCategory.homologyFunctorFactors _ q).app _ ≪≫
      homologyMapHomologicalComplexIso F K' q ≪≫
      F.mapIso (((DerivedCategory.homologyFunctorFactors _ q).app K').symm ≪≫
        (DerivedCategory.homologyFunctor _ q).mapIso eK)
  have hzero' : ∀ q : ℤ, (q < a ∨ a + d < q) → IsZero (F.obj (N q)) := fun q hq =>
    (Functor.map_isZero (Scheme.Modules.overEquiv U).inverse
      ((hzero q hq).of_iso ((Scheme.Modules.overFunctorEquiv U).app (N q)))).of_iso
      ((Scheme.Modules.overEquiv U).unitIso.app _)
  refine ⟨a, d, ?_, ?_, fun q hq₁ hq₂ k hk => ?_⟩
  · rw [DerivedCategory.isGE_iff]
    exact fun q hq => (hzero' q (Or.inl hq)).of_iso (eH q)
  · rw [DerivedCategory.isLE_iff]
    exact fun q hq => (hzero' q (Or.inr hq)).of_iso (eH q)
  · refine subsingleton_hom_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso (eH q))
      (Iso.refl _) ?_
    rcases lt_or_ge k 0 with hneg | hpos
    · exact subsingleton_shiftedHom_single_of_neg _ _ _ hneg
    · obtain ⟨k', hk'⟩ := Int.eq_ofNat_of_zero_le hpos
      rw [hk']
      exact subsingleton_shiftedHom_over_of_restrict X U (N q) E k'
        (hext q hq₁ hq₂ k' (by omega))

end SchemeCase

end Stacks.SheafOfModules

end
