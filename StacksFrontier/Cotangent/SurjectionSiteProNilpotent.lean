module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.AbelianDerivedColimitHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.LeftDerivedColimForget
public import StacksFrontier.Cotangent.SurjectionSiteAugmentationPowVanishing
public import StacksFrontier.Cotangent.SurjectionSiteAugmentationStructureModule
public import StacksFrontier.Cotangent.SurjectionSiteGlobalChain
public import StacksFrontier.Cotangent.SurjectionSiteLocalSections
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactorOrthogonal

/-!
# Pro-nilpotence of the augmentation filtration, for a surjective ring map

This file proves `CommAlgCat.SmallPolynomialAugmentationProNilpotent` — the `hpro` half of the
footnote vanishing of [Stacks, Tag 08RF] — for a surjective `A → B`, with `c = k²`.

## How large `c` must be

`CommAlgCat.SmallPolynomialAugmentationProNilpotent` quantifies `c` existentially, so any `c`
that works discharges it.  The one taken here is `c = k²`: the chain `𝒦^{n+k²} ⊆ ⋯ ⊆ 𝒦ⁿ` is cut
into `k` steps of size `k`, and [Stacks, Tag 08Q2] (`main_covariant`) asks of the `j`-th step
only that it be zero on `H^{-j}`, which the local claim supplies for `j` below the step size.
Steps of size `k` therefore suffice for all `j < k`, and `k` of them give `c = k²`.  A smaller
`c` is not available on this route: over `𝒪(U) = A[E]` the second variable of the local `Tor` is
`𝔪ᵐ ⊗_A B` and not `𝔪ᵐ`, so [Stacks, Tag 08RE] does not kill the step in *every* degree, only
below its size; it would over `Ō(U) = B[E]`, but that is the change of rings
[Stacks, Tag 08YT] records as unavailable.

## Proof outline

The global half is `Stacks.ChaoticSite.homology_derivedColimit_tensor_map_eq_zero_of_objectwise`:
`main_covariant` on a chain of projective resolutions of the `𝒦ᵐ`, the right `t`-exactness of
`Lπ_!`, and the telescoping of the comparison back to the inclusion. For a surjective `A → B` an
objectwise vanishing need only be checked where the point is `0`
(`CommAlgCat.app_eq_zero_of_forall_smallSitePoint_eq_zero`). The objectwise input is the local
claim `CommAlgCat.tor'_map_app_smallPolynomialAugmentationIdealPowStructureOfLE_eq_zero` on
`Tor'_j^{𝒪(U)}(-, M)`, read on `L_j(B̲(U) ⊗_{𝒪(U)} -)` through
`Stacks.NoncommChangeOfRings.leftDerived_extendScalars_map_eq_zero_of_tor'`. [Stacks, Tag 08QJ]
at `𝒦ⁿ` (`CommAlgCat.isIso_derivedColimitTensorComparison_smallPolynomialAugmentationIdealPow`)
transports the vanishing across the change of coefficients, and
`Stacks.ChaoticSite.AbelianValued.leftDerivedColim_map_eq_zero` and
`Stacks.ChaoticSite.leftDerivedColim_map_eq_zero_of_forget` bring it down to `L_i colim` at
`B`-module coefficients, which is `hpro`.

## Main results

* `Stacks.NoncommChangeOfRings.leftDerived_extendScalars_map_eq_zero_of_tor'`: the bridge from
  `Tor'` to the left derived functors of extension of scalars.
* `CommAlgCat.smallPolynomialAugmentationProNilpotent`: **`hpro`.**

## References

* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
* [Stacks Project, Tag 08QJ](https://stacks.math.columbia.edu/tag/08QJ)
* [Stacks Project, Tag 08Q2](https://stacks.math.columbia.edu/tag/08Q2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

open StacksDraft.PolynomialLocalComplex (eq_zero_of_iso_comp_comp_iso
  homologyMap_eq_zero_of_map_eq_zero)

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.NoncommChangeOfRings

/-! ### From `Tor'` to the left derived functors of extension of scalars -/

section Bridge

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [Abelian C] [Abelian D]
  [Abelian E] [EnoughProjectives C]

/-- Vanishing of a left derived map transfers along a natural isomorphism of functors. -/
theorem leftDerived_map_eq_zero_of_natIso {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G)
    (j : ℕ) {X Y : C} (φ : X ⟶ Y) (h : (G.leftDerived j).map φ = 0) :
    (F.leftDerived j).map φ = 0 := by
  have hiso : IsIso (NatTrans.leftDerived e.hom j) :=
    ⟨⟨NatTrans.leftDerived e.inv j, by
        rw [← NatTrans.leftDerived_comp, e.hom_inv_id, NatTrans.leftDerived_id],
      by rw [← NatTrans.leftDerived_comp, e.inv_hom_id, NatTrans.leftDerived_id]⟩⟩
  have hnat := (NatTrans.leftDerived e.hom j).naturality φ
  rw [h, comp_zero] at hnat
  exact zero_of_comp_mono ((NatTrans.leftDerived e.hom j).app Y) hnat

/-- Vanishing of a left derived map is reflected by a faithful exact post-composition. -/
theorem leftDerived_map_eq_zero_of_comp (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive]
    [G.PreservesHomology] [G.Faithful] (j : ℕ) {X Y : C} (φ : X ⟶ Y)
    (h : ((F ⋙ G).leftDerived j).map φ = 0) : (F.leftDerived j).map φ = 0 := by
  have hcomm := ProjectiveResolution.lift_commutes φ (ProjectiveResolution.of X)
    (ProjectiveResolution.of Y)
  generalize ProjectiveResolution.lift φ (ProjectiveResolution.of X)
    (ProjectiveResolution.of Y) = l at hcomm
  have h1 := (F ⋙ G).leftDerived_map_eq j φ l hcomm
  have h2 : HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map l) j = 0 :=
    homologyMap_eq_zero_of_map_eq_zero G (ComplexShape.down ℕ) j _
      (eq_zero_of_iso_comp_comp_iso _ _ (h1.symm.trans h))
  rw [F.leftDerived_map_eq j φ l hcomm,
    show (F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) j).map l = 0 from h2,
    zero_comp, comp_zero]

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- Extension of scalars, restricted back along `f`, is tensoring with the target ring. -/
def extendScalarsCompRestrictScalarsIsoTensorLeft :
    extendScalars.{u} f ⋙ ModuleCat.restrictScalars f ≅
      tensorLeft ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)) :=
  Functor.isoWhiskerRight
      (Adjunction.leftAdjointUniq (extendRestrictScalarsAdj.{u} f)
        (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f))
      (ModuleCat.restrictScalars f) ≪≫
    NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- **The bridge from `Tor'` to extension of scalars.** A morphism of `R`-modules which induces
the zero map on `Tor'_j^R(-, S)` — the variable which a projective resolution of the source
computes, `S` being read as an `R`-module along `f` — induces the zero map on
`L_j(S ⊗_R -)`. -/
theorem leftDerived_extendScalars_map_eq_zero_of_tor' (j : ℕ) {X Y : ModuleCat.{u} R} (φ : X ⟶ Y)
    (h : ((Tor' (ModuleCat.{u} R) j).map φ).app
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)) = 0) :
    ((extendScalars.{u} f).leftDerived j).map φ = 0 := by
  have h1 : ((tensorRight ((ModuleCat.restrictScalars f).obj
      (ModuleCat.of S S))).leftDerived j).map φ = 0 := h
  exact leftDerived_map_eq_zero_of_comp (extendScalars.{u} f) (ModuleCat.restrictScalars f) j φ
    (leftDerived_map_eq_zero_of_natIso (extendScalarsCompRestrictScalarsIsoTensorLeft f) j φ
      (leftDerived_map_eq_zero_of_natIso (BraidedCategory.tensorLeftIsoTensorRight
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S))) j φ h1))

end Bridge

end Stacks.NoncommChangeOfRings

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (κ : Cardinal.{u})

/-! ### The inclusions of the filtration, as a filtration of presheaves of `𝒪`-modules -/

/-- The inclusion `𝒦ⁿ ⊆ 𝒦ⁿ` of presheaves of `𝒪`-modules is the identity. -/
lemma smallPolynomialAugmentationIdealPowStructureOfLE_self (n : ℕ) (h : n ≤ n) :
    smallPolynomialAugmentationIdealPowStructureOfLE A B κ h =
      𝟙 (smallPolynomialAugmentationIdealPowStructureModule A B κ n) :=
  PresheafOfModules.hom_ext fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => Subtype.ext rfl)

/-- The inclusions `𝒦ᵐ ⊆ 𝒦ⁿ` of presheaves of `𝒪`-modules compose. -/
lemma smallPolynomialAugmentationIdealPowStructureOfLE_comp {n m p : ℕ} (h : n ≤ m)
    (h' : m ≤ p) :
    smallPolynomialAugmentationIdealPowStructureOfLE A B κ h' ≫
        smallPolynomialAugmentationIdealPowStructureOfLE A B κ h =
      smallPolynomialAugmentationIdealPowStructureOfLE A B κ (h.trans h') :=
  PresheafOfModules.hom_ext fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => Subtype.ext rfl)

/-! ### The augmentation on sections, in coordinates -/

/-- The ideal of the variables of `A[E]` is contained in the kernel of a ring map killing every
variable. -/
private lemma span_range_X_le_ker {E : Type u} {S : Type u} [Ring S]
    (f : MvPolynomial E A →+* S) (hf : ∀ e, f (MvPolynomial.X e) = 0) :
    (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) :
        Ideal (MvPolynomial E A)) ≤ RingHom.ker f := by
  refine Ideal.span_le.2 (Set.range_subset_iff.2 fun e => ?_)
  change MvPolynomial.X e ∈ RingHom.ker f
  rw [RingHom.mem_ker, hf]

/-- **The augmentation `𝒪(X) ⟶ B̲(X)` on a variable** is the point naming `X`. -/
lemma smallPolynomialAugmentation_app_hom_X (X : (smallBoundedPolynomialSite A B κ)ᵒᵖ)
    (e : ↥(X.unop.unop.1)) :
    ((smallPolynomialAugmentation A B κ).app X).hom (MvPolynomial.X e) =
      smallSitePoint A B κ X e := by
  have hplumb : ((smallPolynomialAugmentation A B κ).app X).hom (MvPolynomial.X e) =
      MvPolynomial.aeval (fun s : ↥(X.unop.unop.1) => (X.unop.unop.2 s : (B : Type u)))
        (MvPolynomial.X e) := rfl
  rw [hplumb, MvPolynomial.aeval_X]

/-- **The augmentation kills every variable at an object whose point is `0`.** -/
lemma smallPolynomialAugmentation_app_hom_X_eq_zero
    (X : (smallBoundedPolynomialSite A B κ)ᵒᵖ) (h0 : smallSitePoint A B κ X = 0)
    (e : ↥(X.unop.unop.1)) :
    ((smallPolynomialAugmentation A B κ).app X).hom (MvPolynomial.X e) = 0 :=
  (smallPolynomialAugmentation_app_hom_X A B κ X e).trans (congrFun h0 e)

/-! ### The local claim in the shape the global half consumes -/

/-- **The local claim of [Stacks, Tag 08RF] in the shape the global half consumes.** Over an
object `X` of the small model whose point is `0`, the inclusion `𝒦ᵐ ⊆ 𝒦ⁿ` induces the zero map
on `L_j(B̲(X) ⊗_{𝒪(X)} -)` for every `j` strictly below the step size `m - n`. -/
theorem leftDerived_extendScalars_map_smallPolynomialAugmentationIdealPowStructureOfLE_eq_zero
    (X : (smallBoundedPolynomialSite A B κ)ᵒᵖ) (h0 : smallSitePoint A B κ X = 0)
    {m n : ℕ} (h : n ≤ m) (j : ℕ) (hj : j < m - n) :
    ((Stacks.NoncommChangeOfRings.extendScalars.{u}
        ((smallPolynomialAugmentation A B κ).app X).hom).leftDerived j).map
      ((smallPolynomialAugmentationIdealPowStructureOfLE A B κ h).app X) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
  exact Stacks.NoncommChangeOfRings.leftDerived_extendScalars_map_eq_zero_of_tor'
    (R := MvPolynomial ↥(X.unop.unop.1) A) (S := (B : Type u))
    ((smallPolynomialAugmentation A B κ).app X).hom j _
    (tor'_map_app_smallPolynomialAugmentationIdealPowStructureOfLE_eq_zero A B κ n k j
      (by omega) X h0 _ fun r hr x => by
        have hr0 : ((smallPolynomialAugmentation A B κ).app X).hom r = 0 :=
          span_range_X_le_ker A
            (((smallPolynomialAugmentation A B κ).app X).hom :
              MvPolynomial ↥(X.unop.unop.1) A →+* (B : Type u))
            (smallPolynomialAugmentation_app_hom_X_eq_zero A B κ X h0) hr
        exact ModuleCat.restrictScalars.smul_eq_zero_of_map_eq_zero _ r hr0 x)

/-! ### `hpro` -/

section Standard

variable {A B}

/-- **Pro-nilpotence of the augmentation filtration on the homology of `C_{B/A}`.** For a
surjective `A → B` and every `k`, the inclusion `𝒦^{n+k²} ⊆ 𝒦ⁿ` induces the zero map on
`H_i(C_{B/A}, -)` for every `n` and every `i < k`.

This is the second claim in the proof of [Stacks, Tag 08RF]. -/
theorem smallPolynomialAugmentationProNilpotent
    (hsurj : Function.Surjective (algebraMap A (B : Type u))) :
    SmallPolynomialAugmentationProNilpotent A B (standardResolutionVarCardinal A B) := by
  intro k
  refine ⟨k * k, fun n i hi => ?_⟩
  -- the arithmetic of the chain of `k` steps of size `k`
  have hmono : ∀ j : ℕ, n + (k - (j + 1)) * k ≤ n + (k - j) * k := fun j =>
    Nat.add_le_add_left (Nat.mul_le_mul (by omega) (le_refl k)) n
  have hstepsize : ∀ j : ℕ, j < k → j < n + (k - j) * k - (n + (k - (j + 1)) * k) := by
    intro j hj
    have e : k - j = (k - (j + 1)) + 1 := by omega
    rw [e, Nat.add_mul, Nat.one_mul]
    omega
  have hM : (fun j => n + (k - j) * k) 0 = n + k * k := by simp
  have hN : (fun j => n + (k - j) * k) k = n := by simp
  -- the global chain argument
  have hchain := Stacks.ChaoticSite.homology_derivedColimit_tensor_map_eq_zero_of_objectwise
    (smallPolynomialAugmentation A B (standardResolutionVarCardinal A B))
    (fun m => smallPolynomialAugmentationIdealPowStructureModule A B
      (standardResolutionVarCardinal A B) m)
    (fun {m n} h => smallPolynomialAugmentationIdealPowStructureOfLE A B
      (standardResolutionVarCardinal A B) h)
    (fun m h => smallPolynomialAugmentationIdealPowStructureOfLE_self A B _ m h)
    (fun {_ _ _} h h' => smallPolynomialAugmentationIdealPowStructureOfLE_comp A B _ h h')
    (fun U => smallSitePoint A B (standardResolutionVarCardinal A B) U = 0)
    (fun {_ _} α hα U => app_eq_zero_of_forall_smallSitePoint_eq_zero A B
      (standardResolutionVarCardinal A B) hsurj α hα U)
    (fun U hU m' n' h j hj =>
      leftDerived_extendScalars_map_smallPolynomialAugmentationIdealPowStructureOfLE_eq_zero
        A B (standardResolutionVarCardinal A B) U hU h j hj)
    k (fun j => n + (k - j) * k) hmono hstepsize (Nat.le_add_right n (k * k)) hM hN i hi
  -- transport the vanishing back across the change of coefficients
  have h08QJ : IsIso ((Stacks.ChaoticSite.derivedColimitTensorComparison
      (smallPolynomialAugmentation A B (standardResolutionVarCardinal A B))).app
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (PresheafOfModules.{u}
            (smallPolynomialStructurePresheaf A B (standardResolutionVarCardinal A B)))
              (ComplexShape.up ℤ) 0).obj
            (smallPolynomialAugmentationIdealPowStructureModule A B
              (standardResolutionVarCardinal A B) n)))) :=
    isIso_derivedColimitTensorComparison_smallPolynomialAugmentationIdealPow A B n
  have hnat := congrArg
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} (-(i : ℤ))).map
    ((Stacks.ChaoticSite.derivedColimitTensorComparison
      (smallPolynomialAugmentation A B (standardResolutionVarCardinal A B))).naturality
      (DerivedCategory.Q.map ((HomologicalComplex.single (PresheafOfModules.{u}
        (smallPolynomialStructurePresheaf A B (standardResolutionVarCardinal A B)))
          (ComplexShape.up ℤ) 0).map (smallPolynomialAugmentationIdealPowStructureOfLE A B
        (standardResolutionVarCardinal A B) (Nat.le_add_right n (k * k))))))
  rw [Functor.map_comp, Functor.map_comp] at hnat
  have hLHS : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} (-(i : ℤ))).map
      ((Stacks.ChaoticSite.abelianDerivedColimitOfModules
        (smallPolynomialStructurePresheaf A B (standardResolutionVarCardinal A B))).map
        (DerivedCategory.Q.map ((HomologicalComplex.single (PresheafOfModules.{u}
          (smallPolynomialStructurePresheaf A B (standardResolutionVarCardinal A B)))
            (ComplexShape.up ℤ) 0).map (smallPolynomialAugmentationIdealPowStructureOfLE A B
          (standardResolutionVarCardinal A B) (Nat.le_add_right n (k * k)))))) = 0 := by
    refine zero_of_comp_mono _ (hnat.trans ?_)
    rw [hchain]
    exact comp_zero
  -- drop the module coefficients, and read `L_i colim` through `Lπ_!`
  refine Stacks.ChaoticSite.leftDerivedColim_map_eq_zero_of_forget
    (standardResolutionSmallCosimplicialObject A B)
    (isPointResolution_standardResolutionSmallCosimplicialObject A B) i _ ?_
  refine Stacks.ChaoticSite.AbelianValued.leftDerivedColim_map_eq_zero
    (standardResolutionSmallCosimplicialObject A B)
    (isPointResolution_standardResolutionSmallCosimplicialObject A B) i _ ?_
  -- the abelian presheaf underlying `𝒦ⁿ` as an `𝒪`-module is the one of `𝒦ⁿ` as a `B`-module
  have E := Functor.isoWhiskerLeft
      (HomologicalComplex.single (PresheafOfModules.{u}
        (smallPolynomialStructurePresheaf A B (standardResolutionVarCardinal A B)))
          (ComplexShape.up ℤ) 0)
      (Functor.isoWhiskerRight
        (PresheafOfModules.toPresheaf.{u}
          (smallPolynomialStructurePresheaf A B
            (standardResolutionVarCardinal A B))).mapDerivedCategoryFactors
        (Stacks.CategoryHomology.totalDerivedColimit
            (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))
            AddCommGrpCat.{u} ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} (-(i : ℤ)))) ≪≫
    Functor.isoWhiskerRight
      (HomologicalComplex.singleMapHomologicalComplex
        (PresheafOfModules.toPresheaf.{u}
          (smallPolynomialStructurePresheaf A B (standardResolutionVarCardinal A B)))
        (ComplexShape.up ℤ) 0)
      (DerivedCategory.Q ⋙
        Stacks.CategoryHomology.totalDerivedColimit
            (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))
            AddCommGrpCat.{u} ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} (-(i : ℤ)))
  have hnat2 := E.hom.naturality (smallPolynomialAugmentationIdealPowStructureOfLE A B
    (standardResolutionVarCardinal A B) (Nat.le_add_right n (k * k)))
  rw [show (HomologicalComplex.single (PresheafOfModules.{u}
        (smallPolynomialStructurePresheaf A B (standardResolutionVarCardinal A B)))
          (ComplexShape.up ℤ) 0 ⋙
      (DerivedCategory.Q ⋙ (PresheafOfModules.toPresheaf.{u} (smallPolynomialStructurePresheaf A B
        (standardResolutionVarCardinal A B))).mapDerivedCategory) ⋙
      (Stacks.CategoryHomology.totalDerivedColimit
          (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))
          AddCommGrpCat.{u} ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} (-(i : ℤ)))).map
      (smallPolynomialAugmentationIdealPowStructureOfLE A B
        (standardResolutionVarCardinal A B) (Nat.le_add_right n (k * k))) = 0 from hLHS,
    zero_comp] at hnat2
  exact zero_of_epi_comp (E.hom.app (smallPolynomialAugmentationIdealPowStructureModule A B
    (standardResolutionVarCardinal A B) (n + k * k))) hnat2.symm

end Standard

end CommAlgCat

end
