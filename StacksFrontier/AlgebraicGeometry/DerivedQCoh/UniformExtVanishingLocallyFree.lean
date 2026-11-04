module

public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceGlobalHom
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedComplexInduction
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.EventualExtVanishing

/-!
# Ext between finite locally free modules vanishes in high degrees, uniformly in both arguments

Let `X` be a quasi-compact and quasi-separated scheme. There is an integer `n₀ > 0`, depending
only on `X`, such that `Ext^n_{D(𝒪_X)}(ℰ, ℱ) = 0` for *every* pair of finite locally free
`𝒪_X`-modules `ℰ` and `ℱ` and every `n ≥ n₀`.

This strengthens the uniformity of
`Stacks.DerivedQCoh.exists_pos_subsingleton_hom_singleFunctor_of_isFiniteLocallyFree`
([Stacks, Tag 08EF]), which produces a bound uniform in the source `ℰ` but depending on the
target. The proof is the one of that tag — Mayer--Vietoris for morphisms in the derived category
([Stacks, Tag 08BW]) and the induction principle for quasi-compact opens of a quasi-separated
scheme ([Stacks, Tag 08DR]) reduce to the affine case — run on the property that quantifies over
both arguments at once. What makes the strengthening go through is that the bound of the affine
case is `max 1 (b + 1)` for `b` an upper cohomological bound of the target, and a module placed
in degree zero has `b = 0`: the affine bound is the constant `1`, so nothing in the induction
depends on the target.

The second half of the file turns a vanishing morphism group out of a bounded complex into the
vanishing of the morphism groups out of its terms, by induction on the stupid truncations.
Together the two halves give the vanishing of `Hom_{D(𝒪_U)}(E, ℱ[-d])` for `E` an object of
`D(𝒪_U)` admitting a bounded finite-locally-free representative and `d` far below the bottom of
that representative.

## Main definitions

* `Stacks.DerivedQCoh.HasBiuniformExtBound`: the conclusion, as a property of a scheme.

## Main results

* `Stacks.DerivedQCoh.hasBiuniformExtBound_of_isCompact`: every quasi-compact open of a
  quasi-separated scheme has such a bound.
* `Stacks.DerivedQCoh.exists_subsingleton_hom_singleFunctor_of_isCompact`: the same, stated for
  the two modules placed in arbitrary degrees `m` and `k` with `k + n₀ ≤ m`.
* `Stacks.DerivedQCoh.subsingleton_hom_Q_obj_of_singleFunctor`: a morphism group out of a
  bounded complex vanishes once the morphism groups out of its terms, each placed in its own
  degree, vanish.

## Implementation notes

The morphism groups are read as in `StacksFrontier/AlgebraicGeometry/DerivedQCoh/
EventualExtVanishing.lean`: `Ext^n(ℰ, ℱ)` is the group of morphisms
`ℰ[0] ⟶ (ℱ[0])⟦n⟧` in `D(𝒪_X)` at the standard model of the derived category, and its vanishing
is subsingletonness. The passage between `ℰ[0] ⟶ (ℱ[0])⟦n⟧` and `ℰ[m] ⟶ ℱ[k]` with `n = m - k`
is the `shiftIso` of the `SingleFunctors` structure, applied in the shape used by
`Stacks.DerivedCategory.Ext.hom_eq_zero_of_forall_ext_eq_zero`.

## References

* [Stacks Project, Tag 08EF](https://stacks.math.columbia.edu/tag/08EF)
* [Stacks Project, Tag 08BW](https://stacks.math.columbia.edu/tag/08BW)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Duality.OpenImmersion (derivedRestrict)

universe u

namespace Stacks.DerivedQCoh

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] preservesFiniteLimits_restrictFunctor

/-! ### Morphisms out of a bounded complex -/

section Bounded

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- There is at most one morphism out of a zero object. -/
theorem subsingleton_hom_of_isZero_source {A T : DerivedCategory C} (h : IsZero A) :
    Subsingleton (A ⟶ T) :=
  ⟨fun f g => h.eq_of_src f g⟩

/-- **Morphism groups out of an extension of complexes.** A short exact sequence of complexes
gives a distinguished triangle in the derived category, so a morphism group out of its middle
term vanishes once the groups out of the two outer terms vanish. -/
theorem subsingleton_hom_of_shortExact (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) (T : DerivedCategory C)
    (h₁ : Subsingleton (DerivedCategory.Q.obj S.X₁ ⟶ T))
    (h₃ : Subsingleton (DerivedCategory.Q.obj S.X₃ ⟶ T)) :
    Subsingleton (DerivedCategory.Q.obj S.X₂ ⟶ T) := by
  have hd := DerivedCategory.triangleOfSES_distinguished hS
  refine ⟨fun f g => ?_⟩
  obtain ⟨f', hf'⟩ := Pretriangulated.Triangle.yoneda_exact₂ _ hd f (h₁.elim _ _)
  obtain ⟨g', hg'⟩ := Pretriangulated.Triangle.yoneda_exact₂ _ hd g (h₁.elim _ _)
  rw [hf', hg', h₃.elim f' g']

/-- **A morphism group out of a bounded complex, from the morphism groups out of its terms.**
If a complex `K` has only finitely many nonzero terms and every term, placed in its own
cohomological degree, admits at most one morphism into `T`, then `K` admits at most one morphism
into `T`. -/
theorem subsingleton_hom_Q_obj_of_singleFunctor (K : CochainComplex C ℤ)
    (hK : {i : ℤ | ¬ IsZero (K.X i)}.Finite) (T : DerivedCategory C)
    (hsingle : ∀ i : ℤ, Subsingleton ((DerivedCategory.singleFunctor C i).obj (K.X i) ⟶ T)) :
    Subsingleton (DerivedCategory.Q.obj K ⟶ T) :=
  Stacks.DerivedCategory.BoundedInduction.property_of_bounded_complex
    (fun A => Subsingleton (A ⟶ T))
    (fun e h => subsingleton_hom_of_iso e.symm (Iso.refl T) h)
    (fun _ hA => subsingleton_hom_of_isZero_source hA)
    (fun S hS h₁ h₃ => subsingleton_hom_of_shortExact S hS T h₁ h₃)
    K hK hsingle

/-- If there is at most one morphism `A[0] ⟶ B[0]⟦m - k⟧`, then there is at most one morphism
from `A` placed in degree `m` to `B` placed in degree `k`. -/
theorem subsingleton_hom_singleFunctor_of_shift (A B : C) (m k : ℤ)
    (h : Subsingleton ((DerivedCategory.singleFunctor C 0).obj A ⟶
      ((DerivedCategory.singleFunctor C 0).obj B)⟦m - k⟧)) :
    Subsingleton ((DerivedCategory.singleFunctor C m).obj A ⟶
      (DerivedCategory.singleFunctor C k).obj B) := by
  have key : Subsingleton (((DerivedCategory.singleFunctor C m).obj A)⟦m⟧ ⟶
      ((DerivedCategory.singleFunctor C k).obj B)⟦m⟧) :=
    subsingleton_hom_of_iso
      (((DerivedCategory.singleFunctors C).shiftIso m 0 m (by omega)).app A)
      ((((DerivedCategory.singleFunctors C).shiftIso m (k - m) k (by omega)).app B) ≪≫
        (((DerivedCategory.singleFunctors C).shiftIso (m - k) (k - m) 0 (by omega)).app B).symm)
      h
  exact ⟨fun f g => (shiftFunctor (DerivedCategory C) m).map_injective (key.elim _ _)⟩

end Bounded

/-! ### Quasi-coherence of the cohomology of a module placed in one degree -/


/-- The cohomology sheaves of a quasi-coherent module placed in a single cohomological degree are
quasi-coherent: in that degree the cohomology is the module itself, and in every other degree it
vanishes. -/
private theorem isQuasicoherent_homology_singleFunctor (Y : Scheme.{u}) (M : Y.Modules)
    (hM : M.IsQuasicoherent) (n i : ℤ) :
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((DerivedCategory.singleFunctor Y.Modules n).obj M)).IsQuasicoherent := by
  by_cases hi : i = n
  · subst hi
    have := hM
    exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso Y.Modules i).app M).symm hM
  · refine Stacks.Duality.isQuasicoherent_of_isZero _ ?_
    rcases lt_or_gt_of_ne hi with h | h
    · exact DerivedCategory.isZero_of_isGE _ n i h
    · exact DerivedCategory.isZero_of_isLE _ n i h

/-! ### The bound as a property of a scheme -/

/-- `HasBiuniformExtBound X` says that `Ext^n_{D(𝒪_X)}(ℰ, ℱ)` vanishes for every pair `ℰ`, `ℱ`
of finite locally free `𝒪_X`-modules and every `n` beyond a positive bound depending on neither
of them. -/
def HasBiuniformExtBound (X : Scheme.{u}) : Prop :=
  ∃ n₀ : ℤ, 0 < n₀ ∧
    ∀ ℰ F : X.Modules, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} ℰ →
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F →
      ∀ n : ℤ, n₀ ≤ n →
        Subsingleton ((DerivedCategory.singleFunctor X.Modules 0).obj ℰ ⟶
          ((DerivedCategory.singleFunctor X.Modules 0).obj F)⟦n⟧)

/-! ### The affine case -/

/-- The spectrum of a ring has the bound, with `n₀ = 1`. -/
theorem hasBiuniformExtBound_spec (R : CommRingCat.{u}) : HasBiuniformExtBound (Spec R) := by
  refine ⟨1, one_pos, fun ℰ F hℰ hF n hn => ?_⟩
  set E := (DerivedCategory.singleFunctor (Spec R).Modules 0).obj F
  have hq : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj E).IsQuasicoherent := fun i =>
    isQuasicoherent_homology_singleFunctor (Spec R) F
      (isQuasicoherent_of_isFiniteLocallyFree F hF) 0 i
  set Γ := AlgebraicGeometry.derivedGlobalSectionsOver (𝟙 (Spec R))
  have hM : (Γ.obj E).IsLE 0 :=
    isLE_derivedGlobalSectionsOver_obj (𝟙 (Spec R)) E 0 inferInstance hq
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_projective_tilde_iso R ℰ hℰ
  let P0 := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj P
  let eSource : (AlgebraicGeometry.derivedTilde R ⋙
      (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι).obj P0 ≅
      (DerivedCategory.singleFunctor (Spec R).Modules 0).obj ℰ :=
    (AlgebraicGeometry.derivedTildeCompι R).app P0 ≪≫
      ((AlgebraicGeometry.tilde.functor R).mapDerivedCategorySingleFunctor 0).app P ≪≫
      (DerivedCategory.singleFunctor (Spec R).Modules 0).mapIso eP
  let adj := (AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction R).val
  let eShift : Γ.obj (E⟦n⟧) ≅ (Γ.obj E)⟦n⟧ := (Γ.commShiftIso n).app E
  have htarget : Subsingleton (P0 ⟶ (Γ.obj E)⟦n⟧) :=
    subsingleton_hom_single_shift_of_projective P (Γ.obj E) 0 n (by omega)
  refine ⟨fun g h => ?_⟩
  have hinj : adj.homEquiv P0 (E⟦n⟧) (eSource.hom ≫ g) ≫ eShift.hom =
      adj.homEquiv P0 (E⟦n⟧) (eSource.hom ≫ h) ≫ eShift.hom := htarget.elim _ _
  exact (cancel_epi eSource.hom).1 ((adj.homEquiv P0 (E⟦n⟧)).injective
    ((cancel_mono eShift.hom).1 hinj))

/-! ### Transport along an isomorphism of schemes -/

/-- The bound is invariant under isomorphism of schemes. -/
theorem hasBiuniformExtBound_of_iso {A B : Scheme.{u}} (e : A ≅ B)
    (h : HasBiuniformExtBound B) : HasBiuniformExtBound A := by
  obtain ⟨N, hN, h⟩ := h
  refine ⟨N, hN, fun ℰ F hℰ hF n hn => ?_⟩
  have hs := h ((Scheme.Modules.restrictFunctor e.inv).obj ℰ)
    ((Scheme.Modules.restrictFunctor e.inv).obj F)
    (isFiniteLocallyFree_restrict e.inv ℰ hℰ) (isFiniteLocallyFree_restrict e.inv F hF) n hn
  have hs' : Subsingleton ((derivedRestrict e.inv).obj
      ((DerivedCategory.singleFunctor A.Modules 0).obj ℰ) ⟶
      (derivedRestrict e.inv).obj
        (((DerivedCategory.singleFunctor A.Modules 0).obj F)⟦n⟧)) :=
    subsingleton_hom_of_iso
      (((Scheme.Modules.restrictFunctor e.inv).mapDerivedCategorySingleFunctor 0).app ℰ)
      (((derivedRestrict e.inv).commShiftIso n).app
          ((DerivedCategory.singleFunctor A.Modules 0).obj F) ≪≫
        (shiftFunctor _ n).mapIso
          (((Scheme.Modules.restrictFunctor e.inv).mapDerivedCategorySingleFunctor 0).app F))
      hs
  let := derivedRestrict_faithful e
  exact ⟨fun a b => (derivedRestrict e.inv).map_injective (hs'.elim _ _)⟩

/-- An affine scheme has the bound. -/
theorem hasBiuniformExtBound_of_isAffine (Z : Scheme.{u}) [IsAffine Z] :
    HasBiuniformExtBound Z :=
  hasBiuniformExtBound_of_iso Z.isoSpec (hasBiuniformExtBound_spec _)

/-! ### The induction on quasi-compact opens -/

/-- The bound, read on the restrictions to an open subscheme of two global finite locally free
modules. -/
theorem exists_biuniform_bound_derivedRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (h : HasBiuniformExtBound X) :
    ∃ n₀ : ℤ, 0 < n₀ ∧
      ∀ ℰ F : Y.Modules, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} ℰ →
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F →
        ∀ n : ℤ, n₀ ≤ n →
          Subsingleton ((derivedRestrict f).obj
              ((DerivedCategory.singleFunctor Y.Modules 0).obj ℰ) ⟶
            ((derivedRestrict f).obj
              ((DerivedCategory.singleFunctor Y.Modules 0).obj F))⟦n⟧) := by
  obtain ⟨N, hN, h⟩ := h
  refine ⟨N, hN, fun ℰ F hℰ hF n hn => ?_⟩
  exact subsingleton_hom_of_iso
    (((Scheme.Modules.restrictFunctor f).mapDerivedCategorySingleFunctor 0).app ℰ)
    ((shiftFunctor _ n).mapIso
      (((Scheme.Modules.restrictFunctor f).mapDerivedCategorySingleFunctor 0).app F))
    (h _ _ (isFiniteLocallyFree_restrict f ℰ hℰ) (isFiniteLocallyFree_restrict f F hF) n hn)

/-- **The Mayer--Vietoris step.** If two opens of a scheme and their intersection have the
bound, then so does their union: the Mayer--Vietoris sequence of [Stacks, Tag 08BW] raises it by
one. -/
theorem hasBiuniformExtBound_sup {X : Scheme.{u}} (U V : X.Opens)
    (hU : HasBiuniformExtBound U.toScheme) (hV : HasBiuniformExtBound V.toScheme)
    (hUV : HasBiuniformExtBound (U ⊓ V).toScheme) :
    HasBiuniformExtBound (U ⊔ V).toScheme := by
  set j := (U ⊔ V).ι with hj
  set U' : (U ⊔ V).toScheme.Opens := j ⁻¹ᵁ U with hU'def
  set V' : (U ⊔ V).toScheme.Opens := j ⁻¹ᵁ V with hV'def
  have hcover : U' ⊔ V' = ⊤ := by
    rw [hU'def, hV'def, ← Scheme.Hom.preimage_sup]
    exact Scheme.Opens.ι_preimage_self _
  have hinf : U' ⊓ V' = j ⁻¹ᵁ (U ⊓ V) := (Scheme.Hom.preimage_inf j).symm
  have restrict_bound : ∀ (S : X.Opens) (T : (U ⊔ V).toScheme.Opens), j ⁻¹ᵁ S = T →
      S ≤ U ⊔ V → HasBiuniformExtBound S.toScheme → HasBiuniformExtBound T.toScheme := by
    rintro S T rfl hS hSb
    refine hasBiuniformExtBound_of_iso (imageOpensIso (U ⊔ V) (j ⁻¹ᵁ S) ≪≫ ?_) hSb
    exact eqToIso (congrArg Scheme.Opens.toScheme (by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        inf_eq_right.mpr hS]))
  have hU'b := restrict_bound U U' rfl le_sup_left hU
  have hV'b := restrict_bound V V' rfl le_sup_right hV
  have hWb := restrict_bound (U ⊓ V) (U' ⊓ V') hinf.symm (inf_le_left.trans le_sup_left) hUV
  obtain ⟨a, ha, hUa⟩ := exists_biuniform_bound_derivedRestrict U'.ι hU'b
  obtain ⟨b, hb, hVb⟩ := exists_biuniform_bound_derivedRestrict V'.ι hV'b
  obtain ⟨c, hc, hWc⟩ := exists_biuniform_bound_derivedRestrict (U' ⊓ V').ι hWb
  refine ⟨max a (max b c) + 1, by omega, fun ℰ F hℰ hF n hn => ?_⟩
  have h := subsingleton_hom_of_cover U' V' hcover
    ((DerivedCategory.singleFunctor (U ⊔ V).toScheme.Modules 0).obj ℰ)
    ((DerivedCategory.singleFunctor (U ⊔ V).toScheme.Modules 0).obj F) (n - 1)
    (by simpa using hUa ℰ F hℰ hF (n - 1 + 1) (by omega))
    (by simpa using hVb ℰ F hℰ hF (n - 1 + 1) (by omega))
    (by simpa using hWc ℰ F hℰ hF (n - 1) (by omega))
  rwa [show n - 1 + 1 = n from by omega] at h

/-- **Every quasi-compact open of a quasi-separated scheme has the bound.** The induction
principle of [Stacks, Tag 08DR] reduces this to the affine case and the Mayer--Vietoris step. -/
theorem hasBiuniformExtBound_of_isCompact {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (W : X.Opens) (hW : IsCompact (W : Set X)) : HasBiuniformExtBound W.toScheme :=
  Stacks.AlgebraicGeometry.InductionPrinciple.induction_isCompact_open
    (fun W => HasBiuniformExtBound W.toScheme)
    (fun _ hV => have : IsAffine _ := hV; hasBiuniformExtBound_of_isAffine _)
    (fun U V _ _ hU hV hUV => hasBiuniformExtBound_sup U V hU hV hUV) W hW

/-- **The bound, with the two modules placed in arbitrary degrees.** On a quasi-compact open `W`
of a quasi-separated scheme there is an `n₀ > 0` such that, for all finite locally free
`𝒪_W`-modules `ℰ` and `ℱ`, there is no nonzero morphism from `ℰ` placed in degree `m` to `ℱ`
placed in degree `k` as soon as `k + n₀ ≤ m`. -/
theorem exists_subsingleton_hom_singleFunctor_of_isCompact {X : Scheme.{u}}
    [QuasiSeparatedSpace X] (W : X.Opens) (hW : IsCompact (W : Set X)) :
    ∃ n₀ : ℤ, 0 < n₀ ∧
      ∀ ℰ F : W.toScheme.Modules,
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} ℰ →
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F →
        ∀ m k : ℤ, k + n₀ ≤ m →
          Subsingleton ((DerivedCategory.singleFunctor W.toScheme.Modules m).obj ℰ ⟶
            (DerivedCategory.singleFunctor W.toScheme.Modules k).obj F) := by
  obtain ⟨n₀, hn₀, h⟩ := hasBiuniformExtBound_of_isCompact W hW
  exact ⟨n₀, hn₀, fun ℰ F hℰ hF m k hmk =>
    subsingleton_hom_singleFunctor_of_shift ℰ F m k (h ℰ F hℰ hF (m - k) (by omega))⟩

end Stacks.DerivedQCoh

end
