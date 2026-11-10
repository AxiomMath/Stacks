module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusTraceIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportFrobeniusNatTrans
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalFrobeniusAdditivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.OpenClosedFrobeniusTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactCharSeries
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit

/-!
# Multiplicativity of the characteristic series of the canonical Frobenius action

Let `k` be a finite field, `X` a scheme over `k` with a compactification `j : X ⟶ X̄`, `k̄` an
extension of `k` and `Λ` a commutative ring. Along a short exact sequence
`0 → K₁ → K₂ → K₃ → 0` of bounded below complexes of sheaves of `Λ`-modules on `X` with
`RΓ_c(X_k̄, Kᵢ)` perfect,

`det(1 - π_X^* T | RΓ_c(X_k̄, K₂)) =`
`det(1 - π_X^* T | RΓ_c(X_k̄, K₁)) · det(1 - π_X^* T | RΓ_c(X_k̄, K₃))`

in `Λ⟦T⟧ˣ`, for the canonical action of `Stacks.EtaleCohomology.canonicalCompactSupportFrobenius`.
This is the determinant analogue of
`Stacks.EtaleCohomology.canonicalCompactSupportLefschetzNumber_X₂_eq_add`, with the same proof:
the canonical action is the derived endomorphism of a twist, and the derived endomorphism of a
twist is computed on a degreewise split injective resolution with a lifted twist
(`CategoryTheory.Functor.TwistResolution`), whose image under global sections is a short exact
sequence of complexes of modules, to which
`CategoryTheory.FilteredDerived.perfectDerivedCharSeries_X₂_eq_mul` applies.

## Main results

* `CategoryTheory.Functor.perfectDerivedCharSeries_derivedTwistEndo_eq`: the characteristic series
  of a twisted endomorphism is computed on an injective resolution.
* `CategoryTheory.Functor.perfectDerivedCharSeries_derivedTwistEndo_X₂_eq_mul`: multiplicativity
  along a short exact sequence with a twist.
* `Stacks.EtaleCohomology.perfectDerivedCharSeries_frobeniusRestrictionCohomologyEndo_X₂_eq_mul`
  and its open and closed instance
  `perfectDerivedCharSeries_frobeniusRestrictionCohomologyEndo_eq_mul_openClosed`.
* `Stacks.EtaleCohomology.perfectDerivedCharSeries_canonicalCompactSupportFrobenius_X₂_eq_mul`.

## Implementation notes

The twisted endomorphisms, their resolutions and the canonical Frobenius action are defined for
the model `HasDerivedCategory.standard` of the derived category, so the results here are stated
in that model; the instance is made local exactly as in the files that define them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v u₁ v₁ r

namespace CategoryTheory.Functor

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

open CategoryTheory.FilteredDerived CochainComplex

variable {R : Type u} [CommRing R] {C D : Type u₁} [Category.{v₁} C] [Category.{v₁} D]
  [Abelian C] [Abelian D] [EnoughInjectives C] [EnoughInjectives D]
  (P : C ⥤ C) (F₁ : C ⥤ D) (F₂ : D ⥤ ModuleCat.{max u v} R) [P.Additive] [F₁.Additive]
  [F₂.Additive] [P.PreservesInjectiveObjects] [F₁.PreservesInjectiveObjects] (θ : P ⋙ F₁ ≅ F₁)

/-- **The characteristic series of a twisted endomorphism is computed on an injective
resolution.** For a quasi-isomorphism `ψ : K ⟶ T` into a bounded below complex of injectives and
twists `τ` of `K` and `g` of `T` compatible along `ψ` in the derived category, the characteristic
series of the derived endomorphism of `RF₂(RF₁(K))` attached to `τ` is that of the componentwise
endomorphism `F₂(F₁(g) ≫ θ)` of `F₂(F₁(T))`. -/
theorem perfectDerivedCharSeries_derivedTwistEndo_eq {K T : CochainComplex.Plus C} (ψ : K ⟶ T)
    [QuasiIso ψ.hom] (hT : ∀ n, Injective (T.obj.X n)) (τ : K ⟶ P.mapCochainComplexPlus.obj K)
    (g : T ⟶ P.mapCochainComplexPlus.obj T)
    (h : DerivedCategory.Plus.Q.map (τ ≫ P.mapCochainComplexPlus.map ψ) =
      DerivedCategory.Plus.Q.map (ψ ≫ g))
    (hK : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)))))
    (hT' : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (F₂.mapCochainComplexPlus.obj (F₁.mapCochainComplexPlus.obj T)).obj)) :
    perfectDerivedCharSeries R _ hK
        (DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ K τ)) =
      perfectDerivedCharSeries R _ hT'
        (DerivedCategory.Q.map (twistChainEndo P F₁ F₂ θ T g).hom) :=
  perfectDerivedCharSeries_congr R hK hT' (twistResolutionIso F₁ F₂ ψ hT) _ _
    (twistResolutionIso_hom_comp P F₁ F₂ θ ψ hT τ g h)

/-- **Multiplicativity of the characteristic series of a twisted derived endomorphism along a
short exact sequence.** Let `0 → X₁ → X₂ → X₃ → 0` be a short exact sequence of bounded below
complexes and `τ` a twist of it. If `RF₂(RF₁(Xᵢ))` is perfect for each `i` then the
characteristic series of the derived endomorphisms attached to `τ` satisfy
`det(X₂) = det(X₁) · det(X₃)`. -/
theorem perfectDerivedCharSeries_derivedTwistEndo_X₂_eq_mul
    {S : ShortComplex (CochainComplex C ℤ)}
    (hS : S.ShortExact) (h₁ : CochainComplex.plus C S.X₁) (h₂ : CochainComplex.plus C S.X₂)
    (h₃ : CochainComplex.plus C S.X₃)
    (τ : S ⟶ S.map (P.mapHomologicalComplex (ComplexShape.up ℤ)))
    (hp₁ : StacksDraft.Perfect.IsPerfect (twistDerivedObj F₁ F₂ h₁))
    (hp₂ : StacksDraft.Perfect.IsPerfect (twistDerivedObj F₁ F₂ h₂))
    (hp₃ : StacksDraft.Perfect.IsPerfect (twistDerivedObj F₁ F₂ h₃)) :
    perfectDerivedCharSeries R _ hp₂
        (DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ _ (plusTwist P h₂ τ.τ₂))) =
      perfectDerivedCharSeries R _ hp₁
          (DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ _ (plusTwist P h₁ τ.τ₁))) *
        perfectDerivedCharSeries R _ hp₃
          (DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ _ (plusTwist P h₃ τ.τ₃))) := by
  obtain ⟨Rs⟩ := TwistResolution.nonempty P hS h₁ h₃ τ
  have hq₁ := StacksDraft.Perfect.isPerfect_of_iso (Rs.iso₁ F₁ F₂ h₁).symm hp₁
  have hq₂ := StacksDraft.Perfect.isPerfect_of_iso (Rs.iso₂ F₁ F₂ h₂).symm hp₂
  have hq₃ := StacksDraft.Perfect.isPerfect_of_iso (Rs.iso₃ F₁ F₂ h₃).symm hp₃
  rw [perfectDerivedCharSeries_congr R hp₁ hq₁ _ _ _ (Rs.iso₁_hom_comp F₁ F₂ θ h₁),
    perfectDerivedCharSeries_congr R hp₂ hq₂ _ _ _ (Rs.iso₂_hom_comp F₁ F₂ θ h₂),
    perfectDerivedCharSeries_congr R hp₃ hq₃ _ _ _ (Rs.iso₃_hom_comp F₁ F₂ θ h₃)]
  exact perfectDerivedCharSeries_X₂_eq_mul (Rs.image_shortExact F₁ F₂) (Rs.imageEndo F₁ F₂ θ)
    hq₁ hq₂ hq₃

end CategoryTheory.Functor

open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Frobenius

variable (Λ : Type r) [CommRing Λ] {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- **Multiplicativity of `det(1 - π T | RΓ(Y_k̄, -))` along a short exact sequence.** For a
short exact sequence `0 → C₁ → C₂ → C₃ → 0` of bounded below complexes of sheaves of
`Λ`-modules on `Y_étale` with `RΓ(Y_k̄, Cᵢ|_{Y_k̄})` perfect, the characteristic series of the
canonical endomorphisms `Stacks.EtaleCohomology.frobeniusRestrictionCohomologyEndo` satisfy
`det(C₂) = det(C₁) · det(C₃)`. -/
theorem perfectDerivedCharSeries_frobeniusRestrictionCohomologyEndo_X₂_eq_mul
    {S : ShortComplex (CochainComplex (EtaleModules.{u, r} Λ Y.left) ℤ)} (hS : S.ShortExact)
    (h₁ : CochainComplex.plus _ S.X₁) (h₂ : CochainComplex.plus _ S.X₂)
    (h₃ : CochainComplex.plus _ S.X₃)
    (hp₁ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar ⟨S.X₁, h₁⟩)))))
    (hp₂ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar ⟨S.X₂, h₂⟩)))))
    (hp₃ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar ⟨S.X₃, h₃⟩))))) :
    CategoryTheory.FilteredDerived.perfectDerivedCharSeries Λ _ hp₂ (DerivedCategory.Plus.ι.map
        (frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard ⟨S.X₂, h₂⟩)) =
      CategoryTheory.FilteredDerived.perfectDerivedCharSeries Λ _ hp₁ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard ⟨S.X₁, h₁⟩)) *
        CategoryTheory.FilteredDerived.perfectDerivedCharSeries Λ _ hp₃ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard ⟨S.X₃, h₃⟩)) :=
  Functor.perfectDerivedCharSeries_derivedTwistEndo_X₂_eq_mul.{r, u + 1}
    (etaleModuleDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard))
    (etaleModuleDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar)))
    (etaleModuleDirectImageComp.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm)
    (fieldBaseChangeRestriction_shortExact.{u, r} Λ Y kbar hS)
    (((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
      ⟨S.X₁, h₁⟩).property)
    (((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
      ⟨S.X₂, h₂⟩).property)
    (((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
      ⟨S.X₃, h₃⟩).property)
    (ShortComplex.mapNatTrans S (NatTrans.mapHomologicalComplex
      (frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard) (ComplexShape.up ℤ))) hp₁ hp₂ hp₃

variable {Z U : Scheme.{u}} (i : Z ⟶ Y.left) [IsClosedImmersion i] (j : U ⟶ Y.left)
  [IsOpenImmersion j] (hij : Set.range j.base = (Set.range i.base)ᶜ)

include hij in
/-- **Multiplicativity of `det(1 - π T | RΓ(Y_k̄, -))` for an open and closed decomposition.**
For a closed immersion `i : Z ⟶ Y` with open complement `j : U ⟶ Y` and a bounded below complex
`C` on `Y_étale`, with the three cohomologies perfect,
`det(C) = det(j_! j^{-1} C) · det(i_* i^{-1} C)`. -/
theorem perfectDerivedCharSeries_frobeniusRestrictionCohomologyEndo_eq_mul_openClosed
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left))
    (hp₁ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar
            ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj
              ((etaleModuleRestriction.{u, r} Λ j).mapCochainComplexPlus.obj C)))))))
    (hp₂ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar C)))))
    (hp₃ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar
            ((etaleModuleDirectImage.{u, r} Λ i).mapCochainComplexPlus.obj
              ((etaleModuleInverseImage.{u, r} Λ i).mapCochainComplexPlus.obj C))))))) :
    CategoryTheory.FilteredDerived.perfectDerivedCharSeries Λ _ hp₂ (DerivedCategory.Plus.ι.map
        (frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard C)) =
      CategoryTheory.FilteredDerived.perfectDerivedCharSeries Λ _ hp₁ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard
            ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj
              ((etaleModuleRestriction.{u, r} Λ j).mapCochainComplexPlus.obj C)))) *
        CategoryTheory.FilteredDerived.perfectDerivedCharSeries Λ _ hp₃ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard
            ((etaleModuleDirectImage.{u, r} Λ i).mapCochainComplexPlus.obj
              ((etaleModuleInverseImage.{u, r} Λ i).mapCochainComplexPlus.obj C)))) :=
  perfectDerivedCharSeries_frobeniusRestrictionCohomologyEndo_X₂_eq_mul Λ Y kbar p q hcard
    (openClosedCochainShortComplex_shortExact Λ i j hij C.obj)
    ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj
      ((etaleModuleRestriction.{u, r} Λ j).mapCochainComplexPlus.obj C)).property C.property
    ((etaleModuleDirectImage.{u, r} Λ i).mapCochainComplexPlus.obj
      ((etaleModuleInverseImage.{u, r} Λ i).mapCochainComplexPlus.obj C)).property hp₁ hp₂ hp₃

end Frobenius

section CompactSupport

variable (Λ : Type r) [CommRing Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- **`det(1 - π_X^* T | RΓ_c(X_k̄, -))` is multiplicative along short exact sequences.** For a
short exact sequence `0 → K₁ → K₂ → K₃ → 0` of bounded below complexes of sheaves of
`Λ`-modules on `X_étale` with `RΓ_c(X_k̄, Kᵢ)` perfect,

`det(1 - π_X^* T | RΓ_c(X_k̄, K₂)) =`
`det(1 - π_X^* T | RΓ_c(X_k̄, K₁)) · det(1 - π_X^* T | RΓ_c(X_k̄, K₃))`

for the canonical action of `Stacks.EtaleCohomology.canonicalCompactSupportFrobenius` through one
compactification. -/
theorem perfectDerivedCharSeries_canonicalCompactSupportFrobenius_X₂_eq_mul
    {S : ShortComplex (CochainComplex (EtaleModules.{u, r} Λ X) ℤ)} (hS : S.ShortExact)
    (h₁ : CochainComplex.plus _ S.X₁) (h₂ : CochainComplex.plus _ S.X₂)
    (h₃ : CochainComplex.plus _ S.X₃)
    (hp₁ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar ⟨S.X₁, h₁⟩)))
    (hp₂ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar ⟨S.X₂, h₂⟩)))
    (hp₃ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar ⟨S.X₃, h₃⟩))) :
    CategoryTheory.FilteredDerived.perfectDerivedCharSeries Λ _ hp₂ (DerivedCategory.Plus.ι.map
        (canonicalCompactSupportFrobenius.{u, r} Λ f j kbar p q hcard ⟨S.X₂, h₂⟩)) =
      CategoryTheory.FilteredDerived.perfectDerivedCharSeries Λ _ hp₁ (DerivedCategory.Plus.ι.map
          (canonicalCompactSupportFrobenius.{u, r} Λ f j kbar p q hcard ⟨S.X₁, h₁⟩)) *
        CategoryTheory.FilteredDerived.perfectDerivedCharSeries Λ _ hp₃ (DerivedCategory.Plus.ι.map
          (canonicalCompactSupportFrobenius.{u, r} Λ f j kbar p q hcard ⟨S.X₃, h₃⟩)) :=
  Functor.perfectDerivedCharSeries_derivedTwistEndo_X₂_eq_mul.{r, u + 1}
    (etaleModuleDirectImage.{u, r} Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
    (etaleModuleDirectImage.{u, r} Λ (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)))
    (etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar)))
    (etaleModuleDirectImageComp.{u, r} Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase (Over.mk j.toBase) kbar p q hcard).symm)
    (compactSupportShortComplex_shortExact.{u, r} Λ f j kbar hS)
    (((etaleModuleInverseImage.{u, r} Λ
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
      ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj
        ⟨S.X₁, h₁⟩)).property)
    (((etaleModuleInverseImage.{u, r} Λ
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
      ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj
        ⟨S.X₂, h₂⟩)).property)
    (((etaleModuleInverseImage.{u, r} Λ
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
      ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj
        ⟨S.X₃, h₃⟩)).property)
    (compactSupportShortComplexTwist.{u, r} Λ f j kbar p q hcard S) hp₁ hp₂ hp₃

/-- **Multiplicativity of `det(1 - π_X^* T | RΓ_c(X_k̄, -))` along a short exact sequence of
sheaves**, each placed in degree `0`. -/
theorem perfectDerivedCharSeries_canonicalCompactSupportFrobenius_single_X₂_eq_mul
    {S : ShortComplex (EtaleModules.{u, r} Λ X)} (hS : S.ShortExact)
    (hp₁ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, r} Λ X) 0).obj S.X₁))))
    (hp₂ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, r} Λ X) 0).obj S.X₂))))
    (hp₃ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, r} Λ X) 0).obj S.X₃)))) :
    CategoryTheory.FilteredDerived.perfectDerivedCharSeries Λ _ hp₂ (DerivedCategory.Plus.ι.map
        (canonicalCompactSupportFrobenius.{u, r} Λ f j kbar p q hcard
          ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, r} Λ X) 0).obj S.X₂))) =
      CategoryTheory.FilteredDerived.perfectDerivedCharSeries Λ _ hp₁ (DerivedCategory.Plus.ι.map
          (canonicalCompactSupportFrobenius.{u, r} Λ f j kbar p q hcard
            ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, r} Λ X) 0).obj S.X₁))) *
        CategoryTheory.FilteredDerived.perfectDerivedCharSeries Λ _ hp₃ (DerivedCategory.Plus.ι.map
          (canonicalCompactSupportFrobenius.{u, r} Λ f j kbar p q hcard
            ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, r} Λ X) 0).obj S.X₃))) :=
  perfectDerivedCharSeries_canonicalCompactSupportFrobenius_X₂_eq_mul Λ f j kbar p q hcard
    (S := S.map (HomologicalComplex.single _ (ComplexShape.up ℤ) 0))
    (hS.map_of_exact _)
    ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, r} Λ X) 0).obj S.X₁).property
    ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, r} Λ X) 0).obj S.X₂).property
    ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, r} Λ X) 0).obj S.X₃).property
    hp₁ hp₂ hp₃

omit [Fintype k] in
/-- **Perfectness of `RΓ_c(X_k̄, -)` is two out of three along a short exact sequence of
sheaves**, each placed in degree `0`. -/
theorem isPerfect_compactSupportFrobeniusCohomology_single_X₂
    {S : ShortComplex (EtaleModules.{u, r} Λ X)} (hS : S.ShortExact)
    (hp₁ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, r} Λ X) 0).obj S.X₁))))
    (hp₃ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, r} Λ X) 0).obj S.X₃)))) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, r} Λ X) 0).obj S.X₂))) :=
  isPerfect_compactSupportFrobeniusCohomology_X₂ Λ f j kbar
    (S := S.map (HomologicalComplex.single _ (ComplexShape.up ℤ) 0))
    (hS.map_of_exact _)
    ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, r} Λ X) 0).obj S.X₁).property
    ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, r} Λ X) 0).obj S.X₂).property
    ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, r} Λ X) 0).obj S.X₃).property
    hp₁ hp₃

/-- **`det(1 - π_X^* T | RΓ_c(X_k̄, -))` is invariant under isomorphisms of complexes.** -/
theorem perfectDerivedCharSeries_canonicalCompactSupportFrobenius_congr
    {K K' : CochainComplex.Plus (EtaleModules.{u, r} Λ X)} (e : K ≅ K')
    (hp : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar K)))
    (hp' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar K'))) :
    CategoryTheory.FilteredDerived.perfectDerivedCharSeries Λ _ hp (DerivedCategory.Plus.ι.map
        (canonicalCompactSupportFrobenius.{u, r} Λ f j kbar p q hcard K)) =
      CategoryTheory.FilteredDerived.perfectDerivedCharSeries Λ _ hp' (DerivedCategory.Plus.ι.map
        (canonicalCompactSupportFrobenius.{u, r} Λ f j kbar p q hcard K')) :=
  CategoryTheory.FilteredDerived.perfectDerivedCharSeries_congr Λ hp hp'
    ((compactSupportFrobeniusFunctor.{u, r} Λ f j kbar ⋙ DerivedCategory.Plus.ι).mapIso e)
    _ _ ((Functor.whiskerRight (canonicalCompactSupportFrobeniusNatTrans.{u, r} Λ f j kbar p q
      hcard) DerivedCategory.Plus.ι).naturality e.hom).symm

end CompactSupport

end Stacks.EtaleCohomology
