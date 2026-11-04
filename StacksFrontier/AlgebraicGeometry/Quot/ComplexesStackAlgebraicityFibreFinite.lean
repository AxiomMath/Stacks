module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackAlgebraicityHeldFlat
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFibreLiftComparison
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFibreFiniteShift
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperDescentOverPullback
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFibreLiftAutomorphisms

/-!
# Stacks 0DLN with the fibre hypotheses of Stacks 0DLL discharged

`ComplexesSituation.isAlgebraicStack_complexes_of_held_of_adjoinDescent` proves Stacks 0DLN
granted results not yet proved here and the steps still internal to this chapter, among them the
two fibre hypotheses of Stacks 0DLL on `Complexes_{X/Y}`: the tangent-space hypothesis `h0DLLT`
(`AlgebraicGeometry.Space.ComplexesSituation.FibreTangentFinite`) and the
infinitesimal-automorphism hypothesis `h0DLLInf`
(`AlgebraicGeometry.Space.ComplexesSituation.FibreInfFinite`). This file proves both at every
field point `x₀` from

* Stacks 0D0T (`h0D0T`, **not yet proved here**), which makes
  `Ext¹(E₀, E₀)` and `Ext⁰(E₀, E₀)` finite dimensional;
* for `h0DLLT`: the coefficient lift comparison of the fibre
  (`AlgebraicGeometry.Space.ComplexesSituation.fibreCoefficientLiftComparison`) at `K₀ = E₀⟦m⟧`,
  `m` an upper bound of the bounded complex `E₀`, whose compatibility with pullback of lifts
  (`hpull`, `AlgebraicGeometry.Space.ComplexesSituation.FibreLiftClassPullback`) is
  **internal, 0DLL-G4-2, pending**
  (`AlgebraicGeometry.Space.ComplexesSituation.fibreTangentFinite_of_fibreLiftClassPullback`);
* for `h0DLLInf`: the maps `g ↦ 1 + g` from `Hom(E₀, E₀ ⊗^L (𝒪 ⊗_k V))` onto the infinitesimal
  automorphisms of the trivial deformations
  (`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftUnipotentAut`, onto by Stacks 0DIZ (1)),
  whose naturality in `V` (`hnat`,
  `AlgebraicGeometry.Space.ComplexesSituation.FibreTrivialAutNatural`) is **internal, pending**
  (the comparison `chi` of 0DLL-G23 / 0DLL-G4-2)
  (`AlgebraicGeometry.Space.ComplexesSituation.fibreInfFinite_of_fibreTrivialAutNatural`);
* condition (RS*) of `Complexes_{X/Y}`
  (`AlgebraicGeometry.Space.ComplexesSituation.satisfiesRSStar_complexesFunctor`, from the
  hypotheses `h0DKY`, `h0DLC3`, `h07W3`, `h0DL7`, `h0DL4` already present),

and states Stacks 0DLN without `h0DLLT` and `h0DLLInf`
(`ComplexesSituation.isAlgebraicStack_complexes_of_held_of_fibreLiftClassPullback`).
Nothing is registered.

## References

* [Stacks Project, Tag 0DLN](https://stacks.math.columbia.edu/tag/0DLN)
* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
* [Stacks Project, Tag 0D0T](https://stacks.math.columbia.edu/tag/0D0T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin Deformation.ComplexLift

universe u z

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}}


attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

attribute [local instance] complexesCategory

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

/-- The test scheme of a field point over `Spec k ⟶ Spec Λ ⟶ S` lies in the site: `Spec k` is
contained in `B`. -/
theorem contains_spec_of_fieldPoint {S : Scheme.{u}} {hS : B.Contains S}
    {D : ComplexesSituation B S hS} {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {iΛ : Spec (.of Λ) ⟶ S} {x₀ : ComplexesObject D}
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    B.Contains (Spec (.of k)) := by
  have h : x₀.T.left.left.obj = Spec (.of k) := congrArg (fun U => U.left) hx₀
  exact h ▸ x₀.T.left.left.property

/-- The complex of a field point of `Complexes_{X/Y}` is bounded above. -/
private theorem exists_isLE_of_fieldPoint {S : Scheme.{u}} {hS : B.Contains S}
    (D : ComplexesSituation B S hS) {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hk : B.Contains (Spec (.of k))) : ∃ n, x₀.E.IsLE n := by
  obtain ⟨⟨⟨n, hn⟩, -⟩, -⟩ := D.derivedCategoryBMinus_and_plus_of_isRelativelyPerfect hk _ x₀.T
    (fieldPoint_left_eq D iΛ x₀ hx₀ hk) x₀.E x₀.relativelyPerfect
  exact ⟨n, (Stacks.DerivedCategory.isBoundedAboveBy_iff_isLE _ _).1 hn⟩

/-- **The tangent-space hypothesis of Stacks 0DLL on the fibre**, at a field point `x₀`, from
Stacks 0D0T, condition (RS*) of `Complexes_{X/Y}` and the compatibility of the classes of lifts
of `E₀⟦m⟧` with pullback for every `m`: the comparison
`AlgebraicGeometry.Space.ComplexesSituation.fibreCoefficientLiftComparison` at a shift `E₀⟦m⟧`
in `D^{≤ 0}` (`m` an upper bound of `E₀`, which is bounded above), fed to
`ComplexesSituation.fibreTangentFinite_of_coefficientLiftComparison_fieldPointShift`.

`h0D0T` is **Stacks 0D0T, not yet proved here**; `hpull` is
**internal, 0DLL-G4-2, pending**. -/
theorem fibreTangentFinite_of_fibreLiftClassPullback {S : Scheme.{u}} {hS : B.Contains S}
    (D : ComplexesSituation B S hS)
    (h0D0T : ∀ (A : Type u) [CommRing A] (hA : B.Contains (Spec (.of A)))
      (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
      (hX : IsAlgebraicSpace B (Spec (.of A)) hA X),
      letI : Linear A (Modules.{u, u} B (Spec (.of A)) hA X hX) :=
        Linear.ofRingHom (baseRingHom A B hA X hX)
      ∀ [IsNoetherianRing A] (f : X ⟶ yoneda.obj (baseObject A B hA)),
        IsProper B (Spec (.of A)) hA f →
        ∀ (K L : DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X hX)),
          DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) K →
          DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) L →
          ∀ n : ℤ, Module.Finite A (K ⟶ L⟦n⟧))
    (hfib : (complexesFunctor D).IsFiberedInGroupoids)
    (rsC : SatisfiesRSStar B S hS (complexesFunctor D) hfib)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hk : B.Contains (Spec (.of k)))
    [hDer : ∀ V : FGModuleCat.{u} k, HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]
    (hpull : ∀ (hK : DerivedCategory.TStructure.t.minus x₀.E)
      (m : ℤ) (hKm : DerivedCategory.TStructure.t.minus (x₀.E⟦m⟧)),
      FibreLiftClassPullback (hDer := hDer) hK m hKm) :
    FibreTangentFinite D iΛ x₀ hx₀ := by
  obtain ⟨n, hn'⟩ := exists_isLE_of_fieldPoint D iΛ x₀ hx₀ hk
  have hm : (x₀.E⟦n⟧).IsLE 0 := DerivedCategory.TStructure.t.isLE_shift x₀.E n n 0 (by omega)
  exact fibreTangentFinite_of_coefficientLiftComparison_fieldPointShift D h0D0T hfib rsC iΛ x₀
    hx₀ hk hfinite hqc n ⟨0, hm⟩
    (fibreCoefficientLiftComparison ⟨n, hn'⟩ n hm (hpull ⟨n, hn'⟩ n ⟨0, hm⟩))

/-- **The infinitesimal-automorphism hypothesis of Stacks 0DLL on the fibre**, at a field point
`x₀`, from Stacks 0D0T, condition (RS*) of `Complexes_{X/Y}` and the naturality of `g ↦ 1 + g` on
the trivial deformations (`AlgebraicGeometry.Space.ComplexesSituation.FibreTrivialAutNatural`):
`AlgebraicGeometry.Space.ComplexesSituation.fibreInfFinite_of_coefficientHom_fieldPoint` with
`θ_V = AlgebraicGeometry.Space.ComplexesSituation.fibreLiftUnipotentAut`, onto by
`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftUnipotentAut_surjective`.

`h0D0T` is **Stacks 0D0T, not yet proved here**; `hnat` is
**internal, pending** (the comparison `chi` of 0DLL-G23 / 0DLL-G4-2). -/
theorem fibreInfFinite_of_fibreTrivialAutNatural {S : Scheme.{u}} {hS : B.Contains S}
    (D : ComplexesSituation B S hS)
    (h0D0T : ∀ (A : Type u) [CommRing A] (hA : B.Contains (Spec (.of A)))
      (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
      (hX : IsAlgebraicSpace B (Spec (.of A)) hA X),
      letI : Linear A (Modules.{u, u} B (Spec (.of A)) hA X hX) :=
        Linear.ofRingHom (baseRingHom A B hA X hX)
      ∀ [IsNoetherianRing A] (f : X ⟶ yoneda.obj (baseObject A B hA)),
        IsProper B (Spec (.of A)) hA f →
        ∀ (K L : DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X hX)),
          DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) K →
          DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) L →
          ∀ n : ℤ, Module.Finite A (K ⟶ L⟦n⟧))
    (rsC : SatisfiesRSStar B S hS (complexesFunctor D) (complexesFunctor_isFiberedInGroupoids D))
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hk : B.Contains (Spec (.of k)))
    [hDer : ∀ V : FGModuleCat.{u} k, HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]
    (hnat : ∀ hK : DerivedCategory.TStructure.t.minus x₀.E,
      FibreTrivialAutNatural (hDer' := hDer) (complexesFunctor_isFiberedInGroupoids D) hK) :
    FibreInfFinite D iΛ x₀ hx₀ := by
  obtain ⟨n, hn'⟩ := exists_isLE_of_fieldPoint D iΛ x₀ hx₀ hk
  exact fibreInfFinite_of_coefficientHom_fieldPoint D h0D0T
    (complexesFunctor_isFiberedInGroupoids D) rsC iΛ x₀ hx₀ hk ⟨n, hn'⟩
    (fun V g => fibreLiftUnipotentAut (hDer' := hDer) (V := V) _ ⟨n, hn'⟩ g)
    (fun f g => hnat ⟨n, hn'⟩ f g)
    (fibreLiftUnipotentAut_surjective (hDer' := hDer) _ ⟨n, hn'⟩)

/-- **Stacks 0DLN, granted results not yet proved here, with the fibre hypotheses of Stacks
0DLL discharged.** This is
`ComplexesSituation.isAlgebraicStack_complexes_of_held_of_adjoinDescent` with `h0DLLT` proved by
`AlgebraicGeometry.Space.ComplexesSituation.fibreTangentFinite_of_fibreLiftClassPullback` and
`h0DLLInf` by `ComplexesSituation.fibreInfFinite_of_fibreTrivialAutNatural`, from

* `h0D0T`: **Stacks 0D0T, not yet proved here**;
* `hpull`: the compatibility of the classes of lifts of `E₀⟦m⟧` with pullback of lifts of the
  base point of the fibre (`AlgebraicGeometry.Space.ComplexesSituation.FibreLiftClassPullback`),
  **internal, 0DLL-G4-2, pending**;
* `hnat`: the naturality of `g ↦ 1 + g` on the trivial deformations
  (`AlgebraicGeometry.Space.ComplexesSituation.FibreTrivialAutNatural`), **internal, pending**.

The other hypotheses are those of
`ComplexesSituation.isAlgebraicStack_complexes_of_held_of_adjoinDescent`, with the same marks;
condition (RS*) of `Complexes_{X/Y}` comes from `h0DKY`, `h0DLC3`, `h07W3`, `h0DL7` and `h0DL4`. -/
theorem isAlgebraicStack_complexes_of_held_of_fibreLiftClassPullback
    (h0D0T : ∀ (A : Type u) [CommRing A] (hA : B.Contains (Spec (.of A)))
      (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
      (hX : IsAlgebraicSpace B (Spec (.of A)) hA X),
      letI : Linear A (Modules.{u, u} B (Spec (.of A)) hA X hX) :=
        Linear.ofRingHom (baseRingHom A B hA X hX)
      ∀ [IsNoetherianRing A] (f : X ⟶ yoneda.obj (baseObject A B hA)),
        IsProper B (Spec (.of A)) hA f →
        ∀ (K L : DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X hX)),
          DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) K →
          DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) L →
          ∀ n : ℤ, Module.Finite A (K ⟶ L⟦n⟧))
    (hpull : ∀ {S : Scheme.{u}} {hS : B.Contains S} (D : ComplexesSituation B S hS)
      {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
      (x₀ : ComplexesObject D)
      (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (hk : B.Contains (Spec (.of k)))
      [hDer : ∀ V : FGModuleCat.{u} k, HasDerivedCategory.{u + 1} (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]
      (hK : DerivedCategory.TStructure.t.minus x₀.E)
      (m : ℤ) (hKm : DerivedCategory.TStructure.t.minus (x₀.E⟦m⟧)),
      FibreLiftClassPullback (hDer := hDer) hK m hKm)
    (hnat : ∀ {S : Scheme.{u}} {hS : B.Contains S} (D : ComplexesSituation B S hS)
      {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
      (x₀ : ComplexesObject D)
      (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (hk : B.Contains (Spec (.of k)))
      [hDer : ∀ V : FGModuleCat.{u} k, HasDerivedCategory.{u + 1} (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]
      (hK : DerivedCategory.TStructure.t.minus x₀.E),
      FibreTrivialAutNatural (hDer' := hDer) (complexesFunctor_isFiberedInGroupoids D) hK)
    (h08K1 : ∀ (A : Type u) [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
      (hZ : B.Contains (⊤_ Scheme.{u})) (i : (Finset A)ᵒᵖ)
      {X Y : Over ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).obj i)} (f : X ⟶ Y),
      IsQuasiCompactSpace B _ hZ ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).obj i) →
      IsAbsolutelyQuasiSeparated B _ hZ hZ ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).obj i) →
      IsAlgebraicSpace B _ hZ X.left → IsAlgebraicSpace B _ hZ Y.left →
      IsQuasiCompactSpace B _ hZ X.left → IsAbsolutelyQuasiSeparated B _ hZ hZ X.left →
      IsQuasiCompactSpace B _ hZ Y.left → IsAbsolutelyQuasiSeparated B _ hZ hZ Y.left →
      IsProper B _ hZ
        ((Over.pullback (limit.π (adjoinSiteDiagram B hZ A hA ⋙ yoneda) i)).map f).left →
      IsLocallyOfFiniteType B _ hZ f.left →
      ∃ (j : (Finset A)ᵒᵖ) (e : j ⟶ i),
        IsProper B _ hZ
          ((Over.pullback ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).map e)).map f).left)
    (hcomp : ChangeOfBaseComparison.{u, z} B)
    (h0DLC2 : ∀ {S : Scheme.{u}} (hS : B.Contains S), NegativeExtVanishesOfFibres B S hS)
    (h0DKY : ∀ {S : Scheme.{u}} (hS : B.Contains S), RelativeDerivedHomDualExists B S hS)
    (h0DLC3 : ∀ {S : Scheme.{u}} (hS : B.Contains S),
      RelativeDerivedHomRepresentableOfFibres B S hS)
    (h0DKW : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      D.RelativelyPerfectColimit)
    (h0DIQ : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D : ComplexesSituation B _ hΛ)
      {level : ℕ → SchemesOver D.Y} {transition : ∀ n, level n ⟶ level (n + 1)}
      (L : D.SpecLimitTower level transition)
      (K : ∀ n, derivedModules B _ hΛ (D.space (level n))),
      (∀ n, (smallEtaleRingedSite B _ hΛ (D.space (level n)).1
        (D.space (level n)).2).IsPseudoCoherent (K n)) →
      ∀ (φ : ∀ n, ((smallEtaleDerivedPullbackData B _ hΛ).pull
        (D.relativeMap (transition n))).obj (K (n + 1)) ⟶ K n), (∀ n, IsIso (φ n)) →
      ∃ (E : derivedModules B _ hΛ (D.space L.T)),
        (smallEtaleRingedSite B _ hΛ (D.space L.T).1 (D.space L.T).2).IsPseudoCoherent E ∧
        ∃ ψ : ∀ n, ((smallEtaleDerivedPullbackData B _ hΛ).pull
          (D.relativeMap (L.toLimit n))).obj E ⟶ K n, (∀ n, IsIso (ψ n)) ∧
          ∀ n, Functor.fibreComp (D.compComparison (transition n) (L.toLimit (n + 1))) (φ n)
              (ψ (n + 1)) =
            (D.relativeMapComparison (L.transition_toLimit n)).hom.app E ≫ ψ n)
    (h0DLA : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      D.CechDescent)
    (h07Y4 : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ)))
      (𝒳 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1}
        (BigFppfOver B (Spec (CommRingCat.of Λ)) hΛ)),
      Stack.HasRepresentableDiagonal B _ hΛ 𝒳 →
      (∃ T : BigFppfOver B _ hΛ,
        ∀ (U : BigFppfOver B _ hΛ) (k : Type u) [Field k],
          U.left.1 = Spec (.of k) → Deformation.Artin.IsFiniteTypeOver B _ hΛ U →
          Cardinal.lift.{u, u + 1}
              (Cardinal.mk (Quotient (isIsomorphicSetoid (𝒳.val.p.Fiber U)))) ≤
            Cardinal.lift.{u + 1, u} T.left.1.size) →
      𝒳.val.p.IsStackInGroupoids.{u + 1} ((etaleTopology B).over (B.obj hΛ)) →
      Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B _ hΛ 𝒳 →
      Deformation.Artin.SatisfiesRS B _ hΛ 𝒳.val.p 𝒳.property →
      (∀ (k : Type u) [Field k] (i₀ : Spec (.of k) ⟶ Spec (CommRingCat.of Λ))
          (x₀ : 𝒳.val.obj)
          (hx₀ : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ = Over.mk i₀),
          LocallyOfFiniteType i₀ → QuasiCompact i₀ →
          ∀ (s : Spec (CommRingCat.of Λ)), i₀ (IsLocalRing.closedPoint k) = s →
          ∀ (Λ' : Type u) [CommRing Λ'] [Algebra Λ' k]
            (_hΛstalk : Λ' = (Spec (CommRingCat.of Λ)).presheaf.stalk s)
            (iΛ : Spec (.of Λ') ⟶ Spec (CommRingCat.of Λ))
            (_hiΛ : HEq iΛ ((Spec (CommRingCat.of Λ)).fromSpecStalk s))
            (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ = i₀),
            let hx : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ =
              Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ) :=
              hx₀.trans (congrArg Over.mk hbase.symm)
            let D := Deformation.Artin.predeformationCategory iΛ
              (𝒳.val.p ⋙ Over.post B.inclusion) x₀ hx
            letI : Category D.carrier := D.category
            ∀ hD : Deformation.IsDeformationCategory D.projection,
              let 𝓕 := BasedCategory.ofFunctor D.projection
              let hS2 :=
                schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
                  𝓕 hD
              letI : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
              letI : Fact (Deformation.SchlessingerConditionS2
                (CategoryOfElements.π
                  (Deformation.isomorphismClasses 𝓕 hD.predeformation.cofibered))) := ⟨hS2⟩
              let F := Deformation.isomorphismClasses 𝓕 hD.predeformation.cofibered
              let T := Deformation.artinianTangentSpace Λ' k F
              letI : AddCommGroup T := Deformation.associatedTangentSpaceAddCommGroupUnlifted 𝓕
              letI : Module k T := Deformation.associatedTangentSpaceModuleUnlifted 𝓕
              FiniteDimensional k T) →
      (∀ ξ : Deformation.Artin.FormalObject B _ hΛ 𝒳.val.p,
        Deformation.Artin.FormalObject.IsEffective B _ hΛ 𝒳.val.p 𝒳.property ξ) →
      (∀ U : Over (Spec (CommRingCat.of Λ)), LocallyOfFiniteType U.hom →
        ∀ (y : 𝒳.val.obj) (hy : (𝒳.val.p ⋙ Over.post B.inclusion).obj y = U) (u : U.left),
          _root_.AlgebraicGeometry.IsFiniteTypePoint u →
          Deformation.Artin.IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u y hy →
          ∃ V : U.left.Opens, u ∈ V.1 ∧
            ∀ u' : U.left, u' ∈ V.1 → _root_.AlgebraicGeometry.IsFiniteTypePoint u' →
              Deformation.Artin.IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u' y hy) →
      (∀ s : Spec (CommRingCat.of Λ), _root_.AlgebraicGeometry.IsFiniteTypePoint s →
        IsGRing ((Spec (CommRingCat.of Λ)).presheaf.stalk s)) →
      Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B _ hΛ 𝒳.val)
    (h0CXU : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D : ComplexesSituation B _ hΛ)
      (U : Over (Spec (CommRingCat.of Λ))), LocallyOfFiniteType U.hom →
      ∀ (y : ComplexesObject D) (hy : (complexesFunctor D ⋙ Over.post B.inclusion).obj y = U)
        (u : U.left), _root_.AlgebraicGeometry.IsFiniteTypePoint u →
        Deformation.Artin.IsVersalAt U (complexesFunctor D ⋙ Over.post B.inclusion) u y hy →
        ∃ V : U.left.Opens, u ∈ V.1 ∧
          ∀ u' : U.left, u' ∈ V.1 → _root_.AlgebraicGeometry.IsFiniteTypePoint u' →
            Deformation.Artin.IsVersalAt U (complexesFunctor D ⋙ Over.post B.inclusion) u' y
              hy)
    (h07W3 : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ)))
      {Z Z' Y Y' : BigFppfOver B _ hΛ} (i : Z ⟶ Z') (f : Z ⟶ Y) (a : Z' ⟶ Y') (b : Y ⟶ Y'),
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B _ hΛ).map i) →
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B _ hΛ).map f) →
      IsPushout ((BigFppfOver.toScheme B _ hΛ).map i) ((BigFppfOver.toScheme B _ hΛ).map f)
        ((BigFppfOver.toScheme B _ hΛ).map a) ((BigFppfOver.toScheme B _ hΛ).map b) →
      ∀ {W WY WZ' WZ : AlgebraicSpaces B _ hΛ} (π : W ⟶ schemeSpace Y')
        (πY : WY ⟶ schemeSpace Y) (πZ' : WZ' ⟶ schemeSpace Z') (πZ : WZ ⟶ schemeSpace Z)
        (n : WY ⟶ W) (m : WZ' ⟶ W) (l : WZ ⟶ WY) (k : WZ ⟶ WZ'),
        IsFlat B _ hΛ π.hom →
        IsPullback n πY π (schemeSpaceMap b) → IsPullback m πZ' π (schemeSpaceMap a) →
        IsPullback l πZ πY (schemeSpaceMap f) → k ≫ πZ' = πZ ≫ schemeSpaceMap i →
        l ≫ n = k ≫ m → IsPushout k l m n)
    (h0DL7 : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ)))
      {P P' Q Q' : AlgebraicSpaces B _ hΛ} (k : P ⟶ P') (l : P ⟶ Q) (m : P' ⟶ Q')
      (n : Q ⟶ Q') (hsq : IsPushout k l m n),
      IsThickeningHom B _ hΛ k → IsAffineHom B _ hΛ l.hom →
      ∀ (M : derivedModules B _ hΛ Q) (K' : derivedModules B _ hΛ P'),
        IsPseudoCoherentObject M → IsPseudoCoherentObject K' →
        ∀ α : ((smallEtaleDerivedPullbackData B _ hΛ).pull l).obj M ≅
            ((smallEtaleDerivedPullbackData B _ hΛ).pull k).obj K',
          ∃ (N : derivedModules B _ hΛ Q')
            (eQ : ((smallEtaleDerivedPullbackData B _ hΛ).pull n).obj N ≅ M)
            (eP' : ((smallEtaleDerivedPullbackData B _ hΛ).pull m).obj N ≅ K'),
            ((smallEtaleDerivedPullbackData B _ hΛ).pull l).map eQ.hom ≫ α.hom =
              ((smallEtaleDerivedPullbackData B _ hΛ).compIso l n).inv.app N ≫
                eqToHom (congrArg
                  (fun g => ((smallEtaleDerivedPullbackData B _ hΛ).pull g).obj N)
                  hsq.w.symm) ≫
                ((smallEtaleDerivedPullbackData B _ hΛ).compIso k m).hom.app N ≫
                ((smallEtaleDerivedPullbackData B _ hΛ).pull k).map eP'.hom)
    (h0DL4 : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D : ComplexesSituation B _ hΛ)
      {T T' : SchemesOver D.Y} (h : T ⟶ T'),
      Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B _ hΛ).map h.left) →
      ∀ (E' : derivedModules B _ hΛ (D.space T')) (E : derivedModules B _ hΛ (D.space T)),
        (((smallEtaleDerivedPullbackData B _ hΛ).pull (D.relativeMap h)).obj E' ≅ E) →
        D.IsRelativelyPerfect T E → D.IsRelativelyPerfect T' E')
    {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS (complexesBasedCategory D) :=
  isAlgebraicStack_complexes_of_held_of_adjoinDescent h08K1 hcomp h0DLC2 h0DKY h0DLC3 h0DKW h0DIQ
    (fun Λ₀ _ _ hΛ D' _ _ _ _ _ iΛ x₀ hx₀ hfinite hqc =>
      fibreTangentFinite_of_fibreLiftClassPullback D' h0D0T
        (complexesFunctor_isFiberedInGroupoids D')
        (satisfiesRSStar_complexesFunctor D' (complexesFunctor_isFiberedInGroupoids D')
          (complexes_hasRepresentableDiagonal D'
            (existsNegativeExtLocus_of_dualExists B _ hΛ (h0DKY hΛ)) (h0DLC3 hΛ)
            (complexesFunctor_isFiberedInGroupoids D'))
          (h07W3 Λ₀ hΛ) (h0DL7 Λ₀ hΛ) (h0DL4 Λ₀ hΛ D'))
        iΛ x₀ hx₀ hfinite hqc (contains_spec_of_fieldPoint hx₀)
        (hDer := fun _ => (HasDerivedCategory.standard _ : HasDerivedCategory.{u + 1} _))
        (hpull D' iΛ x₀ hx₀ (contains_spec_of_fieldPoint hx₀)
          (hDer := fun _ => (HasDerivedCategory.standard _ : HasDerivedCategory.{u + 1} _))))
    (fun Λ₀ _ _ hΛ D' _ _ _ _ _ iΛ x₀ hx₀ _ _ =>
      fibreInfFinite_of_fibreTrivialAutNatural D' h0D0T
        (satisfiesRSStar_complexesFunctor D' (complexesFunctor_isFiberedInGroupoids D')
          (complexes_hasRepresentableDiagonal D'
            (existsNegativeExtLocus_of_dualExists B _ hΛ (h0DKY hΛ)) (h0DLC3 hΛ)
            (complexesFunctor_isFiberedInGroupoids D'))
          (h07W3 Λ₀ hΛ) (h0DL7 Λ₀ hΛ) (h0DL4 Λ₀ hΛ D'))
        iΛ x₀ hx₀ (contains_spec_of_fieldPoint hx₀)
        (hDer := fun _ => (HasDerivedCategory.standard _ : HasDerivedCategory.{u + 1} _))
        (hnat D' iΛ x₀ hx₀ (contains_spec_of_fieldPoint hx₀)
          (hDer := fun _ => (HasDerivedCategory.standard _ : HasDerivedCategory.{u + 1} _))))
    h0DLA h07Y4 h0CXU h07W3 h0DL7 h0DL4 hS D

/-- **The tangent-space hypothesis of Stacks 0DLL on the fibre** (unregistered):
`AlgebraicGeometry.Space.ComplexesSituation.fibreTangentFinite_of_fibreLiftClassPullback` with its
hypothesis `h0D0T` discharged by Stacks 0D0T,
`AlgebraicGeometry.Space.moduleFinite_hom_shift_of_isProper_ofRingHom` (the base's
`AlgebraicGeometry.Space.moduleFinite_hom_shift_of_isProper`). The other hypotheses are those of
`fibreTangentFinite_of_fibreLiftClassPullback`, with the same marks. -/
theorem fibreTangentFinite_of_fibreLiftClassPullback_finiteExt {S : Scheme.{u}} {hS : B.Contains S}
    (D : ComplexesSituation B S hS)
    (hfib : (complexesFunctor D).IsFiberedInGroupoids)
    (rsC : SatisfiesRSStar B S hS (complexesFunctor D) hfib)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hk : B.Contains (Spec (.of k)))
    [hDer : ∀ V : FGModuleCat.{u} k, HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]
    (hpull : ∀ (hK : DerivedCategory.TStructure.t.minus x₀.E)
      (m : ℤ) (hKm : DerivedCategory.TStructure.t.minus (x₀.E⟦m⟧)),
      FibreLiftClassPullback (hDer := hDer) hK m hKm) :
    FibreTangentFinite D iΛ x₀ hx₀ :=
  fibreTangentFinite_of_fibreLiftClassPullback D
    (fun A _ hA X hX => moduleFinite_hom_shift_of_isProper_ofRingHom B A hA X hX)
    hfib rsC iΛ x₀ hx₀ hfinite hqc hk hpull (hDer := hDer)

/-- **The infinitesimal-automorphism hypothesis of Stacks 0DLL on the fibre** (unregistered):
`AlgebraicGeometry.Space.ComplexesSituation.fibreInfFinite_of_fibreTrivialAutNatural` with its
hypothesis `h0D0T` discharged by Stacks 0D0T,
`AlgebraicGeometry.Space.moduleFinite_hom_shift_of_isProper_ofRingHom` (the base's
`AlgebraicGeometry.Space.moduleFinite_hom_shift_of_isProper`). The other hypotheses are those of
`fibreInfFinite_of_fibreTrivialAutNatural`, with the same marks. -/
theorem fibreInfFinite_of_fibreTrivialAutNatural_finiteExt {S : Scheme.{u}} {hS : B.Contains S}
    (D : ComplexesSituation B S hS)
    (rsC : SatisfiesRSStar B S hS (complexesFunctor D) (complexesFunctor_isFiberedInGroupoids D))
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hk : B.Contains (Spec (.of k)))
    [hDer : ∀ V : FGModuleCat.{u} k, HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]
    (hnat : ∀ hK : DerivedCategory.TStructure.t.minus x₀.E,
      FibreTrivialAutNatural (hDer' := hDer) (complexesFunctor_isFiberedInGroupoids D) hK) :
    FibreInfFinite D iΛ x₀ hx₀ :=
  fibreInfFinite_of_fibreTrivialAutNatural D
    (fun A _ hA X hX => moduleFinite_hom_shift_of_isProper_ofRingHom B A hA X hX)
    rsC iΛ x₀ hx₀ hk hnat (hDer := hDer)

/-- **Stacks 0DLN, granted results not yet proved here other than Stacks 0D0T, with the fibre
hypotheses of Stacks 0DLL discharged** (unregistered).
`ComplexesSituation.isAlgebraicStack_complexes_of_held_of_fibreLiftClassPullback` with its
hypothesis `h0D0T` discharged by Stacks 0D0T,
`AlgebraicGeometry.Space.moduleFinite_hom_shift_of_isProper_ofRingHom` (the base's
`AlgebraicGeometry.Space.moduleFinite_hom_shift_of_isProper`). The other hypotheses are those of
`isAlgebraicStack_complexes_of_held_of_fibreLiftClassPullback`, with the same marks: `hpull` and
`hnat` **internal, pending** (0DLL-G4c). -/
theorem isAlgebraicStack_complexes_of_held_of_fibreLiftClassPullback_finiteExt
    (hpull : ∀ {S : Scheme.{u}} {hS : B.Contains S} (D : ComplexesSituation B S hS)
      {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
      (x₀ : ComplexesObject D)
      (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (hk : B.Contains (Spec (.of k)))
      [hDer : ∀ V : FGModuleCat.{u} k, HasDerivedCategory.{u + 1} (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]
      (hK : DerivedCategory.TStructure.t.minus x₀.E)
      (m : ℤ) (hKm : DerivedCategory.TStructure.t.minus (x₀.E⟦m⟧)),
      FibreLiftClassPullback (hDer := hDer) hK m hKm)
    (hnat : ∀ {S : Scheme.{u}} {hS : B.Contains S} (D : ComplexesSituation B S hS)
      {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
      (x₀ : ComplexesObject D)
      (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (hk : B.Contains (Spec (.of k)))
      [hDer : ∀ V : FGModuleCat.{u} k, HasDerivedCategory.{u + 1} (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]
      (hK : DerivedCategory.TStructure.t.minus x₀.E),
      FibreTrivialAutNatural (hDer' := hDer) (complexesFunctor_isFiberedInGroupoids D) hK)
    (h08K1 : ∀ (A : Type u) [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
      (hZ : B.Contains (⊤_ Scheme.{u})) (i : (Finset A)ᵒᵖ)
      {X Y : Over ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).obj i)} (f : X ⟶ Y),
      IsQuasiCompactSpace B _ hZ ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).obj i) →
      IsAbsolutelyQuasiSeparated B _ hZ hZ ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).obj i) →
      IsAlgebraicSpace B _ hZ X.left → IsAlgebraicSpace B _ hZ Y.left →
      IsQuasiCompactSpace B _ hZ X.left → IsAbsolutelyQuasiSeparated B _ hZ hZ X.left →
      IsQuasiCompactSpace B _ hZ Y.left → IsAbsolutelyQuasiSeparated B _ hZ hZ Y.left →
      IsProper B _ hZ
        ((Over.pullback (limit.π (adjoinSiteDiagram B hZ A hA ⋙ yoneda) i)).map f).left →
      IsLocallyOfFiniteType B _ hZ f.left →
      ∃ (j : (Finset A)ᵒᵖ) (e : j ⟶ i),
        IsProper B _ hZ
          ((Over.pullback ((adjoinSiteDiagram B hZ A hA ⋙ yoneda).map e)).map f).left)
    (hcomp : ChangeOfBaseComparison.{u, z} B)
    (h0DLC2 : ∀ {S : Scheme.{u}} (hS : B.Contains S), NegativeExtVanishesOfFibres B S hS)
    (h0DKY : ∀ {S : Scheme.{u}} (hS : B.Contains S), RelativeDerivedHomDualExists B S hS)
    (h0DLC3 : ∀ {S : Scheme.{u}} (hS : B.Contains S),
      RelativeDerivedHomRepresentableOfFibres B S hS)
    (h0DKW : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      D.RelativelyPerfectColimit)
    (h0DIQ : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D : ComplexesSituation B _ hΛ)
      {level : ℕ → SchemesOver D.Y} {transition : ∀ n, level n ⟶ level (n + 1)}
      (L : D.SpecLimitTower level transition)
      (K : ∀ n, derivedModules B _ hΛ (D.space (level n))),
      (∀ n, (smallEtaleRingedSite B _ hΛ (D.space (level n)).1
        (D.space (level n)).2).IsPseudoCoherent (K n)) →
      ∀ (φ : ∀ n, ((smallEtaleDerivedPullbackData B _ hΛ).pull
        (D.relativeMap (transition n))).obj (K (n + 1)) ⟶ K n), (∀ n, IsIso (φ n)) →
      ∃ (E : derivedModules B _ hΛ (D.space L.T)),
        (smallEtaleRingedSite B _ hΛ (D.space L.T).1 (D.space L.T).2).IsPseudoCoherent E ∧
        ∃ ψ : ∀ n, ((smallEtaleDerivedPullbackData B _ hΛ).pull
          (D.relativeMap (L.toLimit n))).obj E ⟶ K n, (∀ n, IsIso (ψ n)) ∧
          ∀ n, Functor.fibreComp (D.compComparison (transition n) (L.toLimit (n + 1))) (φ n)
              (ψ (n + 1)) =
            (D.relativeMapComparison (L.transition_toLimit n)).hom.app E ≫ ψ n)
    (h0DLA : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      D.CechDescent)
    (h07Y4 : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ)))
      (𝒳 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1}
        (BigFppfOver B (Spec (CommRingCat.of Λ)) hΛ)),
      Stack.HasRepresentableDiagonal B _ hΛ 𝒳 →
      (∃ T : BigFppfOver B _ hΛ,
        ∀ (U : BigFppfOver B _ hΛ) (k : Type u) [Field k],
          U.left.1 = Spec (.of k) → Deformation.Artin.IsFiniteTypeOver B _ hΛ U →
          Cardinal.lift.{u, u + 1}
              (Cardinal.mk (Quotient (isIsomorphicSetoid (𝒳.val.p.Fiber U)))) ≤
            Cardinal.lift.{u + 1, u} T.left.1.size) →
      𝒳.val.p.IsStackInGroupoids.{u + 1} ((etaleTopology B).over (B.obj hΛ)) →
      Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B _ hΛ 𝒳 →
      Deformation.Artin.SatisfiesRS B _ hΛ 𝒳.val.p 𝒳.property →
      (∀ (k : Type u) [Field k] (i₀ : Spec (.of k) ⟶ Spec (CommRingCat.of Λ))
          (x₀ : 𝒳.val.obj)
          (hx₀ : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ = Over.mk i₀),
          LocallyOfFiniteType i₀ → QuasiCompact i₀ →
          ∀ (s : Spec (CommRingCat.of Λ)), i₀ (IsLocalRing.closedPoint k) = s →
          ∀ (Λ' : Type u) [CommRing Λ'] [Algebra Λ' k]
            (_hΛstalk : Λ' = (Spec (CommRingCat.of Λ)).presheaf.stalk s)
            (iΛ : Spec (.of Λ') ⟶ Spec (CommRingCat.of Λ))
            (_hiΛ : HEq iΛ ((Spec (CommRingCat.of Λ)).fromSpecStalk s))
            (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ = i₀),
            let hx : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ =
              Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ) :=
              hx₀.trans (congrArg Over.mk hbase.symm)
            let D := Deformation.Artin.predeformationCategory iΛ
              (𝒳.val.p ⋙ Over.post B.inclusion) x₀ hx
            letI : Category D.carrier := D.category
            ∀ hD : Deformation.IsDeformationCategory D.projection,
              let 𝓕 := BasedCategory.ofFunctor D.projection
              let hS2 :=
                schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
                  𝓕 hD
              letI : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
              letI : Fact (Deformation.SchlessingerConditionS2
                (CategoryOfElements.π
                  (Deformation.isomorphismClasses 𝓕 hD.predeformation.cofibered))) := ⟨hS2⟩
              let F := Deformation.isomorphismClasses 𝓕 hD.predeformation.cofibered
              let T := Deformation.artinianTangentSpace Λ' k F
              letI : AddCommGroup T := Deformation.associatedTangentSpaceAddCommGroupUnlifted 𝓕
              letI : Module k T := Deformation.associatedTangentSpaceModuleUnlifted 𝓕
              FiniteDimensional k T) →
      (∀ ξ : Deformation.Artin.FormalObject B _ hΛ 𝒳.val.p,
        Deformation.Artin.FormalObject.IsEffective B _ hΛ 𝒳.val.p 𝒳.property ξ) →
      (∀ U : Over (Spec (CommRingCat.of Λ)), LocallyOfFiniteType U.hom →
        ∀ (y : 𝒳.val.obj) (hy : (𝒳.val.p ⋙ Over.post B.inclusion).obj y = U) (u : U.left),
          _root_.AlgebraicGeometry.IsFiniteTypePoint u →
          Deformation.Artin.IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u y hy →
          ∃ V : U.left.Opens, u ∈ V.1 ∧
            ∀ u' : U.left, u' ∈ V.1 → _root_.AlgebraicGeometry.IsFiniteTypePoint u' →
              Deformation.Artin.IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u' y hy) →
      (∀ s : Spec (CommRingCat.of Λ), _root_.AlgebraicGeometry.IsFiniteTypePoint s →
        IsGRing ((Spec (CommRingCat.of Λ)).presheaf.stalk s)) →
      Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B _ hΛ 𝒳.val)
    (h0CXU : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D : ComplexesSituation B _ hΛ)
      (U : Over (Spec (CommRingCat.of Λ))), LocallyOfFiniteType U.hom →
      ∀ (y : ComplexesObject D) (hy : (complexesFunctor D ⋙ Over.post B.inclusion).obj y = U)
        (u : U.left), _root_.AlgebraicGeometry.IsFiniteTypePoint u →
        Deformation.Artin.IsVersalAt U (complexesFunctor D ⋙ Over.post B.inclusion) u y hy →
        ∃ V : U.left.Opens, u ∈ V.1 ∧
          ∀ u' : U.left, u' ∈ V.1 → _root_.AlgebraicGeometry.IsFiniteTypePoint u' →
            Deformation.Artin.IsVersalAt U (complexesFunctor D ⋙ Over.post B.inclusion) u' y
              hy)
    (h07W3 : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ)))
      {Z Z' Y Y' : BigFppfOver B _ hΛ} (i : Z ⟶ Z') (f : Z ⟶ Y) (a : Z' ⟶ Y') (b : Y ⟶ Y'),
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B _ hΛ).map i) →
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B _ hΛ).map f) →
      IsPushout ((BigFppfOver.toScheme B _ hΛ).map i) ((BigFppfOver.toScheme B _ hΛ).map f)
        ((BigFppfOver.toScheme B _ hΛ).map a) ((BigFppfOver.toScheme B _ hΛ).map b) →
      ∀ {W WY WZ' WZ : AlgebraicSpaces B _ hΛ} (π : W ⟶ schemeSpace Y')
        (πY : WY ⟶ schemeSpace Y) (πZ' : WZ' ⟶ schemeSpace Z') (πZ : WZ ⟶ schemeSpace Z)
        (n : WY ⟶ W) (m : WZ' ⟶ W) (l : WZ ⟶ WY) (k : WZ ⟶ WZ'),
        IsFlat B _ hΛ π.hom →
        IsPullback n πY π (schemeSpaceMap b) → IsPullback m πZ' π (schemeSpaceMap a) →
        IsPullback l πZ πY (schemeSpaceMap f) → k ≫ πZ' = πZ ≫ schemeSpaceMap i →
        l ≫ n = k ≫ m → IsPushout k l m n)
    (h0DL7 : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ)))
      {P P' Q Q' : AlgebraicSpaces B _ hΛ} (k : P ⟶ P') (l : P ⟶ Q) (m : P' ⟶ Q')
      (n : Q ⟶ Q') (hsq : IsPushout k l m n),
      IsThickeningHom B _ hΛ k → IsAffineHom B _ hΛ l.hom →
      ∀ (M : derivedModules B _ hΛ Q) (K' : derivedModules B _ hΛ P'),
        IsPseudoCoherentObject M → IsPseudoCoherentObject K' →
        ∀ α : ((smallEtaleDerivedPullbackData B _ hΛ).pull l).obj M ≅
            ((smallEtaleDerivedPullbackData B _ hΛ).pull k).obj K',
          ∃ (N : derivedModules B _ hΛ Q')
            (eQ : ((smallEtaleDerivedPullbackData B _ hΛ).pull n).obj N ≅ M)
            (eP' : ((smallEtaleDerivedPullbackData B _ hΛ).pull m).obj N ≅ K'),
            ((smallEtaleDerivedPullbackData B _ hΛ).pull l).map eQ.hom ≫ α.hom =
              ((smallEtaleDerivedPullbackData B _ hΛ).compIso l n).inv.app N ≫
                eqToHom (congrArg
                  (fun g => ((smallEtaleDerivedPullbackData B _ hΛ).pull g).obj N)
                  hsq.w.symm) ≫
                ((smallEtaleDerivedPullbackData B _ hΛ).compIso k m).hom.app N ≫
                ((smallEtaleDerivedPullbackData B _ hΛ).pull k).map eP'.hom)
    (h0DL4 : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D : ComplexesSituation B _ hΛ)
      {T T' : SchemesOver D.Y} (h : T ⟶ T'),
      Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B _ hΛ).map h.left) →
      ∀ (E' : derivedModules B _ hΛ (D.space T')) (E : derivedModules B _ hΛ (D.space T)),
        (((smallEtaleDerivedPullbackData B _ hΛ).pull (D.relativeMap h)).obj E' ≅ E) →
        D.IsRelativelyPerfect T E → D.IsRelativelyPerfect T' E')
    {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS (complexesBasedCategory D) :=
  isAlgebraicStack_complexes_of_held_of_fibreLiftClassPullback
    (fun A _ hA X hX => moduleFinite_hom_shift_of_isProper_ofRingHom B A hA X hX)
    hpull hnat h08K1 hcomp h0DLC2 h0DKY h0DLC3 h0DKW h0DIQ h0DLA h07Y4 h0CXU h07W3 h0DL7 h0DL4 hS D

/-- **Stacks 0DLN, granted results not yet proved here other than Stacks 0D0T, 08K0 and 08K1,
with the fibre hypotheses of Stacks 0DLL discharged** (unregistered).
`ComplexesSituation.isAlgebraicStack_complexes_of_held_of_fibreLiftClassPullback_finiteExt`
with its hypothesis `h08K1` (at the systems of finitely generated subrings) also discharged, by
`AlgebraicGeometry.Space.exists_isProper_overPullback_map_of_chartLimitsInSite_properInSite` (the
base's Stacks 08K1 under the convention). The other hypotheses are those of
`isAlgebraicStack_complexes_of_held_of_fibreLiftClassPullback`, with the same marks; `hnat` is put
before `hpull`, so that the statement text differs from that of
`isAlgebraicStack_complexes_of_held_of_fibreLiftClassPullback_finiteExt` at its start. -/
theorem isAlgebraicStack_complexes_of_held_of_fibreLiftClassPullback_finiteExt_properInSite
    (hnat : ∀ {S : Scheme.{u}} {hS : B.Contains S} (D : ComplexesSituation B S hS)
      {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
      (x₀ : ComplexesObject D)
      (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (hk : B.Contains (Spec (.of k)))
      [hDer : ∀ V : FGModuleCat.{u} k, HasDerivedCategory.{u + 1} (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]
      (hK : DerivedCategory.TStructure.t.minus x₀.E),
      FibreTrivialAutNatural (hDer' := hDer) (complexesFunctor_isFiberedInGroupoids D) hK)
    (hpull : ∀ {S : Scheme.{u}} {hS : B.Contains S} (D : ComplexesSituation B S hS)
      {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
      (x₀ : ComplexesObject D)
      (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (hk : B.Contains (Spec (.of k)))
      [hDer : ∀ V : FGModuleCat.{u} k, HasDerivedCategory.{u + 1} (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]
      (hK : DerivedCategory.TStructure.t.minus x₀.E)
      (m : ℤ) (hKm : DerivedCategory.TStructure.t.minus (x₀.E⟦m⟧)),
      FibreLiftClassPullback (hDer := hDer) hK m hKm)
    (hcomp : ChangeOfBaseComparison.{u, z} B)
    (h0DLC2 : ∀ {S : Scheme.{u}} (hS : B.Contains S), NegativeExtVanishesOfFibres B S hS)
    (h0DKY : ∀ {S : Scheme.{u}} (hS : B.Contains S), RelativeDerivedHomDualExists B S hS)
    (h0DLC3 : ∀ {S : Scheme.{u}} (hS : B.Contains S),
      RelativeDerivedHomRepresentableOfFibres B S hS)
    (h0DKW : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      D.RelativelyPerfectColimit)
    (h0DIQ : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D : ComplexesSituation B _ hΛ)
      {level : ℕ → SchemesOver D.Y} {transition : ∀ n, level n ⟶ level (n + 1)}
      (L : D.SpecLimitTower level transition)
      (K : ∀ n, derivedModules B _ hΛ (D.space (level n))),
      (∀ n, (smallEtaleRingedSite B _ hΛ (D.space (level n)).1
        (D.space (level n)).2).IsPseudoCoherent (K n)) →
      ∀ (φ : ∀ n, ((smallEtaleDerivedPullbackData B _ hΛ).pull
        (D.relativeMap (transition n))).obj (K (n + 1)) ⟶ K n), (∀ n, IsIso (φ n)) →
      ∃ (E : derivedModules B _ hΛ (D.space L.T)),
        (smallEtaleRingedSite B _ hΛ (D.space L.T).1 (D.space L.T).2).IsPseudoCoherent E ∧
        ∃ ψ : ∀ n, ((smallEtaleDerivedPullbackData B _ hΛ).pull
          (D.relativeMap (L.toLimit n))).obj E ⟶ K n, (∀ n, IsIso (ψ n)) ∧
          ∀ n, Functor.fibreComp (D.compComparison (transition n) (L.toLimit (n + 1))) (φ n)
              (ψ (n + 1)) =
            (D.relativeMapComparison (L.transition_toLimit n)).hom.app E ≫ ψ n)
    (h0DLA : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      D.CechDescent)
    (h07Y4 : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ)))
      (𝒳 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1}
        (BigFppfOver B (Spec (CommRingCat.of Λ)) hΛ)),
      Stack.HasRepresentableDiagonal B _ hΛ 𝒳 →
      (∃ T : BigFppfOver B _ hΛ,
        ∀ (U : BigFppfOver B _ hΛ) (k : Type u) [Field k],
          U.left.1 = Spec (.of k) → Deformation.Artin.IsFiniteTypeOver B _ hΛ U →
          Cardinal.lift.{u, u + 1}
              (Cardinal.mk (Quotient (isIsomorphicSetoid (𝒳.val.p.Fiber U)))) ≤
            Cardinal.lift.{u + 1, u} T.left.1.size) →
      𝒳.val.p.IsStackInGroupoids.{u + 1} ((etaleTopology B).over (B.obj hΛ)) →
      Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B _ hΛ 𝒳 →
      Deformation.Artin.SatisfiesRS B _ hΛ 𝒳.val.p 𝒳.property →
      (∀ (k : Type u) [Field k] (i₀ : Spec (.of k) ⟶ Spec (CommRingCat.of Λ))
          (x₀ : 𝒳.val.obj)
          (hx₀ : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ = Over.mk i₀),
          LocallyOfFiniteType i₀ → QuasiCompact i₀ →
          ∀ (s : Spec (CommRingCat.of Λ)), i₀ (IsLocalRing.closedPoint k) = s →
          ∀ (Λ' : Type u) [CommRing Λ'] [Algebra Λ' k]
            (_hΛstalk : Λ' = (Spec (CommRingCat.of Λ)).presheaf.stalk s)
            (iΛ : Spec (.of Λ') ⟶ Spec (CommRingCat.of Λ))
            (_hiΛ : HEq iΛ ((Spec (CommRingCat.of Λ)).fromSpecStalk s))
            (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ = i₀),
            let hx : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ =
              Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ) :=
              hx₀.trans (congrArg Over.mk hbase.symm)
            let D := Deformation.Artin.predeformationCategory iΛ
              (𝒳.val.p ⋙ Over.post B.inclusion) x₀ hx
            letI : Category D.carrier := D.category
            ∀ hD : Deformation.IsDeformationCategory D.projection,
              let 𝓕 := BasedCategory.ofFunctor D.projection
              let hS2 :=
                schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
                  𝓕 hD
              letI : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
              letI : Fact (Deformation.SchlessingerConditionS2
                (CategoryOfElements.π
                  (Deformation.isomorphismClasses 𝓕 hD.predeformation.cofibered))) := ⟨hS2⟩
              let F := Deformation.isomorphismClasses 𝓕 hD.predeformation.cofibered
              let T := Deformation.artinianTangentSpace Λ' k F
              letI : AddCommGroup T := Deformation.associatedTangentSpaceAddCommGroupUnlifted 𝓕
              letI : Module k T := Deformation.associatedTangentSpaceModuleUnlifted 𝓕
              FiniteDimensional k T) →
      (∀ ξ : Deformation.Artin.FormalObject B _ hΛ 𝒳.val.p,
        Deformation.Artin.FormalObject.IsEffective B _ hΛ 𝒳.val.p 𝒳.property ξ) →
      (∀ U : Over (Spec (CommRingCat.of Λ)), LocallyOfFiniteType U.hom →
        ∀ (y : 𝒳.val.obj) (hy : (𝒳.val.p ⋙ Over.post B.inclusion).obj y = U) (u : U.left),
          _root_.AlgebraicGeometry.IsFiniteTypePoint u →
          Deformation.Artin.IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u y hy →
          ∃ V : U.left.Opens, u ∈ V.1 ∧
            ∀ u' : U.left, u' ∈ V.1 → _root_.AlgebraicGeometry.IsFiniteTypePoint u' →
              Deformation.Artin.IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u' y hy) →
      (∀ s : Spec (CommRingCat.of Λ), _root_.AlgebraicGeometry.IsFiniteTypePoint s →
        IsGRing ((Spec (CommRingCat.of Λ)).presheaf.stalk s)) →
      Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B _ hΛ 𝒳.val)
    (h0CXU : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D : ComplexesSituation B _ hΛ)
      (U : Over (Spec (CommRingCat.of Λ))), LocallyOfFiniteType U.hom →
      ∀ (y : ComplexesObject D) (hy : (complexesFunctor D ⋙ Over.post B.inclusion).obj y = U)
        (u : U.left), _root_.AlgebraicGeometry.IsFiniteTypePoint u →
        Deformation.Artin.IsVersalAt U (complexesFunctor D ⋙ Over.post B.inclusion) u y hy →
        ∃ V : U.left.Opens, u ∈ V.1 ∧
          ∀ u' : U.left, u' ∈ V.1 → _root_.AlgebraicGeometry.IsFiniteTypePoint u' →
            Deformation.Artin.IsVersalAt U (complexesFunctor D ⋙ Over.post B.inclusion) u' y
              hy)
    (h07W3 : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ)))
      {Z Z' Y Y' : BigFppfOver B _ hΛ} (i : Z ⟶ Z') (f : Z ⟶ Y) (a : Z' ⟶ Y') (b : Y ⟶ Y'),
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B _ hΛ).map i) →
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B _ hΛ).map f) →
      IsPushout ((BigFppfOver.toScheme B _ hΛ).map i) ((BigFppfOver.toScheme B _ hΛ).map f)
        ((BigFppfOver.toScheme B _ hΛ).map a) ((BigFppfOver.toScheme B _ hΛ).map b) →
      ∀ {W WY WZ' WZ : AlgebraicSpaces B _ hΛ} (π : W ⟶ schemeSpace Y')
        (πY : WY ⟶ schemeSpace Y) (πZ' : WZ' ⟶ schemeSpace Z') (πZ : WZ ⟶ schemeSpace Z)
        (n : WY ⟶ W) (m : WZ' ⟶ W) (l : WZ ⟶ WY) (k : WZ ⟶ WZ'),
        IsFlat B _ hΛ π.hom →
        IsPullback n πY π (schemeSpaceMap b) → IsPullback m πZ' π (schemeSpaceMap a) →
        IsPullback l πZ πY (schemeSpaceMap f) → k ≫ πZ' = πZ ≫ schemeSpaceMap i →
        l ≫ n = k ≫ m → IsPushout k l m n)
    (h0DL7 : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ)))
      {P P' Q Q' : AlgebraicSpaces B _ hΛ} (k : P ⟶ P') (l : P ⟶ Q) (m : P' ⟶ Q')
      (n : Q ⟶ Q') (hsq : IsPushout k l m n),
      IsThickeningHom B _ hΛ k → IsAffineHom B _ hΛ l.hom →
      ∀ (M : derivedModules B _ hΛ Q) (K' : derivedModules B _ hΛ P'),
        IsPseudoCoherentObject M → IsPseudoCoherentObject K' →
        ∀ α : ((smallEtaleDerivedPullbackData B _ hΛ).pull l).obj M ≅
            ((smallEtaleDerivedPullbackData B _ hΛ).pull k).obj K',
          ∃ (N : derivedModules B _ hΛ Q')
            (eQ : ((smallEtaleDerivedPullbackData B _ hΛ).pull n).obj N ≅ M)
            (eP' : ((smallEtaleDerivedPullbackData B _ hΛ).pull m).obj N ≅ K'),
            ((smallEtaleDerivedPullbackData B _ hΛ).pull l).map eQ.hom ≫ α.hom =
              ((smallEtaleDerivedPullbackData B _ hΛ).compIso l n).inv.app N ≫
                eqToHom (congrArg
                  (fun g => ((smallEtaleDerivedPullbackData B _ hΛ).pull g).obj N)
                  hsq.w.symm) ≫
                ((smallEtaleDerivedPullbackData B _ hΛ).compIso k m).hom.app N ≫
                ((smallEtaleDerivedPullbackData B _ hΛ).pull k).map eP'.hom)
    (h0DL4 : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
      (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D : ComplexesSituation B _ hΛ)
      {T T' : SchemesOver D.Y} (h : T ⟶ T'),
      Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B _ hΛ).map h.left) →
      ∀ (E' : derivedModules B _ hΛ (D.space T')) (E : derivedModules B _ hΛ (D.space T)),
        (((smallEtaleDerivedPullbackData B _ hΛ).pull (D.relativeMap h)).obj E' ≅ E) →
        D.IsRelativelyPerfect T E → D.IsRelativelyPerfect T' E')
    {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS (complexesBasedCategory D) :=
  isAlgebraicStack_complexes_of_held_of_fibreLiftClassPullback_finiteExt hpull hnat
    (fun A _ hA hZ i _ _ f =>
      exists_isProper_overPullback_map_of_chartLimitsInSite_properInSite B _ hZ hZ _
      (adjoinSiteDiagram_chartLimitsInSite B hZ A hA)
      (adjoinSiteDiagram_isAlgebraicSpace_isAffineHom_qcqs B hZ A hA).1
      (adjoinSiteDiagram_isAlgebraicSpace_isAffineHom_qcqs B hZ A hA).2.1 i f)
    hcomp h0DLC2 h0DKY h0DLC3 h0DKW h0DIQ h0DLA h07Y4 h0CXU h07W3 h0DL7 h0DL4 hS D

end AlgebraicGeometry.Space.ComplexesSituation

end
