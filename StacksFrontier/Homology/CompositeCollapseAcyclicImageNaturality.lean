module

public import StacksFrontier.Homology.CompositeCollapseResolution

/-!
# Naturality of the collapse isomorphism built from acyclic images

`Stacks.RightDerivedComp.objIsoOfAcyclicImage` identifies `Rⁿ(G ⋙ T)(A)` with `Rⁿ T(G A)` at a
`G`-acyclic object `A`, when `G` carries injective objects to `T`-acyclic ones.  Unlike
`Stacks.RightDerivedComp.objIso`, which asks `G` to preserve injective objects, it carried no
naturality statement in `A`.  This file supplies one.

## Main results

* `Stacks.RightDerivedComp.isoRightDerivedObjOfAcyclic_hom_comp_homologyFunctor_map`: the
  computation of `Rⁿ T` on an acyclic resolution is natural along a morphism of resolutions.
* `Stacks.RightDerivedComp.objIsoOfAcyclicImage_naturality_rightDerived`: the collapse isomorphism
  is natural in the `G`-acyclic object.

## Implementation notes

Two comparisons of an acyclic resolution `K` of `X` with an injective resolution of `Y` which
lift the same morphism `X ⟶ Y` are homotopic
(`CategoryTheory.InjectiveResolution.nonempty_descHomotopy_of_quasiIso`), so they induce the
same map on the cohomology of `T` of them; this is all that naturality needs.
-/


@[expose] public section

open CategoryTheory Limits

namespace Stacks.RightDerivedComp

section AcyclicResolutionNaturality

variable {D E : Type*} [Category* D] [Category* E] [Abelian D] [Abelian E]
  [EnoughInjectives D] (T : D ⥤ E) [T.Additive] [PreservesFiniteLimits T]

/-- **The computation of `Rⁿ T` on an acyclic resolution is natural.**  Let `ε : X[0] ⟶ K` and
`ε' : Y[0] ⟶ K'` be resolutions by `T`-acyclic objects and `φ : K ⟶ K'` a morphism of complexes
lifting `g : X ⟶ Y`.  Then `Rⁿ T(g)` corresponds to the cohomology of `T(φ)` under
`Stacks.RightDerivedComp.isoRightDerivedObjOfAcyclic`. -/
theorem isoRightDerivedObjOfAcyclic_hom_comp_homologyFunctor_map {X Y : D}
    {K K' : CochainComplex D ℕ}
    (ε : (CochainComplex.single₀ D).obj X ⟶ K) [QuasiIso ε]
    (ε' : (CochainComplex.single₀ D).obj Y ⟶ K') [QuasiIso ε']
    (hK : ∀ q, acyclic T (K.X q)) (hK' : ∀ q, acyclic T (K'.X q)) (g : X ⟶ Y)
    (φ : K ⟶ K') (hφ : ε ≫ φ = (CochainComplex.single₀ D).map g ≫ ε') (n : ℕ) :
    (isoRightDerivedObjOfAcyclic T ε hK n).hom ≫
        (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
          ((T.mapHomologicalComplex _).map φ) =
      (T.rightDerived n).map g ≫ (isoRightDerivedObjOfAcyclic T ε' hK' n).hom := by
  let J := injectiveResolution X
  let J' := injectiveResolution Y
  let δ := descOfResolution ε J
  let δ' := descOfResolution ε' J'
  have hδ : ε ≫ δ = J.ι := comp_descOfResolution ε J
  have hδ' : ε' ≫ δ' = J'.ι := comp_descOfResolution ε' J'
  let P : ObjectProperty D := acyclic T
  have hX : (isoRightDerivedObjOfAcyclic T ε hK n).hom ≫
      (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
        ((T.mapHomologicalComplex _).map δ) = (J.isoRightDerivedObj T n).hom :=
    isoRightDerivedObjOfQuasiIso_hom_comp P (exists_mono_acyclic T)
      (fun S hS h₁ h₂ => acyclic_shortExact T S hS h₁ h₂) J ε δ hδ hK
      (fun q => have := J.injective q; acyclic_of_injective T _) n
  have hY : (isoRightDerivedObjOfAcyclic T ε' hK' n).hom ≫
      (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
        ((T.mapHomologicalComplex _).map δ') = (J'.isoRightDerivedObj T n).hom :=
    isoRightDerivedObjOfQuasiIso_hom_comp P (exists_mono_acyclic T)
      (fun S hS h₁ h₂ => acyclic_shortExact T S hS h₁ h₂) J' ε' δ' hδ' hK'
      (fun q => have := J'.injective q; acyclic_of_injective T _) n
  have hiso : IsIso ((HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
      ((T.mapHomologicalComplex _).map δ')) :=
    have : IsIso ((isoRightDerivedObjOfAcyclic T ε' hK' n).hom ≫
        (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
          ((T.mapHomologicalComplex _).map δ')) := by rw [hY]; infer_instance
    IsIso.of_isIso_comp_left (isoRightDerivedObjOfAcyclic T ε' hK' n).hom _
  -- the lift of `g` between the chosen injective resolutions
  let ψ := InjectiveResolution.desc g J' J
  have hψ : J.ι.f 0 ≫ ψ.f 0 = g ≫ J'.ι.f 0 := InjectiveResolution.desc_commutes_zero g J' J
  have hnat := InjectiveResolution.isoRightDerivedObj_hom_naturality g J J' ψ hψ T n
  -- the two comparisons `K ⟶ J'` lifting `g` are homotopic
  have hw : ε ≫ (φ ≫ δ') = ε ≫ (δ ≫ ψ) := by
    rw [← Category.assoc, hφ, Category.assoc, hδ', ← Category.assoc, hδ,
      InjectiveResolution.desc_commutes]
  obtain ⟨h⟩ := InjectiveResolution.nonempty_descHomotopy_of_quasiIso J' ε hw
  have hh := (T.mapHomotopy h).homologyMap_eq n
  rw [← cancel_mono ((HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
    ((T.mapHomologicalComplex _).map δ')), Category.assoc, Category.assoc, hY, hnat,
    ← Functor.map_comp, ← Functor.map_comp]
  show _ ≫ HomologicalComplex.homologyMap ((T.mapHomologicalComplex _).map (φ ≫ δ')) n = _
  rw [hh, Functor.map_comp, HomologicalComplex.homologyMap_comp, ← hX, Category.assoc]
  rfl

end AcyclicResolutionNaturality

section CollapseNaturality

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E] [HasInjectiveResolutions C] [EnoughInjectives D]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] (T : D ⥤ E) [T.Additive]
  [PreservesFiniteLimits T]

omit [HasInjectiveResolutions C] [EnoughInjectives D] [PreservesFiniteLimits G] in
/-- `mapι` is natural along a morphism of injective resolutions. -/
lemma mapι_comp_map {A B : C} (IA : InjectiveResolution A) (IB : InjectiveResolution B)
    (g : A ⟶ B) (φ : IA.cocomplex ⟶ IB.cocomplex) (comm : IA.ι.f 0 ≫ φ.f 0 = g ≫ IB.ι.f 0) :
    mapι G IA ≫ (G.mapHomologicalComplex _).map φ =
      (CochainComplex.single₀ D).map (G.map g) ≫ mapι G IB := by
  apply HomologicalComplex.from_single_hom_ext
  have h : G.map (IA.ι.f 0) ≫ G.map (φ.f 0) = G.map g ≫ G.map (IB.ι.f 0) :=
    (G.map_comp _ _).symm.trans ((congrArg G.map comm).trans (G.map_comp _ _))
  simpa using h

/-- **The collapse isomorphism `Rⁿ(G ⋙ T)(A) ≅ Rⁿ T(G A)` of
`Stacks.RightDerivedComp.objIsoOfAcyclicImage` is natural in the `G`-acyclic object `A`.** -/
theorem objIsoOfAcyclicImage_naturality_rightDerived {A B : C}
    (hA : ∀ n, 0 < n → IsZero ((G.rightDerived n).obj A))
    (hB : ∀ n, 0 < n → IsZero ((G.rightDerived n).obj B))
    (hGT : ∀ Z : C, Injective Z → acyclic T (G.obj Z)) (g : A ⟶ B) (n : ℕ) :
    ((G ⋙ T).rightDerived n).map g ≫ (objIsoOfAcyclicImage G T hB hGT n).hom =
      (objIsoOfAcyclicImage G T hA hGT n).hom ≫ (T.rightDerived n).map (G.map g) := by
  have _ : QuasiIso (mapι G (injectiveResolution A)) :=
    quasiIso_mapι G (injectiveResolution A) hA
  have _ : QuasiIso (mapι G (injectiveResolution B)) :=
    quasiIso_mapι G (injectiveResolution B) hB
  let IA := injectiveResolution A
  let IB := injectiveResolution B
  let φ := InjectiveResolution.desc g IB IA
  have comm : IA.ι.f 0 ≫ φ.f 0 = g ≫ IB.ι.f 0 := InjectiveResolution.desc_commutes_zero g IB IA
  have nat1 := InjectiveResolution.isoRightDerivedObj_hom_naturality g IA IB φ comm (G ⋙ T) n
  have nat2 := isoRightDerivedObjOfAcyclic_hom_comp_homologyFunctor_map T (mapι G IA) (mapι G IB)
    (fun q => hGT _ (IA.injective q)) (fun q => hGT _ (IB.injective q)) (G.map g)
    ((G.mapHomologicalComplex _).map φ) (mapι_comp_map G IA IB g φ comm) n
  show ((G ⋙ T).rightDerived n).map g ≫ ((IB.isoRightDerivedObj (G ⋙ T) n).hom ≫
      (isoRightDerivedObjOfAcyclic T (mapι G IB) (fun q => hGT _ (IB.injective q)) n).inv) =
    ((IA.isoRightDerivedObj (G ⋙ T) n).hom ≫
      (isoRightDerivedObjOfAcyclic T (mapι G IA) (fun q => hGT _ (IA.injective q)) n).inv) ≫
        (T.rightDerived n).map (G.map g)
  rw [← Category.assoc, nat1, Category.assoc, Category.assoc]
  congr 1
  rw [Iso.eq_inv_comp, ← Category.assoc]
  refine (Iso.comp_inv_eq _).2 ?_
  exact nat2

end CollapseNaturality

end Stacks.RightDerivedComp
