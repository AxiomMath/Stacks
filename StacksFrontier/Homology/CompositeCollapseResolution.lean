module

public import StacksFrontier.Homology.CompositeCollapse
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedPostcomposeIndexing
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.Homology.DerivedIndexing.Composite

/-!
# The collapse isomorphism on a resolution

`Stacks.RightDerivedComp.objIsoOfAcyclicImage` identifies `Rⁿ(G ⋙ T)(A)` with `Rⁿ T(G A)` for a
`G`-acyclic object `A`, when `G` carries injective objects to `T`-acyclic ones.  This file
computes the composite of a map `Rⁿ T(η) : Rⁿ T(Z) ⟶ Rⁿ T(G A)` with the inverse of that collapse
on injective resolutions: if `γ : I ⟶ G(J)` is a map of complexes from an injective resolution of
`Z` to `G` applied to the chosen injective resolution `J` of `A`, lifting `η` in degree zero, then
the composite is the degree-`n` cohomology of `T(γ)`, read through the identifications of the two
derived functors with cohomology on `I` and on `J`.

## Main results

* `Stacks.RightDerivedComp.isoRightDerivedObj_inv_comp_map_comp_objIsoOfAcyclicImage_inv`: the
  computation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.RightDerivedComp

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E] [HasInjectiveResolutions C] [EnoughInjectives D]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] (T : D ⥤ E) [T.Additive]
  [PreservesFiniteLimits T]

omit [HasInjectiveResolutions C] [G.Additive] [PreservesFiniteLimits G] in
/-- `CategoryTheory.InjectiveResolution.isoRightDerivedObjOfQuasiIso` followed by the cohomology
of `F(β)` is the identification on the injective resolution. -/
theorem isoRightDerivedObjOfQuasiIso_hom_comp {F : D ⥤ E} [F.Additive] (P : ObjectProperty D)
    (hI₁ : ∀ Y : D, ∃ (Z : D) (_ : P Z) (i : Y ⟶ Z), Mono i)
    (hI₂ : ∀ S : ShortComplex D, S.ShortExact → P S.X₁ → P S.X₂ →
      P S.X₃ ∧ (S.map F).ShortExact)
    {X : D} (J : InjectiveResolution X) {K : CochainComplex D ℕ}
    (ε : (CochainComplex.single₀ D).obj X ⟶ K) [QuasiIso ε] (β : K ⟶ J.cocomplex)
    (hβ : ε ≫ β = J.ι) (hIK : ∀ n, P (K.X n)) (hIJ : ∀ n, P (J.cocomplex.X n)) (n : ℕ) :
    (InjectiveResolution.isoRightDerivedObjOfQuasiIso F P hI₁ hI₂ J ε β hβ hIK hIJ n).hom ≫
        (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
          ((F.mapHomologicalComplex _).map β) =
      (J.isoRightDerivedObj F n).hom := by
  have hi := InjectiveResolution.isIso_homologyMap_map_of_desc F P hI₁ hI₂ J ε β hβ hIK hIJ n
  exact (Category.assoc _ _ _).trans <|
    (congrArg _ (@IsIso.inv_hom_id _ _ _ _ _ hi)).trans (Category.comp_id _)

/-- **The inverse of the collapse isomorphism after `Rⁿ T(η)`, on resolutions.**  Let `A` be
`G`-acyclic, let `G` carry injective objects to `T`-acyclic ones, let `η : Z ⟶ G A`, let `I` be
an injective resolution of `Z` and let `γ : I ⟶ G(J)` be a map of complexes into `G` applied to
the chosen injective resolution `J` of `A` which lifts `η` in degree zero.  Then `Rⁿ T(η)`
followed by the inverse of `Stacks.RightDerivedComp.objIsoOfAcyclicImage` is, on `I` and on `J`,
the degree-`n` cohomology of `T(γ)`.

The collapse is computed on the chosen resolution of `G A`, through a comparison `δ` of `G(J)`
with it; `γ ≫ δ` lifts `η` to that resolution, so `Rⁿ T(η)` is the cohomology of `T(γ ≫ δ)`, and
the factor `T(δ)` cancels against the inverse of its cohomology in the collapse. -/
theorem isoRightDerivedObj_inv_comp_map_comp_objIsoOfAcyclicImage_inv {A : C}
    (hA : ∀ n, 0 < n → IsZero ((G.rightDerived n).obj A))
    (hGT : ∀ Z : C, Injective Z → acyclic T (G.obj Z))
    {Z : D} (I : InjectiveResolution Z) (η : Z ⟶ G.obj A)
    (γ : I.cocomplex ⟶ (G.mapHomologicalComplex _).obj (injectiveResolution A).cocomplex)
    (hγ : I.ι.f 0 ≫ γ.f 0 = η ≫ G.map ((injectiveResolution A).ι.f 0)) (n : ℕ) :
    (I.isoRightDerivedObj T n).inv ≫ (T.rightDerived n).map η ≫
        (objIsoOfAcyclicImage G T hA hGT n).inv =
      (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
          ((T.mapHomologicalComplex _).map γ) ≫
        ((injectiveResolution A).isoRightDerivedObj (G ⋙ T) n).inv := by
  have : QuasiIso (mapι G (injectiveResolution A)) := quasiIso_mapι G (injectiveResolution A) hA
  let K := injectiveResolution (G.obj A)
  let δ := descOfResolution (mapι G (injectiveResolution A)) K
  have hδ : mapι G (injectiveResolution A) ≫ δ = K.ι :=
    comp_descOfResolution (mapι G (injectiveResolution A)) K
  have hδ₀ : G.map ((injectiveResolution A).ι.f 0) ≫ δ.f 0 = K.ι.f 0 := by
    simpa using HomologicalComplex.congr_hom hδ 0
  have hφ : I.ι.f 0 ≫ (γ ≫ δ).f 0 = η ≫ K.ι.f 0 := by
    rw [HomologicalComplex.comp_f, ← Category.assoc, hγ]
    exact (Category.assoc _ _ _).trans (congrArg (η ≫ ·) hδ₀)
  have hnat := InjectiveResolution.isoRightDerivedObj_hom_naturality η I K (γ ≫ δ) hφ T n
  let X := isoRightDerivedObjOfAcyclic T (mapι G (injectiveResolution A))
    (fun q => hGT _ ((injectiveResolution A).injective q)) n
  have hX : X.hom ≫ (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
      ((T.mapHomologicalComplex _).map δ) = (K.isoRightDerivedObj T n).hom :=
    isoRightDerivedObjOfQuasiIso_hom_comp (acyclic T) (exists_mono_acyclic T)
      (fun S hS h₁ h₂ => acyclic_shortExact T S hS h₁ h₂) K (mapι G (injectiveResolution A)) δ hδ
      (fun q => hGT _ ((injectiveResolution A).injective q))
      (fun q => have := K.injective q; acyclic_of_injective T _) n
  have hinv : (objIsoOfAcyclicImage G T hA hGT n).inv =
      X.hom ≫ ((injectiveResolution A).isoRightDerivedObj (G ⋙ T) n).inv := rfl
  have hiso : IsIso ((HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
      ((T.mapHomologicalComplex _).map δ)) :=
    have : IsIso (X.hom ≫ (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
        ((T.mapHomologicalComplex _).map δ)) := by
      rw [hX]
      infer_instance
    IsIso.of_isIso_comp_left X.hom _
  rw [hinv, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono ((HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
      ((T.mapHomologicalComplex _).map δ)), Category.assoc, Category.assoc, hX, hnat,
    Iso.inv_hom_id_assoc, Functor.comp_map, Functor.map_comp, Functor.map_comp]

section PostCompose

variable {C D D' : Type*} [Category* C] [Category* D] [Category* D'] [Abelian C] [Abelian D]
  [Abelian D'] [EnoughInjectives C] (F : C ⥤ D) [F.Additive] (G : D ⥤ D') [G.Additive]
  [G.PreservesHomology]

/-- **`CategoryTheory.Functor.rightDerivedCompIso` on the chosen injective resolution.**  Read
through the identifications of `Rⁿ(F ⋙ G)(X)` and of `Rⁿ F(X)` with cohomology on the chosen
injective resolution `J` of `X`, pulling the exact functor `G` out of the right derived functor is
the comparison `Hⁿ(G(F(J))) ≅ G(Hⁿ(F(J)))` of the exact `G` with cohomology. -/
theorem isoRightDerivedObj_inv_comp_rightDerivedCompIso_hom_app (n : ℕ) (X : C) :
    ((injectiveResolution X).isoRightDerivedObj (F ⋙ G) n).inv ≫
        (F.rightDerivedCompIso G n).hom.app X =
      (Stacks.DerivedIndexing.mapExactHomologyIso G
          ((F.mapHomologicalComplex _).obj (injectiveResolution X).cocomplex) n).hom ≫
        G.map ((injectiveResolution X).isoRightDerivedObj F n).inv := by
  have hq := Stacks.DerivedIndexing.mapHomotopyCategoryHomologyIso_hom_app_quotient G
    ((F.mapHomologicalComplex _).obj (injectiveResolution X).cocomplex) n
  rw [Stacks.DerivedIndexing.rightDerivedCompIso_hom_app,
    Stacks.DerivedIndexing.isoRightDerivedObj_injectiveResolution_inv,
    Stacks.DerivedIndexing.isoRightDerivedObj_injectiveResolution_inv]
  exact (congrArg (_ ≫ ·) hq).trans (Iso.inv_hom_id_app_assoc _ _ _)

end PostCompose

end Stacks.RightDerivedComp

end
