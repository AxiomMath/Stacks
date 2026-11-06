module

public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianDerivedBaseChangeCriteria
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The descended base change comparison at an object, from an injective resolution

`Stacks.Cohomology.BaseChange.derived` descends a comparison `τ : F ⋙ G ⟶ G' ⋙ F'` of
underived composites to the bounded below right derived functors.  This file gives a criterion
for its component at an object `X` placed in degree zero to be invertible which mentions only
complexes: if `I` is the chosen injective resolution of `X`, extended by zero to `ℤ`, and
`φ : G'(I) ⟶ L` is a quasi-isomorphism onto a bounded below complex of injectives, then the
component is invertible as soon as the composite of `τ` applied termwise to `I` with `F'(φ)` is
a quasi-isomorphism.

When `G'` is exact, `G'(I)` is a resolution of `G'(X)`, so `L` can be taken to be an injective
resolution of `G'(X)`; the criterion then says that the comparison is invertible at `X[0]` when
the map of complexes `G(F(I)) ⟶ F'(L)` computing it is a quasi-isomorphism.

## Main results

* `Stacks.Cohomology.BaseChange.isIso_derived_app_single_of_isIso_Qh_map`: the criterion, in the
  bounded below homotopy category.
* `Stacks.Cohomology.BaseChange.isIso_derived_app_single_of_quasiIso_cocomplex`: the criterion for
  a quasi-isomorphism of `ℕ`-indexed complexes `G'(I) ⟶ J` to an injective resolution `J` of
  `G'(X)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.BaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
  (F : A ⥤ B) (F' : C ⥤ D) (G : B ⥤ D) (G' : A ⥤ C)
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  (τ : F ⋙ G ⟶ G' ⋙ F')
  (e : G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
    DerivedCategory.Plus.Qh ⋙ G.rightDerivedFunctorPlus)

/-- If `u ≫ r = c ≫ v` with `r` and `v` invertible, then `a ≫ u` is invertible as soon as
`a ≫ c` is. -/
theorem isIso_comp_of_square {𝒞 : Type*} [Category* 𝒞] {P Q R S T : 𝒞} (a : P ⟶ Q)
    (u : Q ⟶ R) (r : R ⟶ S) (c : Q ⟶ T) (v : T ⟶ S) (h : u ≫ r = c ≫ v) [IsIso r] [IsIso v]
    (hac : IsIso (a ≫ c)) : IsIso (a ≫ u) := by
  have : IsIso ((a ≫ u) ≫ r) := by
    rw [Category.assoc, h, ← Category.assoc]
    infer_instance
  exact IsIso.of_isIso_comp_right _ r

/-- **The descended comparison at `X[0]` from a resolution.**  Let `I` be the chosen injective
resolution of `X`, extended by zero to `ℤ` (`Stacks.DerivedIndexing.resPlus`), let `L` be a
bounded below complex of injectives and let `φ : G'(I) ⟶ L` become invertible in the derived
category.  If `τ` applied termwise to `I` followed by `F'(φ)` becomes invertible in the derived
category, then the descended comparison is invertible at `X` placed in degree zero.

`X[0]` is `I` in the derived category, the units of `RF` at `I` and of the exact `G'` are
invertible, so `Stacks.Cohomology.BaseChange.isIso_derived_app_Qh_iff` reduces the claim to the
invertibility of `τ(I)` followed by the unit of `RF'` at `G'(I)`; naturality of that unit along
`φ` and its invertibility at the complex of injectives `L` turn that into the hypothesis. -/
theorem isIso_derived_app_single_of_isIso_Qh_map (X : A)
    (L : HomotopyCategory.Plus C) [∀ n : ℤ, Injective (L.obj.as.X n)]
    (φ : G'.mapHomotopyCategoryPlus.obj (Stacks.DerivedIndexing.resPlus.obj X) ⟶ L)
    [IsIso (DerivedCategory.Plus.Qh.map φ)]
    (h : IsIso (DerivedCategory.Plus.Qh.map
      ((mapPlus τ).app (Stacks.DerivedIndexing.resPlus.obj X) ≫
        F'.mapHomotopyCategoryPlus.map φ))) :
    IsIso ((derived F F' G G' τ e).app ((DerivedCategory.Plus.singleFunctor A 0).obj X)) := by
  let K := Stacks.DerivedIndexing.resPlus.obj X
  refine (NatTrans.isIso_app_iff_of_iso _
    ((Stacks.DerivedIndexing.singleIsoResPlusQh (C := A)).app X)).2 ?_
  have hF : IsIso (F.rightDerivedFunctorPlusUnith.app K) :=
    inferInstanceAs (IsIso (F.rightDerivedFunctorPlusUnith.app
      (Stacks.DerivedIndexing.resPlus.obj X)))
  have hG' : IsIso (G'.rightDerivedFunctorPlusUnith.app K) :=
    have := exactUnit_isIso G'
    inferInstance
  refine (isIso_derived_app_Qh_iff F F' G G' τ e K hF hG').2 ?_
  have hL : IsIso (F'.rightDerivedFunctorPlusUnith.app L) := inferInstance
  have hR : IsIso ((DerivedCategory.Plus.Qh ⋙ F'.rightDerivedFunctorPlus).map φ) :=
    inferInstanceAs (IsIso (F'.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map φ)))
  have h' : IsIso (DerivedCategory.Plus.Qh.map ((mapPlus τ).app K) ≫
      DerivedCategory.Plus.Qh.map (F'.mapHomotopyCategoryPlus.map φ)) :=
    cast (congrArg IsIso (Functor.map_comp DerivedCategory.Plus.Qh _ _)) h
  exact isIso_comp_of_square _ _ _ _ _ (F'.rightDerivedFunctorPlusUnith.naturality φ).symm h'

/-- The extension by zero of an injective resolution, as an object of the bounded below homotopy
category. -/
def injectiveResolutionPlus {Z : C} (J : InjectiveResolution Z) : HomotopyCategory.Plus C :=
  ⟨(HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj J.cochainComplex, by
    rw [HomotopyCategory.plus_quotient_obj_iff]
    exact ⟨0, inferInstance⟩⟩

/-- Every term of the extension by zero of an injective resolution is injective. -/
instance injective_injectiveResolutionPlus_X {Z : C} (J : InjectiveResolution Z) (n : ℤ) :
    Injective ((injectiveResolutionPlus J).obj.as.X n) :=
  inferInstanceAs (Injective (J.cochainComplex.X n))

/-- A morphism of the bounded below homotopy category represented by a quasi-isomorphism of
complexes becomes invertible in the derived category. -/
private theorem isIso_Qh_map_of_quasiIso {E : Type*} [Category* E] [Abelian E]
    {K L : HomotopyCategory.Plus E} (f : K ⟶ L) (g : K.obj.as ⟶ L.obj.as)
    (hf : f.hom = (HomotopyCategory.quotient E (ComplexShape.up ℤ)).map g) (hg : QuasiIso g) :
    IsIso (DerivedCategory.Plus.Qh.map f) :=
  Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso E) f (by
    change HomotopyCategory.quasiIso E (ComplexShape.up ℤ) f.hom
    rw [hf]
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff g).2
      ((HomologicalComplex.mem_quasiIso_iff g).2 hg))

/-- **The descended comparison at `X[0]` from a quasi-isomorphism of complexes.**  Let `I` be the
chosen injective resolution of `X` and `J` an injective resolution of `G'(X)`, both extended by
zero to `ℤ`, and let `χ : G'(I) ⟶ J` be a quasi-isomorphism.  If `τ` applied termwise to `I`
followed by `F'(χ)` is a quasi-isomorphism `G(F(I)) ⟶ F'(J)`, then the descended comparison is
invertible at `X` placed in degree zero. -/
theorem isIso_derived_app_single_of_quasiIso (X : A) {Z : C} (J : InjectiveResolution Z)
    (χ : (G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (injectiveResolution X).cochainComplex ⟶ J.cochainComplex) (hχ : QuasiIso χ)
    (h : QuasiIso ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
        (injectiveResolution X).cochainComplex ≫
      (F'.mapHomologicalComplex (ComplexShape.up ℤ)).map χ)) :
    IsIso ((derived F F' G G' τ e).app ((DerivedCategory.Plus.singleFunctor A 0).obj X)) := by
  let φ : G'.mapHomotopyCategoryPlus.obj (Stacks.DerivedIndexing.resPlus.obj X) ⟶
      injectiveResolutionPlus J :=
    ObjectProperty.homMk ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map χ)
  have hφ : IsIso (DerivedCategory.Plus.Qh.map φ) := isIso_Qh_map_of_quasiIso φ χ rfl hχ
  exact isIso_derived_app_single_of_isIso_Qh_map F F' G G' τ e X (injectiveResolutionPlus J) φ
    (isIso_Qh_map_of_quasiIso _ _ rfl h)

omit [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C] [PreservesFiniteLimits G']
  [PreservesFiniteColimits G'] in
/-- Extension by zero along `e` carries a quasi-isomorphism `ψ : G'(K) ⟶ L`, and the
quasi-isomorphism `τ(K) ≫ F'(ψ)`, to quasi-isomorphisms of the extended complexes, read through
the comparisons `Stacks.DerivedIndexing.mapExtendIso`. -/
theorem extend_quasiIso_of_quasiIso {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (E : c.Embedding c') [E.IsRelIff] (K : HomologicalComplex A c) (L : HomologicalComplex C c)
    (ψ : (G'.mapHomologicalComplex c).obj K ⟶ L) [QuasiIso ψ]
    (h : QuasiIso ((NatTrans.mapHomologicalComplex τ c).app K ≫
      (F'.mapHomologicalComplex c).map ψ)) :
    QuasiIso ((Stacks.DerivedIndexing.mapExtendIso G' E K).inv ≫
        HomologicalComplex.extendMap ψ E) ∧
      QuasiIso ((NatTrans.mapHomologicalComplex τ c').app (K.extend E) ≫
        (F'.mapHomologicalComplex c').map ((Stacks.DerivedIndexing.mapExtendIso G' E K).inv ≫
          HomologicalComplex.extendMap ψ E)) := by
  have : QuasiIso (HomologicalComplex.extendMap ψ E) :=
    (HomologicalComplex.quasiIso_extendMap_iff ψ E).2 inferInstance
  refine ⟨inferInstance, ?_⟩
  have key : (NatTrans.mapHomologicalComplex τ c').app (K.extend E) ≫
      (F'.mapHomologicalComplex c').map ((Stacks.DerivedIndexing.mapExtendIso G' E K).inv ≫
          HomologicalComplex.extendMap ψ E) =
      (Stacks.DerivedIndexing.mapExtendIso (F ⋙ G) E K).inv ≫
        HomologicalComplex.extendMap ((NatTrans.mapHomologicalComplex τ c).app K ≫
          (F'.mapHomologicalComplex c).map ψ) E ≫
        (Stacks.DerivedIndexing.mapExtendIso F' E L).hom := by
    rw [Iso.eq_inv_comp]
    ext i'
    by_cases hi : ∃ i, E.f i = i'
    · obtain ⟨i, hi⟩ := hi
      simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        NatTrans.mapHomologicalComplex_app_f, Functor.map_comp,
        Stacks.DerivedIndexing.mapExtendIso_hom_f_eq _ E _ hi,
        Stacks.DerivedIndexing.mapExtendIso_inv_f_eq _ E _ hi,
        HomologicalComplex.extendMap_f _ E hi, Category.assoc]
      have hn : (F ⋙ G).map (K.extendXIso E hi).inv ≫ τ.app ((K.extend E).X i') =
          τ.app (K.X i) ≫ (G' ⋙ F').map (K.extendXIso E hi).inv := τ.naturality _
      slice_lhs 2 3 => rw [hn]
      simp only [Functor.comp_map, Category.assoc, ← F'.map_comp_assoc, ← G'.map_comp,
        Iso.inv_hom_id, G'.map_id, F'.map_id, Category.id_comp, Iso.inv_hom_id_assoc]
    · push Not at hi
      exact (HomologicalComplex.isZero_extend_X _ E i' hi).eq_of_src _ _
  have : QuasiIso (HomologicalComplex.extendMap ((NatTrans.mapHomologicalComplex τ c).app K ≫
      (F'.mapHomologicalComplex c).map ψ) E) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ E).2 h
  rw [key]
  infer_instance

/-- **The descended comparison at `X[0]` from a quasi-isomorphism of resolutions.**  The form of
`isIso_derived_app_single_of_quasiIso` for complexes indexed by `ℕ`: let `I` be the chosen
injective resolution of `X`, let `J` be an injective resolution of `G'(X)` and let
`ψ : G'(I) ⟶ J` be a quasi-isomorphism.  If `τ` applied termwise to `I` followed by `F'(ψ)` is a
quasi-isomorphism `G(F(I)) ⟶ F'(J)`, then the descended comparison is invertible at `X` placed in
degree zero. -/
theorem isIso_derived_app_single_of_quasiIso_cocomplex (X : A) {Z : C} (J : InjectiveResolution Z)
    (ψ : (G'.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution X).cocomplex ⟶ J.cocomplex) [QuasiIso ψ]
    (h : QuasiIso ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℕ)).app
        (injectiveResolution X).cocomplex ≫
      (F'.mapHomologicalComplex (ComplexShape.up ℕ)).map ψ)) :
    IsIso ((derived F F' G G' τ e).app ((DerivedCategory.Plus.singleFunctor A 0).obj X)) := by
  have := extend_quasiIso_of_quasiIso F F' G G' τ ComplexShape.embeddingUpNat
    (injectiveResolution X).cocomplex J.cocomplex ψ h
  obtain ⟨h₁, h₂⟩ := this
  exact isIso_derived_app_single_of_quasiIso F F' G G' τ e X J
    ((Stacks.DerivedIndexing.mapExtendIso G' ComplexShape.embeddingUpNat
      (injectiveResolution X).cocomplex).inv ≫
        HomologicalComplex.extendMap ψ ComplexShape.embeddingUpNat) h₁ h₂


section Transport

variable {Fm : A ⥤ B} {F'm : C ⥤ D} [Fm.Additive] [F'm.Additive]

omit [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C] [PreservesFiniteLimits G']
  [PreservesFiniteColimits G'] in
/-- **A base change map on complexes is a quasi-isomorphism as soon as its transport is.**  Let
`α : F ≅ Fm` and `β : F' ≅ F'm` compare two readings of the two direct images, and let
`τ : F ⋙ G ⟶ G' ⋙ F'` be `τm : Fm ⋙ G ⟶ G' ⋙ F'm` read through them.  For a complex `I` and
`ψ : G'(I) ⟶ J`, if `τm(I) ≫ F'm(ψ)` is a quasi-isomorphism, then so is `τ(I) ≫ F'(ψ)`: the two
differ by the isomorphisms `G(α_I)` and `β_J⁻¹`. -/
theorem quasiIso_comp_mapHomologicalComplex_of_eq_whisker {ι : Type*} {c : ComplexShape ι}
    (α : F ≅ Fm) (β : F' ≅ F'm) (τm : Fm ⋙ G ⟶ G' ⋙ F'm)
    (hτ : τ = Functor.whiskerRight α.hom G ≫ τm ≫ Functor.whiskerLeft G' β.inv)
    (I : HomologicalComplex A c) {J : HomologicalComplex C c}
    (ψ : (G'.mapHomologicalComplex c).obj I ⟶ J)
    (h : QuasiIso ((NatTrans.mapHomologicalComplex τm c).app I ≫
      (F'm.mapHomologicalComplex c).map ψ)) :
    QuasiIso ((NatTrans.mapHomologicalComplex τ c).app I ≫
      (F'.mapHomologicalComplex c).map ψ) := by
  have key : (NatTrans.mapHomologicalComplex τ c).app I ≫ (F'.mapHomologicalComplex c).map ψ =
      ((NatIso.mapHomologicalComplex (Functor.isoWhiskerRight α G) c).app I).hom ≫
        ((NatTrans.mapHomologicalComplex τm c).app I ≫ (F'm.mapHomologicalComplex c).map ψ) ≫
        ((NatIso.mapHomologicalComplex β c).app J).inv := by
    subst hτ
    ext k
    have hn := β.inv.naturality (ψ.f k)
    simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplex_map_f, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Iso.app_hom, Iso.app_inv, NatIso.mapHomologicalComplex_hom_app_f,
      NatIso.mapHomologicalComplex_inv_app_f, Functor.isoWhiskerRight_hom, Category.assoc] at hn ⊢
    rw [hn]
    rfl
  rw [key]
  infer_instance

end Transport

end Stacks.Cohomology.BaseChange

end
