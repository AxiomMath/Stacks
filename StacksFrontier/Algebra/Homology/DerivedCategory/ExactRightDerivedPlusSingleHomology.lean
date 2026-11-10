module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactDerivedHomologyComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactMapDerivedPlusIsoApp
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactPlusSingleCompatible
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactUnitSingle
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology

/-!
# For an exact functor, the two identifications `F ≅ H⁰(RF((-)[0]))` agree

Let `F : 𝒜 ⥤ ℬ` be an exact functor between abelian categories, `𝒜` having enough injectives.
There are two isomorphisms `F(N) ≅ H⁰(RF(N[0]))` in this development, natural in `N`:

* `CategoryTheory.Functor.isoRightDerivedPlusSingle F 0`, which exists for every left exact `F`
  and is the derived-functor unit at `N[0]` read by `H⁰` ([Stacks, Tag 05TD] (3));
* the comparison `Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso F 0` of `H⁰ ∘ RF` with
  `F ∘ H⁰`, which exists because `F` is exact, at the complex `N[0]`, followed by `F` of the
  identification `H⁰(N[0]) ≅ N`.

This file proves they agree:
`isoRightDerivedPlusSingle_hom_app_comp_exactRightDerivedPlusHomologyIso`.

The proof descends to complexes: the unit and the comparison of the derived functor with the
degreewise action cancel against each other, leaving Mathlib's comparison of the degreewise action
with the degree-zero embedding against the comparison of homology of complexes with `F`, which on a
single complex is read off its cycles.

## Main results

* `Stacks.DerivedFunctor.singleObjHomologySelfIso_inv_comp_complexHomologyIso` — the statement on
  complexes.
* `Stacks.DerivedFunctor.singleFunctorCompHomologyFunctorIso_inv_comp_derivedHomologyIso` — the
  statement on the unbounded derived category.
* `Stacks.DerivedFunctor.isoRightDerivedPlusSingle_hom_app_comp_exactRightDerivedPlusHomologyIso`
  — **the statement on the bounded below derived category.**

## References

* [Stacks Project, Tag 05TD](https://stacks.math.columbia.edu/tag/05TD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w

namespace Stacks.DerivedFunctor

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The rearrangement behind `singleObjHomologySelfIso_inv_comp_complexHomologyIso`, stated on
variables. -/
private theorem single_algebra {E : Type*} [Category* E] {P Q R S T U V : E}
    {hL : P ⟶ R} {a : P ⟶ Q} {πL : Q ⟶ R} {hm : R ⟶ S} {cm : Q ⟶ T} {πK : T ⟶ S}
    {ch mh : S ⟶ U} {mc : T ⟶ V} {Fπ : V ⟶ U} {b : P ⟶ V} {Fh : P ⟶ U}
    (h₁ : hL = a ≫ πL) (hn : πL ≫ hm = cm ≫ πK) (hπ : πK ≫ mh = mc ≫ Fπ)
    (hX : a ≫ cm ≫ mc = b) (hc : ch = mh) (hF : Fh = b ≫ Fπ) :
    hL ≫ hm ≫ ch = Fh := by
  subst h₁ hc hF hX
  rw [Category.assoc, reassoc_of% hn, hπ]
  simp only [Category.assoc]

/-- **On a complex concentrated in degree zero, the comparison of homology with `F` is `F` of the
identification of the homology with the object.** -/
theorem singleObjHomologySelfIso_inv_comp_complexHomologyIso (N : A) :
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (F.obj N)).inv ≫
        HomologicalComplex.homologyMap ((F.mapCochainComplexSingleFunctor 0).inv.app N) 0 ≫
          (complexHomologyIso F (ComplexShape.up ℤ) 0).hom.app
            ((CochainComplex.singleFunctor A 0).obj N) =
      F.map (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 N).inv := by
  let K := (CochainComplex.singleFunctor A 0).obj N
  let L := (CochainComplex.singleFunctor B 0).obj (F.obj N)
  let φ : L ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
    (F.mapCochainComplexSingleFunctor 0).inv.app N
  have hi : HomologicalComplex.cyclesMap φ 0 ≫ ((K.sc 0).mapCyclesIso F).hom ≫
      F.map (K.iCycles 0) =
        HomologicalComplex.cyclesMap φ 0 ≫
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).iCycles 0 :=
    congrArg (HomologicalComplex.cyclesMap φ 0 ≫ ·)
      (ShortComplex.mapCyclesIso_hom_iCycles (K.sc 0) F)
  have hci : HomologicalComplex.cyclesMap φ 0 ≫
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).iCycles 0 =
        L.iCycles 0 ≫ φ.f 0 :=
    HomologicalComplex.cyclesMap_i φ 0
  have hsL : (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 (F.obj N)).inv ≫
      L.iCycles 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (F.obj N)).inv :=
    HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles _ _ _
  have hsK : (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 N).inv ≫
      K.iCycles 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).inv :=
    HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles _ _ _
  have hφ : φ.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (F.obj N)).hom ≫
      F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).inv :=
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self F (ComplexShape.up ℤ) 0 N
  have hX : (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 (F.obj N)).inv ≫
      HomologicalComplex.cyclesMap φ 0 ≫ ((K.sc 0).mapCyclesIso F).hom =
        F.map (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 N).inv := by
    refine (cancel_mono (F.map (K.iCycles 0))).1 ?_
    refine (Category.assoc _ _ _).trans ?_
    refine ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans hi)).trans ?_).trans
      ((F.map_comp _ _).symm.trans (congrArg F.map hsK)).symm
    refine (congrArg (_ ≫ ·) hci).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    rw [hsL, hφ, Iso.inv_hom_id_assoc]
  have hπ : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ 0 ≫
      ((K.sc 0).mapHomologyIso F).hom = ((K.sc 0).mapCyclesIso F).hom ≫ F.map (K.homologyπ 0) :=
    Stacks.Homology.mapHomologyIso_homologyπ (K.sc 0) F
  have hn : L.homologyπ 0 ≫ HomologicalComplex.homologyMap φ 0 =
      HomologicalComplex.cyclesMap φ 0 ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ 0 :=
    HomologicalComplex.homologyπ_naturality φ 0
  have hL : (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (F.obj N)).inv =
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 (F.obj N)).inv ≫
        L.homologyπ 0 :=
    (HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ _ _ _).symm
  have hK : (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 N).inv =
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 N).inv ≫ K.homologyπ 0 :=
    (HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ _ _ _).symm
  have hc : (complexHomologyIso F (ComplexShape.up ℤ) 0).hom.app K =
      ((K.sc 0).mapHomologyIso F).hom :=
    complexHomologyIso_hom_app (c := ComplexShape.up ℤ) (i := 0) F K
  exact single_algebra hL hn hπ hX hc ((congrArg F.map hK).trans (F.map_comp _ _))

/-! ### The unbounded derived category -/

section Unbounded

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

omit [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- The inverse of the identification of the cohomology of a single complex with the object, on
the derived category, is the inverse identification on complexes followed by the factorization of
cohomology through complexes. -/
theorem singleFunctorCompHomologyFunctorIso_inv_app (C : Type*) [Category* C] [Abelian C]
    [HasDerivedCategory C] (X : C) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).inv.app X =
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).inv ≫
        (DerivedCategory.homologyFunctorFactors C 0).inv.app
          ((CochainComplex.singleFunctor C 0).obj X) := by
  simp [DerivedCategory.singleFunctorCompHomologyFunctorIso,
    DerivedCategory.singleFunctorsPostcompQIso, HomologicalComplex.homologyFunctorSingleIso]
  rfl

/-- The rearrangement behind `singleFunctorCompHomologyFunctorIso_inv_comp_derivedHomologyIso`,
stated on variables. -/
private theorem unbounded_algebra {E : Type*} [Category* E] {P R H₁ H₂ H₃ S U U'' : E}
    {sB : P ⟶ H₁} {s₁ : P ⟶ R} {q₁ : R ⟶ H₁} {m₁ : H₁ ⟶ H₂} {d : H₂ ⟶ U''} {m₂ : H₂ ⟶ H₃}
    {q₂ : H₃ ⟶ S} {c : S ⟶ U} {f : U ⟶ U''} {Hφ : H₁ ⟶ H₃} {q₁' : H₁ ⟶ R} {hmφ : R ⟶ S}
    {Fs : P ⟶ U} {G : P ⟶ U''}
    (hsB : sB = s₁ ≫ q₁) (hQ : d = m₂ ≫ q₂ ≫ c ≫ f) (hm : m₁ ≫ m₂ = Hφ)
    (hn : Hφ ≫ q₂ = q₁' ≫ hmφ) (hinv : q₁ ≫ q₁' = 𝟙 R) (hC : s₁ ≫ hmφ ≫ c = Fs)
    (hG : G = Fs ≫ f) : sB ≫ m₁ ≫ d = G := by
  subst hsB hG hQ hC
  simp only [Category.assoc]
  rw [reassoc_of% hm, reassoc_of% hn, reassoc_of% hinv]

/-- **On the unbounded derived category, the comparison of cohomology with an exact functor, at
a complex concentrated in degree zero, is `F` of the identification of its cohomology with the
object.** Mathlib's comparison of the degreewise action with the degree-zero embedding is read
backwards. -/
theorem singleFunctorCompHomologyFunctorIso_inv_comp_derivedHomologyIso (N : A) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).inv.app (F.obj N) ≫
        (DerivedCategory.homologyFunctor B 0).map
            ((F.mapDerivedCategorySingleFunctor 0).inv.app N) ≫
          (derivedHomologyIso F 0).hom.app ((DerivedCategory.singleFunctor A 0).obj N) =
      F.map ((DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).inv.app N) := by
  let K := (CochainComplex.singleFunctor A 0).obj N
  let L := (CochainComplex.singleFunctor B 0).obj (F.obj N)
  let φ : L ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
    (F.mapCochainComplexSingleFunctor 0).inv.app N
  have hQ : (derivedHomologyIso F 0).hom.app ((DerivedCategory.singleFunctor A 0).obj N) =
      (DerivedCategory.homologyFunctor B 0).map (F.mapDerivedCategoryFactors.hom.app K) ≫
        (DerivedCategory.homologyFunctorFactors B 0).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (complexHomologyIso F (ComplexShape.up ℤ) 0).hom.app K ≫
        F.map ((DerivedCategory.homologyFunctorFactors A 0).inv.app K) :=
    derivedHomologyIso_hom_app_Q F 0 K
  have hm : (DerivedCategory.homologyFunctor B 0).map
        ((F.mapDerivedCategorySingleFunctor 0).inv.app N) ≫
      (DerivedCategory.homologyFunctor B 0).map (F.mapDerivedCategoryFactors.hom.app K) =
        (DerivedCategory.homologyFunctor B 0).map (DerivedCategory.Q.map φ) :=
    ((DerivedCategory.homologyFunctor B 0).map_comp _ _).symm.trans
      (congrArg (DerivedCategory.homologyFunctor B 0).map
        (F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app N))
  have hn : (DerivedCategory.homologyFunctor B 0).map (DerivedCategory.Q.map φ) ≫
      (DerivedCategory.homologyFunctorFactors B 0).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
        (DerivedCategory.homologyFunctorFactors B 0).hom.app L ≫
          HomologicalComplex.homologyMap φ 0 :=
    (DerivedCategory.homologyFunctorFactors B 0).hom.naturality φ
  have hinv : (DerivedCategory.homologyFunctorFactors B 0).inv.app L ≫
      (DerivedCategory.homologyFunctorFactors B 0).hom.app L = 𝟙 _ :=
    (DerivedCategory.homologyFunctorFactors B 0).inv_hom_id_app L
  have hG : F.map ((DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).inv.app N) =
      F.map (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 N).inv ≫
        F.map ((DerivedCategory.homologyFunctorFactors A 0).inv.app K) :=
    (congrArg F.map (singleFunctorCompHomologyFunctorIso_inv_app A N)).trans (F.map_comp _ _)
  exact unbounded_algebra (singleFunctorCompHomologyFunctorIso_inv_app B (F.obj N)) hQ hm hn
    hinv (singleObjHomologySelfIso_inv_comp_complexHomologyIso F N) hG

end Unbounded

/-! ### The bounded below derived category -/

section Plus

attribute [local instance]
  CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B] [EnoughInjectives A]

omit [PreservesFiniteColimits F] in
/-- **The isomorphism `F ≅ H⁰(RF((-)[0]))` of a left exact functor is the canonical map
`Stacks.DerivedIndexing.rightDerivedPlusUnitSingle` read by `H⁰`**, after the identification of the
cohomology of `F(N)[0]` with `F(N)`. -/
theorem isoRightDerivedPlusSingle_zero_hom_app (N : A) :
    (F.isoRightDerivedPlusSingle 0).hom.app N =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app (F.obj N) ≫
        (DerivedCategory.Plus.homologyFunctor B 0).map
          ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle F).app N) := by
  rw [F.isoRightDerivedPlusSingle_hom_app 0 N]
  change _ = _ ≫ (DerivedCategory.Plus.homologyFunctor B 0).map (_ ≫ _ ≫ _)
  rw [Functor.map_comp, Functor.map_comp]
  rfl

/-- The cancellation behind
`isoRightDerivedPlusSingle_hom_app_comp_exactRightDerivedPlusHomologyIso`, stated on
variables. -/
private theorem plus_algebra {E : Type*} [Category* E] {O₁ O₂ O₃ O₄ O₅ O₆ : E}
    {X : O₁ ⟶ O₂} {u : O₂ ⟶ O₃} {r : O₃ ⟶ O₄} {ε : O₄ ⟶ O₅} {ε' : O₃ ⟶ O₆} {m : O₆ ⟶ O₅}
    {fi : O₂ ⟶ O₆} {fh : O₆ ⟶ O₂} {ms : O₅ ⟶ O₆} {es : O₁ ⟶ O₅}
    (h₁ : r ≫ ε = ε' ≫ m) (h₂ : u ≫ ε' = fi) (h₃ : es ≫ ms ≫ fh = X) (h₄ : fh ≫ fi = 𝟙 _)
    (h₅ : ms ≫ m = 𝟙 _) : X ≫ u ≫ r ≫ ε = es := by
  rw [h₁, reassoc_of% h₂, ← h₃]
  simp only [Category.assoc]
  rw [reassoc_of% h₄, h₅, Category.comp_id]

/-- The last regrouping of
`isoRightDerivedPlusSingle_hom_app_comp_exactRightDerivedPlusHomologyIso`, stated on variables. -/
private theorem final_algebra {E : Type*} [Category* E] {P Q₁ Q₂ Q₃ Q₄ Q₅ U : E} {s : P ⟶ Q₁}
    {x : Q₁ ⟶ Q₂} {y : Q₂ ⟶ Q₃} {z : Q₃ ⟶ Q₄} {t : Q₄ ⟶ Q₅} {d : Q₅ ⟶ U} {e : Q₁ ⟶ Q₅}
    {G : P ⟶ U} (h : x ≫ y ≫ z ≫ t = e) (h' : s ≫ e ≫ d = G) :
    (s ≫ x ≫ y ≫ z) ≫ t ≫ d = G := by
  rw [← h', ← h]
  simp only [Category.assoc]

/-- **For an exact functor the two identifications `F ≅ H⁰(RF((-)[0]))` agree.** The
isomorphism `CategoryTheory.Functor.isoRightDerivedPlusSingle F 0` of [Stacks, Tag 05TD] (3),
followed by the comparison `Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso F 0` at the
complex `N[0]`, is `F` of the identification of the cohomology of `N[0]` with `N`. -/
theorem isoRightDerivedPlusSingle_hom_app_comp_exactRightDerivedPlusHomologyIso (N : A) :
    (F.isoRightDerivedPlusSingle 0).hom.app N ≫
        (exactRightDerivedPlusHomologyIso F 0).hom.app
          ((DerivedCategory.Plus.singleFunctor A 0).obj N) =
      F.map ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app N) := by
  let H := DerivedCategory.Plus.homologyFunctor B 0
  have hI := F.isoRightDerivedPlusSingle_hom_app 0 N
  have hE : (exactRightDerivedPlusHomologyIso F 0).hom.app
        ((DerivedCategory.Plus.singleFunctor A 0).obj N) =
      H.map ((exactMapDerivedCategoryPlusIso F).inv.app
          ((DerivedCategory.Plus.singleFunctor A 0).obj N)) ≫
        (derivedHomologyIso F 0).hom.app
          (DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor A 0).obj N)) := rfl
  have h₁ := (exactMapDerivedCategoryPlusIso F).inv.naturality
    ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app N)
  have h₂ : F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor A 0).obj N) ≫
      (exactMapDerivedCategoryPlusIso F).inv.app
        (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor A 0).obj N)) =
      F.mapDerivedCategoryPlusFactorsh.inv.app
        ((HomotopyCategory.Plus.singleFunctor A 0).obj N) := by
    rw [exactMapDerivedCategoryPlusIso_inv_app_Qh]
    simp
  have h₃ := exactSingleFunctorRightDerivedPlusIso_residual F N
  have h₄ := F.mapDerivedCategoryPlusFactorsh.hom_inv_id_app
    ((HomotopyCategory.Plus.singleFunctor A 0).obj N)
  have h₅ : F.mapDerivedCategoryPlus.map
        ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).hom.app N) ≫
      F.mapDerivedCategoryPlus.map ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app N) =
        𝟙 _ :=
    (F.mapDerivedCategoryPlus.map_comp _ _).symm.trans
      ((congrArg F.mapDerivedCategoryPlus.map
        ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).hom_inv_id_app N)).trans
          (F.mapDerivedCategoryPlus.map_id _))
  have hX := plus_algebra h₁ h₂ h₃ h₄ h₅
  have hU := singleFunctorCompHomologyFunctorIso_inv_comp_derivedHomologyIso F N
  have hι := ι_map_exactMapDerivedCategoryPlusSingle_inv_app F 0 N
  have h : H.map ((Functor.mapSingleFunctorCompQhIso F).inv.app N) ≫
      H.map (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor A 0).obj N)) ≫
        H.map (F.rightDerivedFunctorPlus.map
          ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app N)) ≫
          H.map ((exactMapDerivedCategoryPlusIso F).inv.app
            ((DerivedCategory.Plus.singleFunctor A 0).obj N)) =
      H.map ((exactMapDerivedCategoryPlusSingle F 0).inv.app N) := by
    rw [← H.map_comp, ← H.map_comp, ← H.map_comp]
    exact congrArg H.map hX
  have h' : (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app (F.obj N) ≫
      H.map ((exactMapDerivedCategoryPlusSingle F 0).inv.app N) ≫
        (derivedHomologyIso F 0).hom.app
          (DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor A 0).obj N)) =
      F.map ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app N) :=
    (congrArg (fun z => (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).inv.app
        (F.obj N) ≫ (DerivedCategory.homologyFunctor B 0).map z ≫
          (derivedHomologyIso F 0).hom.app ((DerivedCategory.singleFunctor A 0).obj N)) hι).trans hU
  rw [hI, hE]
  exact final_algebra h h'

end Plus

end Stacks.DerivedFunctor

end
