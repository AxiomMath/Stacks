module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.SerreSheafFunctoriality
public import StacksFrontier.Topology.Sheaves.Cohomology.CechRefinements.CohomologyCompatibility
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.DegreeSectionBaseChange
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactMapDerivedPlusIsoApp
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactDerivedHomologyComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompositionQhComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactPlusCompositionNatTrans
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import StacksFrontier.Homology.PseudoCoherent.ChangeOfRings
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.ChartGamma
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistCohomologyMonomial

/-!
# Exact functors on derived categories and Čech refinement for `SerreSheafBaseChange`

The comparison of the derived functor of an exact functor with its degreewise action, and
[Stacks, Tag 01FD] on explicit Čech complexes (the refinement map of an `f`-map).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

attribute [local instance 5000] IsGrothendieckAbelian.enoughInjectives
attribute [local instance 5000]
  instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover

namespace Stacks.DerivedFunctor

section Exact

attribute [local instance]
  CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  (T : C ⥤ D) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]

/-- A composite with an isomorphism cancelled, stated on variables. -/
theorem comp_cancel_of_eq {E : Type*} [Category* E] {P Q R S W T : E} (a : P ⟶ Q) (u : Q ⟶ R)
    (m : R ⟶ S) (e : S ⟶ T) (e' : R ⟶ W) (k : W ⟶ T) (v : R ⟶ Q) (f : Q ⟶ W)
    (h₁ : m ≫ e = e' ≫ k) (h₂ : e' = v ≫ f) (h₃ : u ≫ v = 𝟙 _) :
    (a ≫ u ≫ m) ≫ e = a ≫ f ≫ k := by
  rw [Category.assoc, Category.assoc, h₁, h₂, Category.assoc, reassoc_of% h₃]

/-- Inverting a commuting square of three isomorphisms, stated on variables. -/
theorem inv_comp_inv_comp_of_comm {E : Type*} [Category* E] {A B C' D' : E} (x : A ≅ B)
    (y : B ≅ D') (z : A ⟶ C') (w : C' ≅ D') (h : x.hom ≫ y.hom = z ≫ w.hom) :
    y.inv ≫ x.inv ≫ z = w.inv := by
  rw [← cancel_mono w.hom, Category.assoc, Category.assoc, ← h, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Iso.inv_hom_id]

/-- A functor applied to a composite, followed by a morphism, stated on variables. -/
theorem map_comp_comp_of_eq {E E' : Type*} [Category* E] [Category* E'] (F : E ⥤ E')
    {A B C' : E} {Z : E'} (a : A ⟶ B) (b : B ⟶ C') (d : A ⟶ C') (c : F.obj C' ⟶ Z)
    (h : a ≫ b = d) : F.map a ≫ F.map b ≫ c = F.map d ≫ c := by
  rw [← h, F.map_comp, Category.assoc]

/-- The image of an inverse, followed by the image of the morphism, stated on variables. -/
theorem map_inv_comp_map_hom_comp {E E' : Type*} [Category* E] [Category* E'] (F : E ⥤ E')
    {A B : E} {Z : E'} (x : A ≅ B) (r : F.obj B ⟶ Z) :
    F.map x.inv ≫ F.map x.hom ≫ r = r := by
  rw [← Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id, Category.id_comp]

/-- The derived-functor unit of an exact functor at a bounded below complex, followed by the
identification of its right derived functor with its degreewise action, is the factorization of
that action through the homotopy category, conjugated by the comparisons of the two
localizations. -/
theorem unit_comp_exactMapDerivedCategoryPlusIso_inv (K : CochainComplex.Plus C) :
    T.mapCochainComplexPlusDerivedUnit.app K ≫
        (exactMapDerivedCategoryPlusIso T).inv.app (DerivedCategory.Plus.Q.obj K) =
      (DerivedCategory.Plus.quotientCompQhIso D).inv.app (T.mapCochainComplexPlus.obj K) ≫
        T.mapDerivedCategoryPlusFactorsh.inv.app ((HomotopyCategory.Plus.quotient C).obj K) ≫
        T.mapDerivedCategoryPlus.map ((DerivedCategory.Plus.quotientCompQhIso C).hom.app K) := by
  have : T.PreservesHomology := inferInstance
  have := T.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  exact comp_cancel_of_eq _ _ _ _ _ _ _ _
    ((exactMapDerivedCategoryPlusIso T).inv.naturality
      ((DerivedCategory.Plus.quotientCompQhIso C).hom.app K))
    (exactMapDerivedCategoryPlusIso_inv_app_Qh T _)
    ((asIso T.rightDerivedFunctorPlusUnith).hom_inv_id_app _)

/-- The unit of an exact functor and the comparison with its degreewise action, read in the
unbounded derived category, invert the factorization of that action through complexes. -/
theorem ι_map_unit_comp_exactMapDerivedCategoryPlusIso_inv (K : CochainComplex.Plus C) :
    DerivedCategory.Plus.ι.map (T.mapCochainComplexPlusDerivedUnit.app K ≫
        (exactMapDerivedCategoryPlusIso T).inv.app (DerivedCategory.Plus.Q.obj K)) =
      T.mapDerivedCategoryFactors.inv.app K.obj := by
  have h := inv_comp_inv_comp_of_comm
    (T.mapDerivedCategoryFactorsh.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K.obj))
    ((DerivedCategory.quotientCompQhIso D).app
      ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj))
    (T.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app K.obj))
    (T.mapDerivedCategoryFactors.app K.obj)
    (mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso T K.obj)
  refine (congrArg DerivedCategory.Plus.ι.map
    (unit_comp_exactMapDerivedCategoryPlusIso_inv T K)).trans ?_
  refine (DerivedCategory.Plus.ι.map_comp _ _).trans ?_
  refine (congrArg (fun z => _ ≫ z) (DerivedCategory.Plus.ι.map_comp _ _)).trans ?_
  refine Eq.trans ?_ h
  exact congrArg₂ (· ≫ ·) (Stacks.DerivedIndexing.ι_map_quotientCompQhIso_inv_app _)
    (congrArg₂ (· ≫ ·) (ι_map_mapDerivedCategoryPlusFactorsh_inv_app T _)
      (congrArg T.mapDerivedCategory.map
        (Stacks.DerivedIndexing.ι_map_quotientCompQhIso_hom_app K)))

/-- **The cohomology comparison of an exact functor, on a bounded below complex.** The
derived-functor unit at `K`, read on `H^q` and followed by the comparison `H^q ∘ RT ≅ T ∘ H^q`, is
the comparison of the homology of the complex of `T`-images with the `T`-image of the homology,
conjugated by the factorizations of `H^q` through complexes. -/
theorem homology_unit_comp_exactRightDerivedPlusHomologyIso (q : ℤ) (K : CochainComplex.Plus C) :
    (DerivedCategory.Plus.homologyFunctor D q).map (T.mapCochainComplexPlusDerivedUnit.app K) ≫
        (exactRightDerivedPlusHomologyIso T q).hom.app (DerivedCategory.Plus.Q.obj K) =
      (DerivedCategory.homologyFunctorFactors D q).hom.app
          ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj) ≫
        (complexHomologyIso T (ComplexShape.up ℤ) q).hom.app K.obj ≫
        T.map ((DerivedCategory.homologyFunctorFactors C q).inv.app K.obj) := by
  refine (map_comp_comp_of_eq (DerivedCategory.homologyFunctor D q) _ _ _ _
    ((DerivedCategory.Plus.ι.map_comp _ _).symm.trans
      (ι_map_unit_comp_exactMapDerivedCategoryPlusIso_inv T K))).trans ?_
  refine (congrArg (fun z => _ ≫ z) (derivedHomologyIso_hom_app_Q T q K.obj)).trans ?_
  exact map_inv_comp_map_hom_comp _ (T.mapDerivedCategoryFactors.app K.obj) _

omit [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T] in
/-- The cycle-level square behind `homologyMap_mapExtendIso_comp_mapHomologyIso`, stated on
variables. -/
theorem cycles_square {Pc Qc Rc W0 : D} {Mc Nc X0 Lq : C}
    (cm : Pc ⟶ Qc) (mc₁ : Qc ⟶ T.obj Mc) (ec₁ : Mc ⟶ Nc) (iL : Nc ⟶ Lq) (iE : Mc ⟶ X0)
    (xL : X0 ≅ Lq) (iTE : Qc ⟶ T.obj X0) (iTLe : Pc ⟶ W0) (mf : W0 ⟶ T.obj X0)
    (xTL : W0 ≅ T.obj Lq) (ec₂ : Pc ⟶ Rc) (iTL : Rc ⟶ T.obj Lq) (mc₂ : Rc ⟶ T.obj Nc)
    [Mono (T.map iL)]
    (hc₁ : ec₁ ≫ iL = iE ≫ xL.hom) (hc₂ : ec₂ ≫ iTL = iTLe ≫ xTL.hom)
    (hm₁ : mc₁ ≫ T.map iE = iTE) (hm₂ : mc₂ ≫ T.map iL = iTL)
    (hcm : cm ≫ iTE = iTLe ≫ mf) (hX : mf = xTL.hom ≫ T.map xL.inv) :
    cm ≫ mc₁ ≫ T.map ec₁ = ec₂ ≫ mc₂ := by
  rw [← cancel_mono (T.map iL), Category.assoc, Category.assoc, ← T.map_comp, hc₁, T.map_comp,
    ← Category.assoc mc₁, hm₁, ← Category.assoc, hcm, hX, Category.assoc, Category.assoc,
    ← T.map_comp, Iso.inv_hom_id, T.map_id, Category.comp_id, Category.assoc, hm₂, hc₂]

omit [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T] in
/-- The homology-level square behind `homologyMap_mapExtendIso_comp_mapHomologyIso`, stated on
variables. -/
theorem homology_square {Pc Qc Rc Hp Hq Hr : D} {Mc Nc HM HN : C}
    (πp : Pc ⟶ Hp) (πq : Qc ⟶ Hq) (πr : Rc ⟶ Hr) (πM : Mc ⟶ HM) (πN : Nc ⟶ HN)
    (cm : Pc ⟶ Qc) (mc₁ : Qc ⟶ T.obj Mc) (ec₁ : Mc ⟶ Nc) (ec₂ : Pc ⟶ Rc) (mc₂ : Rc ⟶ T.obj Nc)
    (A : Hp ⟶ Hq) (B : Hq ⟶ T.obj HM) (eL : HM ⟶ HN) (D₀ : Hp ⟶ Hr) (E₀ : Hr ⟶ T.obj HN)
    [Epi πp]
    (n1 : πp ≫ A = cm ≫ πq) (n2 : πq ≫ B = mc₁ ≫ T.map πM) (n3 : πM ≫ eL = ec₁ ≫ πN)
    (n4 : πp ≫ D₀ = ec₂ ≫ πr) (n5 : πr ≫ E₀ = mc₂ ≫ T.map πN)
    (hcyc : cm ≫ mc₁ ≫ T.map ec₁ = ec₂ ≫ mc₂) :
    A ≫ B ≫ T.map eL = D₀ ≫ E₀ := by
  rw [← cancel_epi πp, reassoc_of% n1, reassoc_of% n2, ← T.map_comp, n3, T.map_comp,
    reassoc_of% n4, n5, ← Category.assoc, ← Category.assoc, ← Category.assoc, Category.assoc cm,
    hcyc, Category.assoc]

omit [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C] in
/-- **The homology comparison of an exact functor commutes with extension by zero.** For a
complex `L` indexed by `ℕ`, the comparison for the extension of `L` to `ℤ`, read through the
identifications of the homology of an extension with the homology of the complex, is the
comparison for `L`. -/
theorem homologyMap_mapExtendIso_comp_mapHomologyIso (L : CochainComplex C ℕ) (q : ℕ) :
    HomologicalComplex.homologyMap
          (Stacks.DerivedIndexing.mapExtendIso T ComplexShape.embeddingUpNat L).hom (q : ℤ) ≫
        (((L.extend ComplexShape.embeddingUpNat).sc (q : ℤ)).mapHomologyIso T).hom ≫
        T.map (L.extendHomologyIso ComplexShape.embeddingUpNat (j := q) (j' := (q : ℤ))
          (by simp)).hom =
      (((T.mapHomologicalComplex (ComplexShape.up ℕ)).obj L).extendHomologyIso
          ComplexShape.embeddingUpNat (j := q) (j' := (q : ℤ)) (by simp)).hom ≫
        ((L.sc q).mapHomologyIso T).hom :=
  homology_square T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (HomologicalComplex.homologyπ_naturality
      (Stacks.DerivedIndexing.mapExtendIso T ComplexShape.embeddingUpNat L).hom (q : ℤ))
    (Stacks.Homology.mapHomologyIso_homologyπ ((L.extend ComplexShape.embeddingUpNat).sc (q : ℤ)) T)
    (HomologicalComplex.homologyπ_extendHomologyIso_hom _ _ _)
    (HomologicalComplex.homologyπ_extendHomologyIso_hom _ _ _)
    (Stacks.Homology.mapHomologyIso_homologyπ (L.sc q) T)
    (cycles_square T _ _ _ _ _ _ _ _ _ _ _ _ _
      (HomologicalComplex.extendCyclesIso_hom_iCycles _ _ _)
      (HomologicalComplex.extendCyclesIso_hom_iCycles _ _ _)
      (ShortComplex.mapCyclesIso_hom_iCycles ((L.extend ComplexShape.embeddingUpNat).sc (q : ℤ)) T)
      (ShortComplex.mapCyclesIso_hom_iCycles (L.sc q) T)
      (HomologicalComplex.cyclesMap_i
        (Stacks.DerivedIndexing.mapExtendIso T ComplexShape.embeddingUpNat L).hom (q : ℤ))
      (Stacks.DerivedIndexing.mapExtendIso_hom_f_eq T ComplexShape.embeddingUpNat L
        (i := q) (i' := (q : ℤ)) (by simp)))

/-- Splitting a homology map of a composite on the right of an equation, stated on variables. -/
theorem eq_comp_homologyMap_comp {C₀ : Type*} [Category* C₀] [HasZeroMorphisms C₀] {κ : Type*}
    {c : ComplexShape κ} {K₁ K₂ K₃ : HomologicalComplex C₀ c} (p : κ) [K₁.HasHomology p]
    [K₂.HasHomology p] [K₃.HasHomology p] {A : C₀} (a : A ⟶ K₃.homology p)
    (g : A ⟶ K₁.homology p) (x : K₁ ⟶ K₂) (y : K₂ ⟶ K₃)
    (h : a = g ≫ HomologicalComplex.homologyMap (x ≫ y) p) :
    a = g ≫ HomologicalComplex.homologyMap x p ≫ HomologicalComplex.homologyMap y p := by
  rw [h, HomologicalComplex.homologyMap_comp]

/-- Replacing the middle factor of a composite by an equal morphism, stated on variables. -/
theorem comp_middle_eq {C₀ : Type*} [Category* C₀] {P Q R W : C₀} (a : P ⟶ Q) (f₂ m₂ : Q ⟶ R)
    (t : R ⟶ W) (r : P ⟶ W) (hc : f₂ = m₂) (h : a ≫ m₂ ≫ t = r) : a ≫ f₂ ≫ t = r := by
  rw [hc]; exact h

/-- The pasting behind `cechCohomologyToCohomology_comp_derivedModuleGlobalSectionsMap`, stated on
variables. -/
theorem refinement_paste {C₀ C₁ : Type*} [Category* C₀] [Category* C₁] (T : C₀ ⥤ C₁)
    {A0 A1 A2 B1 B2 B3 C1 D1 D2 D2' E2 : C₁} {M2 MK MH MR : C₀}
    (cY : A0 ⟶ A1) (HD : A1 ⟶ A2) (Hci : A2 ⟶ B3) (E1 : B3 ⟶ T.obj MR)
    (HQ : A0 ⟶ B1) (Hu : B1 ⟶ B2) (HRc : B2 ⟶ B3) (Hch : B3 ⟶ A2)
    (E0 : B2 ⟶ T.obj MH) (a4 : MH ⟶ MR) (f1 : B1 ⟶ C1) (f2 : C1 ⟶ T.obj M2) (a3 : M2 ⟶ MH)
    (g1 : A0 ⟶ D1) (hext : D1 ⟶ D2) (hmei : D2 ⟶ C1) (eK : M2 ≅ MK) (eTK : D2 ⟶ E2)
    (mK : E2 ⟶ T.obj MK) (eKY : D1 ⟶ D2') (hγn : D2' ⟶ E2)
    (h01FD : HQ ≫ Hu ≫ HRc ≫ Hch = cY ≫ HD) (hcomp : Hch ≫ Hci = 𝟙 B3)
    (hE : HRc ≫ E1 = E0 ≫ T.map a4) (hL : Hu ≫ E0 = f1 ≫ f2 ≫ T.map a3)
    (hQ : HQ ≫ f1 = g1 ≫ hext ≫ hmei)
    (hM : hmei ≫ f2 ≫ T.map eK.hom = eTK ≫ mK) (hX : hext ≫ eTK = eKY ≫ hγn) :
    cY ≫ HD ≫ Hci ≫ E1 = (g1 ≫ eKY) ≫ hγn ≫ mK ≫ T.map (eK.inv ≫ a3 ≫ a4) := by
  have h1 : cY ≫ HD ≫ Hci ≫ E1 = HQ ≫ Hu ≫ E0 ≫ T.map a4 := by
    rw [← Category.assoc cY, ← h01FD]
    simp only [Category.assoc]
    rw [reassoc_of% hcomp, hE]
  rw [h1, reassoc_of% hL, reassoc_of% hQ, T.map_comp, T.map_comp]
  have h2 : hmei ≫ f2 ≫ T.map a3 ≫ T.map a4 =
      eTK ≫ mK ≫ T.map eK.inv ≫ T.map a3 ≫ T.map a4 := by
    rw [← Category.assoc eTK, ← hM]
    simp only [Category.assoc, ← T.map_comp_assoc, Iso.hom_inv_id_assoc]
  rw [h2, reassoc_of% hX]
  simp only [Category.assoc]

/-- The pasting behind `twistBaseChangeCohomology_comp_cechHomologyIso`, stated on variables. -/
theorem final_paste {C₀ C₁ : Type*} [Category* C₀] [Category* C₁] (T : C₀ ⥤ C₁)
    {P A0 A1 A2 A3 B1 B2 : C₁} {MR MP MK0 MK : C₀}
    (rdY : P ⟶ A1) (cY : A0 ⟶ A1) (icY : A1 ⟶ A0) (HD : A1 ⟶ A2) (Hci : A2 ⟶ A3)
    (E : A3 ⟶ T.obj MR)
    (rdXinv : MR ⟶ MP) (rdX : MP ⟶ MR) (cX : MK0 ⟶ MR) (icX : MR ⟶ MK0) (cpX : MK0 ≅ MK)
    (cp : A0 ⟶ B1) (m : B1 ⟶ B2) (r : B2 ⟶ T.obj MK)
    (h : cY ≫ HD ≫ Hci ≫ E = cp ≫ m ≫ r ≫ T.map (cpX.inv ≫ cX)) (hY : icY ≫ cY = 𝟙 _)
    (hX : cX ≫ icX = 𝟙 _) (hrd : rdXinv ≫ rdX = 𝟙 _) :
    (rdY ≫ HD ≫ Hci ≫ E ≫ T.map rdXinv) ≫ T.map (rdX ≫ icX ≫ cpX.hom) =
      (rdY ≫ icY ≫ cp) ≫ m ≫ r := by
  have ha : HD ≫ Hci ≫ E = icY ≫ cp ≫ m ≫ r ≫ T.map (cpX.inv ≫ cX) := by
    rw [← h, ← Category.assoc icY, hY, Category.id_comp]
  simp only [Category.assoc]
  rw [reassoc_of% ha]
  simp only [Category.assoc, ← T.map_comp]
  rw [reassoc_of% hrd, reassoc_of% hX, Iso.inv_hom_id, T.map_id, Category.comp_id]

end Exact

end Stacks.DerivedFunctor


namespace Stacks.Cohomology.CechRefinement

open Stacks.Cohomology.CechSheaf Stacks.Cohomology.CechDerived
open Stacks.Cohomology.Basis (res res_app res_res res_zero)
open Stacks.CategoryTheory.CechComplex (inter)
open RingedSpaceModuleAdjunction (modulePullback)

attribute [local instance 2000] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  {Ix Jy : Type u} (U : Ix → Opens X.carrier) (V : Jy → Opens Y.carrier)
  (hU : (⊤ : Opens X.carrier) = ⨆ i, U i) (hV : (⊤ : Opens Y.carrier) = ⨆ j, V j)
  (F : Modules X) (G : Modules Y)
  (φ : (modulePullback f).obj G ⟶ F)
  (c : Ix → Jy) (hc : ∀ i, U i ≤ (Opens.map f.hom.base).obj (V (c i)))
  [HasSheafify (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat]
  [(Opens.grothendieckTopology (X : TopCat)).WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify (Opens.grothendieckTopology (Y : TopCat)) AddCommGrpCat]
  [(Opens.grothendieckTopology (Y : TopCat)).WEqualsLocallyBijective AddCommGrpCat]
  [EnoughInjectives (Modules X)] [EnoughInjectives (Modules Y)]

/-- The canonical map from Čech cohomology to cohomology is the cohomology of the derived
comparison. -/
theorem cechCohomologyToCohomology_app_eq {Z : Type u} [TopologicalSpace Z]
    (O : Sheaf (Opens.grothendieckTopology Z) RingCat.{u}) (W : Opens Z) {I : Type u}
    (Wi : I → Opens Z) (hW : W = ⨆ i, Wi i)
    [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [EnoughInjectives (SheafOfModules.{u} O)] (p : ℤ) (M : SheafOfModules.{u} O) :
    (cechCohomologyToCohomology O W Wi hW p).app M =
      (DerivedCategory.Plus.homologyFunctor _ p).map
        ((cechToDerivedGlobalSections O W Wi hW).app M) := by
  show (Functor.associator (cechComplexPlusFunctor O W Wi hW) DerivedCategory.Plus.Q
      (DerivedCategory.Plus.homologyFunctor _ p)).inv.app M ≫
    (Functor.whiskerRight (cechToDerivedGlobalSections O W Wi hW)
      (DerivedCategory.Plus.homologyFunctor _ p)).app M = _
  rw [Functor.associator_inv_app, Functor.whiskerRight_app, Category.id_comp]

/-- **[Stacks, Tag 01FD] on the explicit Čech complexes.** The canonical map from Čech to sheaf
cohomology on `Y`, followed by the map on cohomology induced by an `f`-map
`φ : f^* G ⟶ F` and the identification of the cohomology of `X` read over `Γ(Y, 𝒪_Y)` with the
cohomology of `X` with scalars restricted, is the map induced on the homology of the explicit
Čech complexes by the Čech refinement map, followed by the canonical map from Čech to sheaf
cohomology on `X`. -/
theorem cechCohomologyToCohomology_comp_derivedModuleGlobalSectionsMap (p : ℕ) :
    (cechCohomologyToCohomology (ringCatSheaf Y) ⊤ V hV p).app G ≫
        (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).map
          (derivedModuleGlobalSectionsMap f φ) ≫
        (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).map
          ((derivedSectionsScalarComparison f).inv.app
            ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F)) ≫
        (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (restrictGlobalScalars f)
          (p : ℤ)).hom.app _ =
      (Stacks.Cohomology.CechVanishing.cechPlusHomologyIso (ringCatSheaf Y) ⊤ V hV G p).hom ≫
        HomologicalComplex.homologyMap (cechComplexRefinementMap f F G φ U V hU hV c hc) p ≫
        (Stacks.Homology.RestrictScalars.restrictScalarsHomologyIso
          (globalSectionsRingHom f).hom
          ((cechComplexNatFunctor (ringCatSheaf X) ⊤ U hU).obj F) p).hom ≫
        (restrictGlobalScalars f).map
          ((Stacks.Cohomology.CechVanishing.cechPlusHomologyIso (ringCatSheaf X) ⊤ U hU F p).inv ≫
            (cechCohomologyToCohomology (ringCatSheaf X) ⊤ U hU p).app F) := by
  rw [cechCohomologyToCohomology_app_eq (ringCatSheaf X) ⊤ U hU (p : ℤ) F]
  exact Stacks.DerivedFunctor.refinement_paste (restrictGlobalScalars f) _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _
    (cechCohomologyToCohomology_naturality_of_refinement f U V hU hV F G φ c hc (p : ℤ))
    ((DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).mapIso
      ((derivedSectionsScalarComparison f).app
        ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F))).hom_inv_id
    ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (restrictGlobalScalars f)
      (p : ℤ)).hom.naturality ((cechToDerivedGlobalSections (ringCatSheaf X) ⊤ U hU).app F))
    (Stacks.DerivedFunctor.homology_unit_comp_exactRightDerivedPlusHomologyIso
      (restrictGlobalScalars f) (p : ℤ) _)
    (Stacks.DerivedFunctor.eq_comp_homologyMap_comp _ _ _ _ _
      (DerivedCategory.homologyFunctorFactors_hom_naturality
        (cechComplexRefinementMapInt f F G φ U V hU hV c hc) (p : ℤ)))
    (Stacks.DerivedFunctor.comp_middle_eq _ _ _ _ _
      (Stacks.DerivedFunctor.complexHomologyIso_hom_app (ComplexShape.up ℤ) (p : ℤ)
        (restrictGlobalScalars f) _)
      (Stacks.DerivedFunctor.homologyMap_mapExtendIso_comp_mapHomologyIso
        (restrictGlobalScalars f) ((cechComplexNatFunctor (ringCatSheaf X) ⊤ U hU).obj F) p))
    (HomologicalComplex.extendHomologyIso_hom_naturality _ _ _)

/-- Restricting three times is restricting once. -/
theorem res_res3 {Z : TopCat} (Q : (Opens Z)ᵒᵖ ⥤ AddCommGrpCat.{u}) {W₁ W₂ W₃ W₄ : Opens Z}
    (h₁ : W₁ ≤ W₂) (h₂ : W₂ ≤ W₃) (h₃ : W₃ ≤ W₄) (t : ToType (Q.obj (op W₄))) :
    res Q h₁ (res Q h₂ (res Q h₃ t)) = res Q (h₁.trans (h₂.trans h₃)) t := by
  rw [res_res, res_res]

/-- Restriction commutes with the adjoint `G ⟶ f_* F` of an `f`-map. -/
private theorem res_homEquiv_app {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (F : Modules X)
    (G : Modules Y) (φ : (modulePullback f).obj G ⟶ F) {W W' : Opens Y.carrier} (h : W' ≤ W)
    (t : ToType ((abSections G).obj (op W))) :
    res (abSections F) ((Opens.map f.hom.base).monotone h)
        (ConcreteCategory.hom ((RingedSpaceModuleAdjunction.homEquiv f F G φ).val.app (op W)) t) =
      ConcreteCategory.hom ((RingedSpaceModuleAdjunction.homEquiv f F G φ).val.app (op W'))
        (res (abSections G) h t) :=
  res_app (abSections G)
    ((PresheafOfModules.toPresheaf _).map (RingedSpaceModuleAdjunction.homEquiv f F G φ).val) h t

omit [HasSheafify (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat]
  [(Opens.grothendieckTopology (X : TopCat)).WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify (Opens.grothendieckTopology (Y : TopCat)) AddCommGrpCat]
  [(Opens.grothendieckTopology (Y : TopCat)).WEqualsLocallyBijective AddCommGrpCat]
  [EnoughInjectives (Modules X)] [EnoughInjectives (Modules Y)] in
include hc in
/-- A refined intersection lies in the inverse image of the corresponding intersection, for the
intersections of the explicit Čech model. -/
theorem cechInter_le_map_cechInter {n : ℕ} (x : Fin (n + 1) → Ix) :
    CechCochains.inter (X := TopCat.of X.carrier) U x ≤
      (Opens.map f.hom.base).obj (CechCochains.inter (X := TopCat.of Y.carrier) V (c ∘ x)) := by
  intro z hz
  have hi : ∀ a, z ∈ U (x a) := fun a ↦ (iInf_le (fun b ↦ U (x b)) a) hz
  show f.hom.base z ∈ (⨅ a, V ((c ∘ x) a) : Opens Y.carrier)
  rw [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  exact fun a ↦ hc (x a) (hi a)

omit [HasSheafify (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat]
  [(Opens.grothendieckTopology (X : TopCat)).WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify (Opens.grothendieckTopology (Y : TopCat)) AddCommGrpCat]
  [(Opens.grothendieckTopology (Y : TopCat)).WEqualsLocallyBijective AddCommGrpCat]
  [EnoughInjectives (Modules X)] [EnoughInjectives (Modules Y)] in
/-- **The explicit formula for the Čech refinement map of [Stacks, Tag 01FD].** On the explicit
Čech cochains, the component of the image of a cochain at a tuple `x` is the image under the
adjoint `G ⟶ f_* F` of the `f`-map of the component at `c ∘ x`, restricted to the refined
intersection. -/
theorem toCochainFun_cechComplexRefinementMap {n : ℕ}
    (s : ToType (((CategoryTheory.cechComplexFunctor (coverObject V hV)).obj
      (sectionsPresheaf ⊤ G)).X n)) (x : Fin (n + 1) → Ix) :
    toCochainFun ⊤ U hU F
        (ConcreteCategory.hom ((cechComplexRefinementMap f F G φ U V hU hV c hc).f n) s) x =
      res (abSections F) (cechInter_le_map_cechInter f U V c hc x)
        (ConcreteCategory.hom ((RingedSpaceModuleAdjunction.homEquiv f F G φ).val.app
          (op (CechCochains.inter (X := TopCat.of Y.carrier) V (c ∘ x))))
          (toCochainFun ⊤ V hV G s (c ∘ x))) := by
  have hπ := ConcreteCategory.congr_hom
    (cechComplexRefinementMap_comp_map_π f φ (U := U) (V := V) (hU := hU) (hV := hV) (c := c)
      (hc := hc) n x) s
  have hraw : rawcomp ⊤ U hU F
      (ConcreteCategory.hom ((cechComplexRefinementMap f F G φ U V hU hV c hc).f n) s) x =
      res (abSections F) (inter_le_map_inter f U V hU hV c hc n x)
        (ConcreteCategory.hom ((RingedSpaceModuleAdjunction.homEquiv f F G φ).val.app
          (op (inter (coverObject V hV) (c ∘ x)).left)) (rawcomp ⊤ V hV G s (c ∘ x))) := hπ
  have hG : CechCochains.inter (X := TopCat.of Y.carrier) V (c ∘ x) ≤
      (inter (coverObject V hV) (c ∘ x)).left :=
    (Stacks.Cech.cechComplexInter_eq (X := TopCat.of Y.carrier) V (c ∘ x)).ge.trans
      (inter_coverObject_left ⊤ V hV (c ∘ x)).ge
  have hτ' := res_homEquiv_app f F G φ hG (rawcomp ⊤ V hV G s (c ∘ x))
  have htc : toCochainFun ⊤ V hV G s (c ∘ x) =
      res (abSections G) hG (rawcomp ⊤ V hV G s (c ∘ x)) :=
    res_res _ _ _ _
  calc _ = res (abSections F) ((cechInter_le_map_cechInter f U V c hc x).trans
          ((Opens.map f.hom.base).monotone hG))
        (ConcreteCategory.hom ((RingedSpaceModuleAdjunction.homEquiv f F G φ).val.app
          (op (inter (coverObject V hV) (c ∘ x)).left)) (rawcomp ⊤ V hV G s (c ∘ x))) :=
        (congrArg (fun z => res (abSections F)
          (Stacks.Cech.cechComplexInter_eq (X := TopCat.of X.carrier) U x).ge
          (res (abSections F) (inter_coverObject_left ⊤ U hU x).ge z)) hraw).trans
          (res_res3 _ _ _ _ _)
    _ = res (abSections F) (cechInter_le_map_cechInter f U V c hc x)
        (res (abSections F) ((Opens.map f.hom.base).monotone hG)
          (ConcreteCategory.hom ((RingedSpaceModuleAdjunction.homEquiv f F G φ).val.app
            (op (inter (coverObject V hV) (c ∘ x)).left)) (rawcomp ⊤ V hV G s (c ∘ x)))) :=
        (res_res _ _ _ _).symm
    _ = _ := by rw [hτ', htc]

section Ordered

variable {I : Type u} [LinearOrder I] (U' : I → Opens X.carrier) (V' : I → Opens Y.carrier)
  (hU' : (⊤ : Opens X.carrier) = ⨆ i, U' i) (hV' : (⊤ : Opens Y.carrier) = ⨆ j, V' j)
  (hc' : ∀ i, U' i ≤ (Opens.map f.hom.base).obj (V' i))

/-- The explicit Čech cochain map of [Stacks, Tag 01FD] for the identity refinement: the image
under the adjoint of the `f`-map of the component at a tuple, restricted to the refined
intersection. -/
def refineCochain {p : ℕ}
    (b : CechCochains.Cochain (X := TopCat.of Y.carrier) V' (abSections G) p) :
    CechCochains.Cochain (X := TopCat.of X.carrier) U' (abSections F) p := fun x =>
  res (abSections F) (cechInter_le_map_cechInter f U' V' id hc' x)
    (ConcreteCategory.hom ((RingedSpaceModuleAdjunction.homEquiv f F G φ).val.app
      (op (CechCochains.inter (X := TopCat.of Y.carrier) V' x))) (b x))

omit [HasSheafify (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat]
  [(Opens.grothendieckTopology (X : TopCat)).WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify (Opens.grothendieckTopology (Y : TopCat)) AddCommGrpCat]
  [(Opens.grothendieckTopology (Y : TopCat)).WEqualsLocallyBijective AddCommGrpCat]
  [EnoughInjectives (Modules X)] [EnoughInjectives (Modules Y)]
  [LinearOrder I] in
/-- The explicit Čech cochain map of [Stacks, Tag 01FD] preserves alternating cochains. -/
theorem refineCochain_isAlternating {p : ℕ}
    (b : CechCochains.Cochain (X := TopCat.of Y.carrier) V' (abSections G) p)
    (hb : CechCochains.IsAlternating (X := TopCat.of Y.carrier) V' (abSections G) b) :
    CechCochains.IsAlternating (X := TopCat.of X.carrier) U' (abSections F)
      (refineCochain f F G φ U' V' hc' b) := by
  refine ⟨fun i hi => ?_, fun i a a' haa' => ?_⟩
  · show res (abSections F) _ (ConcreteCategory.hom
      ((RingedSpaceModuleAdjunction.homEquiv f F G φ).val.app
        (op (CechCochains.inter (X := TopCat.of Y.carrier) V' i))) (b i)) = 0
    rw [hb.1 i hi]
    exact (congrArg (res (abSections F) _) (map_zero _)).trans (res_zero _ _)
  · show res (abSections F) _ (ConcreteCategory.hom
        ((RingedSpaceModuleAdjunction.homEquiv f F G φ).val.app
          (op (CechCochains.inter (X := TopCat.of Y.carrier) V' (i ∘ Equiv.swap a a'))))
          (b (i ∘ Equiv.swap a a'))) =
      -CechCochains.permIso (X := TopCat.of X.carrier) U' (abSections F) i (Equiv.swap a a')
        (res (abSections F) (cechInter_le_map_cechInter f U' V' id hc' i) (ConcreteCategory.hom
          ((RingedSpaceModuleAdjunction.homEquiv f F G φ).val.app
            (op (CechCochains.inter (X := TopCat.of Y.carrier) V' i))) (b i)))
    rw [hb.2 i a a' haa']
    have hle : CechCochains.inter (X := TopCat.of Y.carrier) V' (i ∘ Equiv.swap a a') ≤
        CechCochains.inter (X := TopCat.of Y.carrier) V' i :=
      le_of_eq (CechCochains.inter_comp_perm (X := TopCat.of Y.carrier) V' i (Equiv.swap a a'))
    have hτ := res_homEquiv_app f F G φ hle (b i)
    have hp : CechCochains.permIso (X := TopCat.of Y.carrier) V' (abSections G) i
        (Equiv.swap a a') (b i) = res (abSections G) hle (b i) := rfl
    have hp' : ∀ t, CechCochains.permIso (X := TopCat.of X.carrier) U' (abSections F) i
        (Equiv.swap a a') t = res (abSections F) (le_of_eq (CechCochains.inter_comp_perm
          (X := TopCat.of X.carrier) U' i (Equiv.swap a a'))) t := fun _ => rfl
    refine ((congrArg (res (abSections F) _) (map_neg _ _)).trans (map_neg _ _)).trans
      (congrArg Neg.neg ?_)
    rw [hp, hp']
    exact (congrArg (res (abSections F) _) hτ.symm).trans
      ((res_res _ _ _ _).trans (res_res _ _ _ _).symm)

/-- The ordered Čech cochain map of [Stacks, Tag 01FD] for the identity refinement. -/
def refineOrd {p : ℕ}
    (v : CechCochains.OrdCochain (X := TopCat.of Y.carrier) V' (abSections G) p) :
    CechCochains.OrdCochain (X := TopCat.of X.carrier) U' (abSections F) p :=
  CechCochains.pi (X := TopCat.of X.carrier) U' (abSections F) p
    (refineCochain f F G φ U' V' hc'
      (CechCochains.c (X := TopCat.of Y.carrier) V' (abSections G) p v))

omit [HasSheafify (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat]
  [(Opens.grothendieckTopology (X : TopCat)).WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify (Opens.grothendieckTopology (Y : TopCat)) AddCommGrpCat]
  [(Opens.grothendieckTopology (Y : TopCat)).WEqualsLocallyBijective AddCommGrpCat]
  [EnoughInjectives (Modules X)] [EnoughInjectives (Modules Y)] in
/-- The ordered Čech cochain map, componentwise. -/
theorem refineOrd_apply {p : ℕ}
    (v : CechCochains.OrdCochain (X := TopCat.of Y.carrier) V' (abSections G) p)
    (k : CechCochains.OrdIndex (I := I) p) :
    refineOrd f F G φ U' V' hc' v k =
      res (abSections F) (cechInter_le_map_cechInter f U' V' id hc' k.1)
        (ConcreteCategory.hom ((RingedSpaceModuleAdjunction.homEquiv f F G φ).val.app
          (op (CechCochains.inter (X := TopCat.of Y.carrier) V' k.1))) (v k)) :=
  congrArg (fun t => res (abSections F) (cechInter_le_map_cechInter f U' V' id hc' k.1)
    (ConcreteCategory.hom ((RingedSpaceModuleAdjunction.homEquiv f F G φ).val.app
      (op (CechCochains.inter (X := TopCat.of Y.carrier) V' k.1))) t))
    (congrFun (CechCochains.pi_c (X := TopCat.of Y.carrier) V' (abSections G) p v) k)

omit [HasSheafify (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat]
  [(Opens.grothendieckTopology (X : TopCat)).WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify (Opens.grothendieckTopology (Y : TopCat)) AddCommGrpCat]
  [(Opens.grothendieckTopology (Y : TopCat)).WEqualsLocallyBijective AddCommGrpCat]
  [EnoughInjectives (Modules X)] [EnoughInjectives (Modules Y)] in
/-- **The Čech refinement map of [Stacks, Tag 01FD] carries the image of an ordered cochain to
the image of its ordered refinement.** -/
theorem refinementMap_orderedToCechComplex {p : ℕ}
    (v : CechCochains.OrdCochain (X := TopCat.of Y.carrier) V' (abSections G) p) :
    (ConcreteCategory.hom ((cechComplexRefinementMap f F G φ U' V' hU' hV' id hc').f p)
        (ConcreteCategory.hom ((orderedToCechComplex ⊤ V' hV' G).f p) v) :
      ToType ((cechComplex.{u, u, u, u} (⊤ : Opens X.carrier) U' hU' F).X p)) =
      ConcreteCategory.hom ((orderedToCechComplex ⊤ U' hU' F).f p)
        (refineOrd f F G φ U' V' hc' v) := by
  refine toCochainFun_injective ⊤ U' hU' F ?_
  refine Eq.trans ?_ (toCochainFun_orderedToCechComplex ⊤ U' hU' F p _).symm
  refine Eq.trans ?_ (CechCochains.c_pi_of_isAlternating (X := TopCat.of X.carrier) U'
    (abSections F) p _ (refineCochain_isAlternating f F G φ U' V' hc' _
      (CechCochains.c_isAlternating (X := TopCat.of Y.carrier) V' (abSections G) p v))).symm
  funext x
  refine (toCochainFun_cechComplexRefinementMap f U' V' hU' hV' F G φ id hc' _ x).trans ?_
  exact congrArg (fun t => res (abSections F) (cechInter_le_map_cechInter f U' V' id hc' x)
    (ConcreteCategory.hom ((RingedSpaceModuleAdjunction.homEquiv f F G φ).val.app
      (op (CechCochains.inter (X := TopCat.of Y.carrier) V' x))) t))
    (congrFun (toCochainFun_orderedToCechComplex ⊤ V' hV' G p v) x)

end Ordered

end Stacks.Cohomology.CechRefinement

end
