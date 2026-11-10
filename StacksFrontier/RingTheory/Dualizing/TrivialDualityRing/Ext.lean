module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.RingTheory.Dualizing.TrivialDualityRing.Basic

/-!
# The cohomology of derived Hom is Ext

For a homomorphism of commutative rings `f : A →+* B` and a derived coextension functor
`RF ≃ RHom(B, -) : D(A) ⥤ D(B)`, the `A`-module `H^q(RF K)` is canonically
`Ext_A^q(B, K)` in every integer degree.

## Main results

* `Dualizing.homologyExtComparison_nonempty` — existence of a natural, normalized Ext
  identification.
* `Dualizing.derivedCoextendScalarsHomologyLinearEquivExt` — the identification itself.

## Implementation notes

The identification carries naturality in the derived argument and a normalization: a morphism
`B[-q] → K` corresponds to its action on the class of `id_B` supplied by the derived unit
`Dualizing.coextendSingleUnit`. This pins down the identification, including its sign, and makes
it compatible with `Dualizing.derivedCoextendScalarsCompDerivedRestrictScalarsIso`. The module
`ULift B` represents the free rank-one `B`-module in the chosen module universe; the comparison
is obtained by combining the adjunction between restriction and `RF` with the fact that
morphisms out of a single-term complex on a projective object compute cohomology.

## References

* [Stacks Project, Tag 0A71](https://stacks.math.columbia.edu/tag/0A71)
-/

@[expose] public section

open CategoryTheory

universe u v wA wB

namespace Dualizing

noncomputable section

variable {A B : Type u} [CommRing A] [CommRing B]
  [HasDerivedCategory.{wA} (ModuleCat.{max v u} A)]
  [HasDerivedCategory.{wB} (ModuleCat.{max v u} B)]

/-- The `A`-linear structure on a `B`-linear category obtained by restricting scalars along
`f : A →+* B`. -/
@[instance_reducible]
private noncomputable def linearAlong
    {A B : Type*} [CommRing A] [CommRing B]
    {C : Type*} [Category* C] [Preadditive C] [CategoryTheory.Linear B C]
    (f : A →+* B) : CategoryTheory.Linear A C where
  homModule X Y := Module.compHom (X ⟶ Y) f
  smul_comp X Y Z r g h := CategoryTheory.Linear.smul_comp X Y Z (f r) g h
  comp_smul X Y Z g r h := CategoryTheory.Linear.comp_smul X Y Z g (f r) h

variable (f : A →+* B)
  (RF : DerivedCategory (ModuleCat.{max v u} A) ⥤
    DerivedCategory (ModuleCat.{max v u} B))
  (α : coextendScalarsToDerivedCategory f ⟶ DerivedCategory.Qh ⋙ RF)

/-- A right adjoint of an `R`-linear functor is `R`-linear. -/
private theorem rightAdjoint_linear
    {R : Type*} [CommRing R]
    {C : Type*} [Category* C] [Preadditive C] [CategoryTheory.Linear R C]
    {D : Type*} [Category* D] [Preadditive D] [CategoryTheory.Linear R D]
    {G : C ⥤ D} {F : D ⥤ C} (adj : G ⊣ F) [G.Linear R] : F.Linear R := by
  apply (Functor.linear_iff R F).2
  intro Y r
  have hc : (adj.homEquiv (F.obj Y) Y) (adj.counit.app Y) = 𝟙 (F.obj Y) := by
    rw [← adj.homEquiv_symm_id Y, Equiv.apply_symm_apply]
  calc
    F.map (r • 𝟙 Y) =
        (adj.homEquiv (F.obj Y) Y) (adj.counit.app Y ≫ (r • 𝟙 Y)) := by
          simpa [hc] using
            (adj.homEquiv_naturality_right (adj.counit.app Y) (r • 𝟙 Y)).symm
    _ = (adj.homEquiv (F.obj Y) Y)
          (G.map (r • 𝟙 (F.obj Y)) ≫ adj.counit.app Y) := by
          rw [G.map_smul]
          simp
    _ = r • 𝟙 (F.obj Y) := by
          rw [adj.homEquiv_naturality_left]
          simp only [hc, Category.comp_id]

/-- Restriction of scalars on derived categories is left adjoint to a derived coextension
functor: the degreewise adjunction derives. -/
private noncomputable def derivedRestrictScalarsAdjunction
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ))] :
    (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory ⊣ RF := by
  let G := ModuleCat.restrictScalars.{max v u} f
  let F := ModuleCat.coextendScalars.{u, u, max v u} f
  let adj := homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f) (.up ℤ)
  let W_A := HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ)
  let W_B := HomotopyCategory.quasiIso (ModuleCat.{max v u} B) (.up ℤ)
  let G' := G.mapDerivedCategory
  let γ : DerivedCategory.Qh ⋙ G' ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    G.mapDerivedCategoryFactorsh.hom
  have hG : G'.IsLeftDerivedFunctor γ W_B :=
    Functor.isLeftDerivedFunctor_of_inverts W_B _ G.mapDerivedCategoryFactorsh
  letI : G'.IsLeftDerivedFunctor γ W_B := hG
  have hGcomp : (G' ⋙ RF).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight γ RF) W_B := by
    exact Functor.isLeftDerivedFunctor_of_inverts W_B _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight G.mapDerivedCategoryFactorsh RF)
  letI : (G' ⋙ RF).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight γ RF) W_B := hGcomp
  letI : G'.IsLeftAdjoint := restrictScalars_mapDerivedCategory_isLeftAdjoint f
  have hFcomp : (RF ⋙ G').IsRightDerivedFunctor
      (Functor.whiskerRight α G' ≫ (Functor.associator _ _ _).hom) W_A := by
    infer_instance
  letI : (RF ⋙ G').IsRightDerivedFunctor
      (Functor.whiskerRight α G' ≫ (Functor.associator _ _ _).hom) W_A := hFcomp
  exact adj.derived W_B W_A γ α

/-- Derived coextension is `A`-linear: it sends `r • g` to `f r • RF g`. -/
private lemma derivedCoextendScalars_map_smul
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ))]
    {K L : DerivedCategory (ModuleCat.{max v u} A)} (r : A) (g : K ⟶ L) :
    RF.map (r • g) = (f r) • RF.map g := by
  let : CategoryTheory.Linear A (ModuleCat.{max v u} B) := linearAlong f
  let : CategoryTheory.Linear A
      (HomotopyCategory (ModuleCat.{max v u} B) (.up ℤ)) := inferInstance
  let : CategoryTheory.Linear A
      (DerivedCategory (ModuleCat.{max v u} B)) := inferInstance
  have : Functor.Linear A (ModuleCat.restrictScalars.{max v u} f) := by
    constructor
    intro X Y h s
    ext x
    rfl
  let : Functor.Linear A RF :=
    rightAdjoint_linear (derivedRestrictScalarsAdjunction f RF α)
  exact RF.map_smul r g

/-- Evaluating a morphism out of the single-term complex on the free rank-one module at the
class of `1` gives a `B`-linear map to cohomology. -/
private noncomputable def freeHomologyLinearMap
    (X : DerivedCategory (ModuleCat.{max v u} B)) (q : ℤ) :
    (((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj
      (ModuleCat.of B (ULift.{v} B))) ⟶ X) →ₗ[B]
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).obj X where
  toFun g := ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).map g)
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{max v u} B) q).inv.app _ (ULift.up 1))
  map_add' g h := by simp
  map_smul' r g := by
    let : Functor.Linear B
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q) :=
      DerivedCategory.homologyFunctor_linear (C := ModuleCat.{max v u} B) B q
    simp

/-- A chain map out of a single-term complex on a projective object which vanishes on
cohomology in that degree is null-homotopic. -/
private lemma chainMap_from_single_eq_zero
    {C : Type*} [Category C] [Abelian C]
    (P : C) [CategoryTheory.Projective P]
    (q : ℤ) (L : CochainComplex C ℤ)
    (g : (CochainComplex.singleFunctor C q).obj P ⟶ L)
    (hg : HomologicalComplex.homologyMap g q = 0) :
    (HomotopyCategory.quotient C (.up ℤ)).map g = 0 := by
  let eP := HomologicalComplex.singleObjXSelf (.up ℤ) q P
  let a : P ⟶ L.X q := eP.inv ≫ g.f q
  have ha : a ≫ L.d q (q + 1) = 0 := by
    dsimp [a]
    rw [Category.assoc, g.comm]
    simp
  let z : P ⟶ L.cycles q := L.liftCycles a (q + 1) (by simp) ha
  have hz : z ≫ L.homologyπ q = 0 := by
    have he : z = (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) q P).inv ≫
        HomologicalComplex.cyclesMap g q := by
      apply (cancel_mono (L.iCycles q)).1
      rw [L.liftCycles_i, Category.assoc, HomologicalComplex.cyclesMap_i]
      dsimp only [a]
      simp [eP, CochainComplex.singleFunctor]
    rw [he, Category.assoc, ← HomologicalComplex.homologyπ_naturality, hg]
    simp
  let S := ShortComplex.mk (L.toCycles (q - 1) q) (L.homologyπ q)
    (L.toCycles_comp_homologyπ (q - 1) q)
  have hS : S.Exact := ShortComplex.exact_of_g_is_cokernel _
    (L.homologyIsCokernel (q - 1) q (by simp))
  let t : P ⟶ L.X (q - 1) := hS.liftFromProjective z hz
  have ht : t ≫ L.d (q - 1) q = a := by
    rw [← L.toCycles_i (q - 1) q, ← Category.assoc]
    change (hS.liftFromProjective z hz ≫ S.f) ≫ L.iCycles q = _
    rw [ShortComplex.Exact.liftFromProjective_comp]
    exact L.liftCycles_i _ _ _ _
  rw [HomotopyCategory.quotient_map_eq_zero_iff]
  let γ := CochainComplex.HomComplex.Cochain.fromSingleMk t
    (show q + (-1 : ℤ) = q - 1 by omega)
  exact ⟨(CochainComplex.HomComplex.Cochain.equivHomotopy _ _).symm
    ⟨γ, by
      apply (CochainComplex.HomComplex.Cochain.fromSingleEquiv
        (show q + 0 = q by simp)).injective
      simp only [CochainComplex.HomComplex.Cochain.ofHom_zero, add_zero]
      dsimp [γ]
      rw [CochainComplex.HomComplex.Cochain.δ_fromSingleMk t
        (show q + (-1 : ℤ) = q - 1 by omega) 0 q (by omega),
        CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
      simpa [CochainComplex.HomComplex.Cochain.fromSingleEquiv,
        CochainComplex.HomComplex.Cochain.ofHom, a, eP] using ht.symm⟩⟩

/-- A morphism in the derived category out of a single-term complex on a projective object is
determined by its effect on cohomology in that degree. -/
private lemma derivedSingleHomologyMap_injective
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : C) [CategoryTheory.Projective P] (q : ℤ)
    {X : DerivedCategory C}
    (g : (DerivedCategory.singleFunctor C q).obj P ⟶ X)
    (hg : (DerivedCategory.homologyFunctor C q).map g = 0) : g = 0 := by
  let S := (CochainComplex.singleFunctor C q).obj P
  have hProj (n : ℤ) : CategoryTheory.Projective (S.X n) := by
    change CategoryTheory.Projective (((HomologicalComplex.single C (.up ℤ) q).obj P).X n)
    infer_instance
  let : S.IsKProjective := CochainComplex.isKProjective_of_projective S q
  let L := (DerivedCategory.Q (C := C)).objPreimage X
  let eX := (DerivedCategory.Q (C := C)).objObjPreimageIso X
  let e := DerivedCategory.quotientCompQhIso C
  let Q := HomotopyCategory.quotient C (.up ℤ)
  let t : DerivedCategory.Qh.obj (Q.obj S) ⟶ DerivedCategory.Qh.obj (Q.obj L) :=
    e.hom.app S ≫ g ≫ eX.inv ≫ e.inv.app L
  obtain ⟨h, hh⟩ := (CochainComplex.IsKProjective.Qh_map_bijective S (Q.obj L)).surjective t
  obtain ⟨φ, hφ⟩ := Q.map_surjective h
  have hQ : (DerivedCategory.Q (C := C)).map φ = g ≫ eX.inv := by
    apply (cancel_epi (e.hom.app S)).1
    apply (cancel_mono (e.inv.app L)).1
    simp only [← Category.assoc]
    rw [← e.hom.naturality φ]
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    change DerivedCategory.Qh.map (Q.map φ) = t
    rw [hφ, hh]
  have hφH : HomologicalComplex.homologyMap φ q = 0 := by
    apply (cancel_epi ((DerivedCategory.homologyFunctorFactors C q).hom.app S)).1
    rw [← DerivedCategory.homologyFunctorFactors_hom_naturality, hQ]
    simp only [Functor.map_comp, hg, CategoryTheory.Limits.zero_comp]
    exact CategoryTheory.Limits.comp_zero.symm
  have hQ0 : (DerivedCategory.Q (C := C)).map φ = 0 := by
    apply (cancel_epi (e.hom.app S)).1
    apply (cancel_mono (e.inv.app L)).1
    rw [← e.hom.naturality φ]
    simp [chainMap_from_single_eq_zero P q L φ hφH]
  rw [hQ] at hQ0
  exact (cancel_mono eX.inv).1 (by simpa using hQ0)

/-- Every map from a projective object into the cohomology of a complex in a given degree is
induced by a chain map out of the single-term complex. -/
private lemma chainMap_from_single_homology
    {C : Type*} [Category C] [Abelian C]
    (P : C) [CategoryTheory.Projective P]
    (q : ℤ) (L : CochainComplex C ℤ) (f : P ⟶ L.homology q) :
    ∃ g : (CochainComplex.singleFunctor C q).obj P ⟶ L,
      HomologicalComplex.homologyMap g q =
        (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) q P).hom ≫ f := by
  let l := CategoryTheory.Projective.factorThru f (L.homologyπ q)
  let g := HomologicalComplex.mkHomFromSingle (l ≫ L.iCycles q)
    (fun k hk => by simp)
  have hc : HomologicalComplex.cyclesMap g q =
      (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) q P).hom ≫ l := by
    apply (cancel_mono (L.iCycles q)).mp
    simp [g, HomologicalComplex.singleObjCyclesSelfIso_hom]
  refine ⟨g, ?_⟩
  apply (cancel_epi (((HomologicalComplex.single C (.up ℤ) q).obj P).homologyπ q)).mp
  simp [hc, Category.assoc, l]

/-- The inverse of the single-functor/cohomology comparison factors through the degreewise
comparison of the single-term complex. -/
private lemma singleFunctorCompHomologyFunctorIso_inv_app
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] (P : C) (q : ℤ) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C q).inv.app P =
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) q P).inv ≫
        (DerivedCategory.homologyFunctorFactors C q).inv.app
          ((CochainComplex.singleFunctor C q).obj P) := by
  simp [DerivedCategory.singleFunctorCompHomologyFunctorIso,
    DerivedCategory.singleFunctorsPostcompQIso,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors]
  rfl

/-- Every map from a projective object into the cohomology of an object of the derived category
is induced by a morphism out of the single-term complex. -/
private lemma derivedSingleHomologyMap_surjective
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : C) [CategoryTheory.Projective P] (q : ℤ)
    (X : DerivedCategory C)
    (f : P ⟶ (DerivedCategory.homologyFunctor C q).obj X) :
    ∃ g : (DerivedCategory.singleFunctor C q).obj P ⟶ X,
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C q).inv.app P ≫
        (DerivedCategory.homologyFunctor C q).map g = f := by
  let L := (DerivedCategory.Q (C := C)).objPreimage X
  let e : DerivedCategory.Q.obj L ≅ X :=
    (DerivedCategory.Q (C := C)).objObjPreimageIso X
  let H := DerivedCategory.homologyFunctor C q
  let eH := DerivedCategory.homologyFunctorFactors C q
  -- `eH` identifies `Q ⋙ H` with the cohomology functor, so its components are typed with
  -- `(Q ⋙ H).obj Y` where the compositions below need `H.obj (Q.obj Y)`. The two agree
  -- definitionally but not syntactically; ascribing the components once here keeps every
  -- composite syntactically well-typed, so the later tactics need no extra
  -- transparency.
  let ε : ∀ Y : CochainComplex C ℤ, H.obj (DerivedCategory.Q.obj Y) ⟶ Y.homology q :=
    fun Y => eH.hom.app Y
  let ε' : ∀ Y : CochainComplex C ℤ, Y.homology q ⟶ H.obj (DerivedCategory.Q.obj Y) :=
    fun Y => eH.inv.app Y
  have hεε' (Y : CochainComplex C ℤ) : ε Y ≫ ε' Y = 𝟙 _ := eH.hom_inv_id_app Y
  have hε'nat {Y Z : CochainComplex C ℤ} (ψ : Y ⟶ Z) :
      HomologicalComplex.homologyMap ψ q ≫ ε' Z =
        ε' Y ≫ H.map (DerivedCategory.Q.map ψ) := eH.inv.naturality ψ
  let f' : P ⟶ L.homology q := f ≫ H.map e.inv ≫ ε L
  obtain ⟨φ, hφ⟩ := chainMap_from_single_homology P q L f'
  let eS := HomologicalComplex.singleObjHomologySelfIso (.up ℤ) q P
  have hsingle :
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C q).inv.app P =
        eS.inv ≫ ε' ((CochainComplex.singleFunctor C q).obj P) :=
    singleFunctorCompHomologyFunctorIso_inv_app P q
  refine ⟨DerivedCategory.Q.map φ ≫ e.hom, ?_⟩
  rw [H.map_comp, hsingle]
  calc
    (eS.inv ≫ ε' ((CochainComplex.singleFunctor C q).obj P)) ≫
          H.map (DerivedCategory.Q.map φ) ≫ H.map e.hom
        = eS.inv ≫ (ε' ((CochainComplex.singleFunctor C q).obj P) ≫
          H.map (DerivedCategory.Q.map φ)) ≫ H.map e.hom := by
      simp only [Category.assoc]
    _ = eS.inv ≫ (HomologicalComplex.homologyMap φ q ≫ ε' L) ≫ H.map e.hom := by
      rw [← hε'nat φ]
    _ = eS.inv ≫ ((eS.hom ≫ f') ≫ ε' L) ≫ H.map e.hom := by rw [hφ]
    _ = f := by
      dsimp only [f']
      simp only [Category.assoc, Iso.inv_hom_id_assoc, hεε', Category.id_comp,
        ← Functor.map_comp, Iso.inv_hom_id]
      rw [H.map_id, Category.comp_id]

omit [HasDerivedCategory.{wB} (ModuleCat.{max v u} B)] in
/-- Two maps out of the free rank-one `B`-module agree as soon as they agree on `1`. -/
private lemma freeHom_ext
    (M : ModuleCat.{max v u} B)
    {g h : ModuleCat.of B (ULift.{v} B) ⟶ M}
    (heq : g (ULift.up 1) = h (ULift.up 1)) : g = h := by
  ext y
  obtain ⟨b⟩ := y
  have hy : (ULift.up b : ULift.{v} B) = b • (ULift.up 1 : ULift.{v} B) := by
    apply ULift.ext
    change b = b * 1
    simp
  rw [hy]
  simpa only [map_smul] using congrArg (fun z => b • z) heq

/-- Morphisms out of the single-term complex on the free rank-one module compute cohomology. -/
private theorem freeHomologyLinearMap_bijective
    (X : DerivedCategory (ModuleCat.{max v u} B)) (q : ℤ) :
    Function.Bijective (freeHomologyLinearMap X q) := by
  let P := ModuleCat.of B (ULift.{v} B)
  have : Module.Projective B (ULift.{v} B) :=
    Module.Projective.of_equiv' (ULift.moduleEquiv (R := B) (M := B)).symm
  have : CategoryTheory.Projective P := ModuleCat.projective_of_categoryTheory_projective P
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q
  let e := DerivedCategory.singleFunctorCompHomologyFunctorIso
    (ModuleCat.{max v u} B) q
  have hzero {g : (DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj P ⟶ X}
      (hg : freeHomologyLinearMap X q g = 0) : g = 0 := by
    have hco : e.inv.app P ≫ H.map g = 0 := by
      apply freeHom_ext
      simpa [freeHomologyLinearMap, P, H, e] using hg
    exact derivedSingleHomologyMap_injective P q g
      ((cancel_epi (e.inv.app P)).1 (by simpa using hco))
  refine ⟨(injective_iff_map_eq_zero _).2 fun _ => hzero, fun x => ?_⟩
  let m : P ⟶ H.obj X :=
    ModuleCat.ofHom ((LinearMap.toSpanSingleton B (H.obj X) x).comp
      ULift.moduleEquiv.toLinearMap)
  obtain ⟨g, hg⟩ := derivedSingleHomologyMap_surjective P q X m
  refine ⟨g, ?_⟩
  simpa [freeHomologyLinearMap, m, P, H, e] using
    congrArg (fun t : P ⟶ H.obj X => t (ULift.up 1)) hg

/-- The resulting linear identification of morphisms out of `B[-q]` with cohomology in
degree `q`. -/
private noncomputable def freeHomologyLinearEquiv
    (X : DerivedCategory (ModuleCat.{max v u} B)) (q : ℤ) :
    (((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj
      (ModuleCat.of B (ULift.{v} B))) ⟶ X) ≃ₗ[B]
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).obj X :=
  LinearEquiv.ofBijective (freeHomologyLinearMap X q)
    (freeHomologyLinearMap_bijective X q)

/-- Restriction of scalars commutes with the single-term complex functor. -/
private noncomputable def restrictSingleIso (q : ℤ) :
    (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj
        (ModuleCat.of B (ULift.{v} B))) ≅
    (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q).obj
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of B (ULift.{v} B))) :=
  ((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategorySingleFunctor q).app _

/-- The unit of the derived adjunction, evaluated at the image of a homotopy class, factors
through the degreewise unit and the derived-functor unit `α`. -/
private lemma derivedRestrictScalarsAdjunction_unit_fac
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ))]
    (X : HomotopyCategory (ModuleCat.{max v u} B) (.up ℤ)) :
    (derivedRestrictScalarsAdjunction f RF α).unit.app (DerivedCategory.Qh.obj X) ≫
      RF.map ((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategoryFactorsh.hom.app X) =
    DerivedCategory.Qh.map
        ((homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f)
          (.up ℤ)).unit.app X) ≫ α.app
      ((ModuleCat.restrictScalars.{max v u} f).mapHomotopyCategory (.up ℤ) |>.obj X) := by
  let G := ModuleCat.restrictScalars.{max v u} f
  let G' := G.mapDerivedCategory
  let γ : DerivedCategory.Qh ⋙ G' ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    G.mapDerivedCategoryFactorsh.hom
  let W_B := HomotopyCategory.quasiIso (ModuleCat.{max v u} B) (.up ℤ)
  let : (G' ⋙ RF).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight γ RF) W_B :=
    Functor.isLeftDerivedFunctor_of_inverts W_B _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight G.mapDerivedCategoryFactorsh RF)
  simpa only [derivedRestrictScalarsAdjunction, Adjunction.derived,
    Adjunction.derived'_unit] using
    (homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f)
      (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso (ModuleCat.{max v u} B) (.up ℤ))
      ((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategoryFactorsh.hom) α X

/-- The Ext group of `B` into `K` in degree `q`, identified additively with the cohomology of
`RF K` by combining the shift, the single-term comparison and the derived adjunction. -/
private noncomputable def extHomologyAddEquiv
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ))]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (q : ℤ) :
    DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of B (ULift.{v} B)))) K q ≃+
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).obj (RF.obj K) :
        Type (max v u)) := by
  let M : ModuleCat.{max v u} A :=
    (ModuleCat.restrictScalars f).obj (ModuleCat.of B (ULift.{v} B))
  let S : DerivedCategory (ModuleCat.{max v u} B) :=
    (DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj
      (ModuleCat.of B (ULift.{v} B))
  let e := (DerivedCategory.singleFunctors (ModuleCat.{max v u} A)).shiftIso q 0 q (by simp)
  let shiftFF := Functor.FullyFaithful.ofFullyFaithful
    (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) q)
  let e₁ : DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj M) K q ≃+
      (((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q).obj M) ⟶ K) :=
    ((CategoryTheory.Linear.homCongr ℤ (e.app M).symm (Iso.refl _)).toAddEquiv).trans
      (AddEquiv.ofBijective
        (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) q).mapAddHom
        ⟨fun x y h => shiftFF.map_injective h,
          fun z => shiftFF.map_surjective z⟩).symm
  let e₂ : (((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q).obj M) ⟶ K) ≃+
      (((ModuleCat.restrictScalars f).mapDerivedCategory.obj S) ⟶ K) :=
    (CategoryTheory.Linear.homCongr ℤ (restrictSingleIso f q).symm (Iso.refl _)).toAddEquiv
  let e₃ := (derivedRestrictScalarsAdjunction f RF α).homAddEquiv S K
  exact e₁.trans (e₂.trans (e₃.trans (freeHomologyLinearEquiv (RF.obj K) q).toAddEquiv))

/-- The normalized map from Ext to cohomology: an Ext class is sent to the image under its
associated morphism of the class of `id_B` supplied by the derived unit. -/
private noncomputable def extToHomology
    (K : DerivedCategory (ModuleCat.{max v u} A)) (q : ℤ)
    (h : DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of B (ULift.{v} B)))) K q) :
    ((ModuleCat.restrictScalars f).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).obj (RF.obj K))) := by
  let M : ModuleCat.{max v u} A :=
    (ModuleCat.restrictScalars f).obj (ModuleCat.of B (ULift.{v} B))
  let e := (DerivedCategory.singleFunctors (ModuleCat.{max v u} A)).shiftIso q 0 q (by simp)
  let shiftFF := Functor.FullyFaithful.ofFullyFaithful
    (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) q)
  let g : (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q).obj M ⟶ K :=
    shiftFF.preimage (e.hom.app M ≫ h)
  let x := coextendSingleUnit f RF α M q
    (((ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f).unit.app
      (ModuleCat.of B (ULift.{v} B))) (ULift.up 1))
  exact (ModuleCat.restrictScalars f).map
    ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).map (RF.map g)) x

/-- The class of `id_B` produced by `Dualizing.coextendSingleUnit` agrees with the one produced
by the unit of the derived adjunction. -/
private theorem coextendSingleUnit_eq_derivedAdjunctionUnit
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ))]
    (q : ℤ) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).map
      ((derivedRestrictScalarsAdjunction f RF α).unit.app
          ((DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj
            (ModuleCat.of B (ULift.{v} B))) ≫
        RF.map (restrictSingleIso f q).hom))
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{max v u} B) q).inv.app _ (ULift.up 1)) =
    coextendSingleUnit f RF α
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of B (ULift.{v} B))) q
      (((ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f).unit.app
        (ModuleCat.of B (ULift.{v} B))) (ULift.up 1)) := by
  let P := ModuleCat.of B (ULift.{v} B)
  let M := (ModuleCat.restrictScalars f).obj P
  let S := (DerivedCategory.singleFunctor (ModuleCat.{max v u} B) q).obj P
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q
  have heq : (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{max v u} B) q).inv.app P ≫
      H.map ((derivedRestrictScalarsAdjunction f RF α).unit.app S ≫
        RF.map (restrictSingleIso f q).hom) =
      (ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f).unit.app P ≫
        coextendSingleUnit f RF α M q := by
    let T := (CochainComplex.singleFunctor (ModuleCat.{max v u} B) q).obj P
    let σ := DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max v u} B) q
    let G := (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory
    let adj := derivedRestrictScalarsAdjunction f RF α
    have hnat : σ.inv.app P ≫ adj.unit.app S =
        adj.unit.app (DerivedCategory.Q.obj T) ≫
          RF.map (G.map (σ.inv.app P)) := by
      exact (adj.unit_naturality _).symm
    have hunit : adj.unit.app S =
        σ.hom.app P ≫ adj.unit.app (DerivedCategory.Q.obj T) ≫
          RF.map (G.map (σ.inv.app P)) := by
      calc
        adj.unit.app S = σ.hom.app P ≫ σ.inv.app P ≫ adj.unit.app S := by simp
        _ = σ.hom.app P ≫ adj.unit.app (DerivedCategory.Q.obj T) ≫
            RF.map (G.map (σ.inv.app P)) := by
              simpa only [Category.assoc] using congrArg (fun t => σ.hom.app P ≫ t) hnat
    let G₀ := ModuleCat.restrictScalars.{max v u} f
    let U := (HomotopyCategory.quotient (ModuleCat.{max v u} B) (.up ℤ)).obj T
    let eB := DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} B)
    let eA := DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} A)
    let γ := G₀.mapHomotopyCategoryFactors (.up ℤ)
    have hq : adj.unit.app (DerivedCategory.Q.obj T) ≫
        RF.map (G₀.mapDerivedCategoryFactors.hom.app T) =
      eB.inv.app T ≫ DerivedCategory.Qh.map
        ((homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f)
          (.up ℤ)).unit.app U) ≫
        α.app ((G₀.mapHomotopyCategory (.up ℤ)).obj U) ≫
        RF.map (DerivedCategory.Qh.map (γ.hom.app T) ≫
          eA.hom.app ((G₀.mapHomologicalComplex (.up ℤ)).obj T)) := by
      have hfac := derivedRestrictScalarsAdjunction_unit_fac f RF α U
      have hnatE : eB.hom.app T ≫ adj.unit.app (DerivedCategory.Q.obj T) =
          adj.unit.app (DerivedCategory.Qh.obj U) ≫
            RF.map (G.map (eB.hom.app T)) := by
        exact (adj.unit_naturality _).symm
      have hδ : G.map (eB.hom.app T) ≫
          G₀.mapDerivedCategoryFactors.hom.app T =
          G₀.mapDerivedCategoryFactorsh.hom.app U ≫
            DerivedCategory.Qh.map (γ.hom.app T) ≫
              eA.hom.app ((G₀.mapHomologicalComplex (.up ℤ)).obj T) := by
        have hγ : DerivedCategory.Qh.map
            ((G₀.mapHomotopyCategoryFactors (.up ℤ)).inv.app T) ≫
            DerivedCategory.Qh.map
              ((G₀.mapHomotopyCategoryFactors (.up ℤ)).hom.app T) = 𝟙 _ := by
          rw [← Functor.map_comp]
          simp
        apply (cancel_mono (eA.inv.app ((G₀.mapHomologicalComplex (.up ℤ)).obj T))).1
        apply (cancel_mono (DerivedCategory.Qh.map (γ.inv.app T))).1
        rw [G₀.mapDerivedCategoryFactorsh_hom_app T]
        let X := (G₀.mapDerivedCategory.map (eB.hom.app T) ≫
          G₀.mapDerivedCategoryFactors.hom.app T) ≫
            eA.inv.app ((G₀.mapHomologicalComplex (.up ℤ)).obj T)
        have hX : (G.map (eB.hom.app T) ≫
            G₀.mapDerivedCategoryFactors.hom.app T) ≫
            eA.inv.app ((G₀.mapHomologicalComplex (.up ℤ)).obj T) = X := rfl
        simp only [← Category.assoc]
        rw [hX]
        dsimp only [γ] at hγ ⊢
        rw [Category.assoc X (DerivedCategory.Qh.map (γ.inv.app T))
          (DerivedCategory.Qh.map (γ.hom.app T)), hγ]
        simp
      apply (cancel_epi (eB.hom.app T)).1
      simpa only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] using
        (calc
          eB.hom.app T ≫ (adj.unit.app (DerivedCategory.Q.obj T) ≫
              RF.map (G₀.mapDerivedCategoryFactors.hom.app T)) =
            (adj.unit.app (DerivedCategory.Qh.obj U) ≫
              RF.map (G.map (eB.hom.app T))) ≫
              RF.map (G₀.mapDerivedCategoryFactors.hom.app T) := by
                rw [← Category.assoc, hnatE]
          _ = adj.unit.app (DerivedCategory.Qh.obj U) ≫
              RF.map (G.map (eB.hom.app T) ≫
                G₀.mapDerivedCategoryFactors.hom.app T) := by simp [Functor.map_comp]
          _ = adj.unit.app (DerivedCategory.Qh.obj U) ≫
              RF.map (G₀.mapDerivedCategoryFactorsh.hom.app U ≫
                DerivedCategory.Qh.map (γ.hom.app T) ≫
                  eA.hom.app ((G₀.mapHomologicalComplex (.up ℤ)).obj T)) := by rw [hδ]
          _ = DerivedCategory.Qh.map
                ((homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f)
                  (.up ℤ)).unit.app U) ≫
              α.app ((G₀.mapHomotopyCategory (.up ℤ)).obj U) ≫
                RF.map (DerivedCategory.Qh.map (γ.hom.app T) ≫
                  eA.hom.app ((G₀.mapHomologicalComplex (.up ℤ)).obj T)) := by
                    rw [Functor.map_comp, ← Category.assoc, hfac]
                    simp [Category.assoc, G₀])
    have hcomp : adj.unit.app S ≫ RF.map (restrictSingleIso f q).hom =
        (σ.hom.app P ≫ (adj.unit.app (DerivedCategory.Q.obj T) ≫
          RF.map (G₀.mapDerivedCategoryFactors.hom.app T))) ≫
          RF.map (DerivedCategory.Q.map
            ((HomologicalComplex.singleMapHomologicalComplex G₀ (.up ℤ) q).hom.app P)) ≫
            RF.map ((DerivedCategory.singleFunctorIsoCompQ
              (ModuleCat.{max v u} A) q).inv.app M) := by
      rw [hunit]
      simp [restrictSingleIso, Functor.mapDerivedCategorySingleFunctor,
        Functor.map_comp, Category.assoc, G, G₀, σ, M]
      rfl
    let Ta := (CochainComplex.singleFunctor (ModuleCat.{max v u} A) q).obj M
    let V := (HomotopyCategory.quotient (ModuleCat.{max v u} A) (.up ℤ)).obj Ta
    let mG := (HomologicalComplex.singleMapHomologicalComplex G₀ (.up ℤ) q).hom.app P
    let tG : (G₀.mapHomotopyCategory (.up ℤ)).obj U ⟶ V :=
      γ.hom.app T ≫
        (HomotopyCategory.quotient (ModuleCat.{max v u} A) (.up ℤ)).map mG
    have hpost : α.app ((G₀.mapHomotopyCategory (.up ℤ)).obj U) ≫
        RF.map (DerivedCategory.Qh.map (γ.hom.app T) ≫
          eA.hom.app ((G₀.mapHomologicalComplex (.up ℤ)).obj T) ≫
            DerivedCategory.Q.map mG) =
      DerivedCategory.Qh.map
          ((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomotopyCategory
            (.up ℤ) |>.map tG) ≫
        α.app V ≫ RF.map (eA.hom.app Ta) := by
      have hnatA : eA.hom.app ((G₀.mapHomologicalComplex (.up ℤ)).obj
          ((CochainComplex.singleFunctor (ModuleCat.{max v u} B) q).obj P)) ≫
          DerivedCategory.Q.map mG =
          DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (ModuleCat.{max v u} A) (.up ℤ)).map mG) ≫
            eA.hom.app ((CochainComplex.singleFunctor (ModuleCat.{max v u} A) q).obj
              (G₀.obj P)) := by
        simpa only [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
          Functor.comp_map, Functor.comp_obj] using
          (eA.hom.naturality mG).symm
      have hnatα : α.app ((G₀.mapHomotopyCategory (.up ℤ)).obj U) ≫
          RF.map (DerivedCategory.Qh.map tG) =
          DerivedCategory.Qh.map
            ((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomotopyCategory
              (.up ℤ) |>.map tG) ≫ α.app V := by
        simpa only [Functor.comp_map] using (α.naturality tG).symm
      calc
        _ = α.app ((G₀.mapHomotopyCategory (.up ℤ)).obj U) ≫
            RF.map (DerivedCategory.Qh.map tG ≫ eA.hom.app Ta) := by
              dsimp only [T, Ta, M]
              rw [hnatA]
              simp [tG, Functor.map_comp, Category.assoc]
              rfl
        _ = α.app ((G₀.mapHomotopyCategory (.up ℤ)).obj U) ≫
            RF.map (DerivedCategory.Qh.map tG) ≫ RF.map (eA.hom.app Ta) := by
              rw [Functor.map_comp]
        _ = DerivedCategory.Qh.map
              ((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomotopyCategory
                (.up ℤ) |>.map tG) ≫
            α.app V ≫ RF.map (eA.hom.app Ta) := by
              simpa only [Category.assoc] using
                congrArg (fun k => k ≫ RF.map (eA.hom.app Ta)) hnatα
    have htotal : adj.unit.app S ≫ RF.map (restrictSingleIso f q).hom =
        σ.hom.app P ≫ eB.inv.app T ≫
          DerivedCategory.Qh.map
            ((homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f)
              (.up ℤ)).unit.app U) ≫
          DerivedCategory.Qh.map
            (((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomotopyCategory
              (.up ℤ)).map tG) ≫
          α.app V ≫ RF.map (eA.hom.app Ta) ≫
          RF.map ((DerivedCategory.singleFunctorIsoCompQ
            (ModuleCat.{max v u} A) q).inv.app M) := by
      calc
        _ = σ.hom.app P ≫ eB.inv.app T ≫
            DerivedCategory.Qh.map
              ((homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f)
                (.up ℤ)).unit.app U) ≫
            (α.app ((G₀.mapHomotopyCategory (.up ℤ)).obj U) ≫
              RF.map (DerivedCategory.Qh.map (γ.hom.app T) ≫
                eA.hom.app ((G₀.mapHomologicalComplex (.up ℤ)).obj T) ≫
                DerivedCategory.Q.map mG)) ≫
            RF.map ((DerivedCategory.singleFunctorIsoCompQ
              (ModuleCat.{max v u} A) q).inv.app M) := by
                rw [hcomp, hq]
                simp [mG, Functor.map_comp, Category.assoc]
        _ = _ := by rw [hpost]; simp [Category.assoc]
    let F₀ := ModuleCat.coextendScalars.{u, u, max v u} f
    let J := (F₀.mapHomologicalComplex (.up ℤ)).obj Ta
    have hsource :
        (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) q P).inv ≫
          (DerivedCategory.homologyFunctorFactors (ModuleCat.{max v u} B) q).inv.app T ≫
          H.map (eB.inv.app T) ≫
          H.map (DerivedCategory.Qh.map
            ((homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f)
              (.up ℤ)).unit.app U)) ≫
          H.map (DerivedCategory.Qh.map ((F₀.mapHomotopyCategory (.up ℤ)).map tG)) =
        (ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f).unit.app P ≫
          (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) q (F₀.obj M)).inv ≫
          HomologicalComplex.homologyMap
            ((HomologicalComplex.singleMapHomologicalComplex F₀ (.up ℤ) q).inv.app M) q ≫
          (DerivedCategory.homologyFunctorFactors (ModuleCat.{max v u} B) q).inv.app J ≫
          H.map (eB.inv.app J) ≫
          H.map (DerivedCategory.Qh.map
            ((F₀.mapHomotopyCategoryFactors (.up ℤ)).inv.app Ta)) := by
      have hγ : γ.hom.app T = 𝟙 ((G₀.mapHomotopyCategory (.up ℤ)).obj U) := rfl
      let adj₀ := ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f
      let ηT : T ⟶ (F₀.mapHomologicalComplex (.up ℤ)).obj
          ((G₀.mapHomologicalComplex (.up ℤ)).obj T) :=
        { f := fun n => adj₀.unit.app (T.X n)
          comm' := by
            intro i j hij
            change adj₀.unit.app (T.X i) ≫ F₀.map (G₀.map (T.d i j)) =
              T.d i j ≫ adj₀.unit.app (T.X j)
            simpa only [Functor.comp_map, Functor.id_map] using
              (adj₀.unit.naturality (T.d i j)).symm }
      have hunitQ :
          (homotopyAdjunction adj₀ (.up ℤ)).unit.app U =
            (HomotopyCategory.quotient (ModuleCat.{max v u} B) (.up ℤ)).map ηT := by
        rfl
      have htG : tG =
          (HomotopyCategory.quotient (ModuleCat.{max v u} A) (.up ℤ)).map mG := by
        dsimp only [tG]
        refine Eq.trans (congrArg (fun z => z ≫
          (HomotopyCategory.quotient (ModuleCat.{max v u} A) (.up ℤ)).map mG) hγ) ?_
        exact Category.id_comp _
      have hmaptG :
          (F₀.mapHomotopyCategory (.up ℤ)).map tG =
            (HomotopyCategory.quotient (ModuleCat.{max v u} B) (.up ℤ)).map
              ((F₀.mapHomologicalComplex (.up ℤ)).map mG) :=
        (congrArg (F₀.mapHomotopyCategory (.up ℤ)).map htG).trans
          (F₀.mapHomotopyCategory_map mG)
      let η : P ⟶ F₀.obj M := adj₀.unit.app P
      let mF := HomologicalComplex.singleMapHomologicalComplex F₀ (.up ℤ) q
      have hchain : ηT ≫ (F₀.mapHomologicalComplex (.up ℤ)).map mG =
          ((CochainComplex.singleFunctor (ModuleCat.{max v u} B) q).map η) ≫
            mF.inv.app M := by
        refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
        by_cases hn : n = q
        · subst n
          change adj₀.unit.app (T.X q) ≫ F₀.map (mG.f q) =
            ((CochainComplex.singleFunctor (ModuleCat.{max v u} B) q).map η).f q ≫
              (mF.inv.app M).f q
          dsimp only [mG, mF, M, T]
          simp only [CochainComplex.singleFunctor]
          rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
            HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
            HomologicalComplex.single_map_f_self]
          simp only [Functor.comp_obj, Functor.id_obj, Functor.map_comp,
            Category.assoc, Iso.inv_hom_id_assoc]
          simp [η, F₀, G₀]
        · simp only [HomologicalComplex.comp_f]
          simp only [Functor.comp_obj, Functor.mapHomologicalComplex_obj_X,
            HomologicalComplex.singleMapHomologicalComplex, NatIso.ofComponents_hom_app,
            Functor.mapHomologicalComplex_map_f, hn, ↓reduceDIte, NatIso.ofComponents_inv_app,
            Limits.comp_zero, T, F₀, G₀, mG, M, η, mF, ηT]
          rw [F₀.map_zero]
          simp
      let φ : T ⟶ J :=
        ((CochainComplex.singleFunctor (ModuleCat.{max v u} B) q).map η) ≫ mF.inv.app M
      have hpath : (homotopyAdjunction adj₀ (.up ℤ)).unit.app U ≫
          (F₀.mapHomotopyCategory (.up ℤ)).map tG =
          (HomotopyCategory.quotient (ModuleCat.{max v u} B) (.up ℤ)).map φ := by
        rw [hunitQ, hmaptG]
        exact ((HomotopyCategory.quotient (ModuleCat.{max v u} B) (.up ℤ)).map_comp ηT
            ((F₀.mapHomologicalComplex (.up ℤ)).map mG)).symm.trans
          (congrArg (HomotopyCategory.quotient (ModuleCat.{max v u} B) (.up ℤ)).map hchain)
      have hnatE : eB.inv.app T ≫ DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (ModuleCat.{max v u} B) (.up ℤ)).map φ) =
          DerivedCategory.Q.map φ ≫ eB.inv.app J := by
        simpa only [Functor.comp_map] using (eB.inv.naturality φ).symm
      have hnatH : (DerivedCategory.homologyFunctorFactors
          (ModuleCat.{max v u} B) q).inv.app T ≫ H.map (DerivedCategory.Q.map φ) =
          HomologicalComplex.homologyMap φ q ≫
            (DerivedCategory.homologyFunctorFactors
              (ModuleCat.{max v u} B) q).inv.app J :=
        ((DerivedCategory.homologyFunctorFactors
          (ModuleCat.{max v u} B) q).inv.naturality φ).symm
      have hnatS : (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) q P).inv ≫
          HomologicalComplex.homologyMap
            ((CochainComplex.singleFunctor (ModuleCat.{max v u} B) q).map η) q =
          η ≫ (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) q (F₀.obj M)).inv := by
        simpa only [CochainComplex.singleFunctor, CochainComplex.singleFunctors]
          using HomologicalComplex.singleObjHomologySelfIso_inv_naturality (.up ℤ) q η
      have hnatH' : (DerivedCategory.homologyFunctorFactors
            (ModuleCat.{max v u} B) q).inv.app T ≫
          H.map (DerivedCategory.Q.map φ) ≫ H.map (eB.inv.app J) =
          HomologicalComplex.homologyMap φ q ≫
            (DerivedCategory.homologyFunctorFactors (ModuleCat.{max v u} B) q).inv.app J ≫
            H.map (eB.inv.app J) := by
        refine Eq.trans (Category.assoc _ _ _).symm (Eq.trans ?_ (Category.assoc _ _ _))
        exact congrArg (fun z => z ≫ H.map (eB.inv.app J)) hnatH
      have hδF : (F₀.mapHomotopyCategoryFactors (.up ℤ)).inv.app Ta = 𝟙 _ := rfl
      have hδFmap : H.map (DerivedCategory.Qh.map
          ((F₀.mapHomotopyCategoryFactors (.up ℤ)).inv.app Ta)) = 𝟙 _ := by
        refine Eq.trans (congrArg (fun z => H.map (DerivedCategory.Qh.map z)) hδF) ?_
        exact (congrArg H.map (DerivedCategory.Qh.map_id _)).trans (H.map_id _)
      refine Eq.trans (b := (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) q P).inv ≫
              (DerivedCategory.homologyFunctorFactors (ModuleCat.{max v u} B) q).inv.app T ≫
              H.map (eB.inv.app T ≫ DerivedCategory.Qh.map
                ((homotopyAdjunction adj₀ (.up ℤ)).unit.app U ≫
                  (F₀.mapHomotopyCategory (.up ℤ)).map tG))) ?_
        (Eq.trans (b := (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) q P).inv ≫
              (DerivedCategory.homologyFunctorFactors (ModuleCat.{max v u} B) q).inv.app T ≫
              H.map (eB.inv.app T ≫ DerivedCategory.Qh.map
                ((HomotopyCategory.quotient (ModuleCat.{max v u} B) (.up ℤ)).map φ))) ?_
          (Eq.trans (b := (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) q P).inv ≫
              HomologicalComplex.homologyMap φ q ≫
              (DerivedCategory.homologyFunctorFactors (ModuleCat.{max v u} B) q).inv.app J ≫
              H.map (eB.inv.app J)) ?_ ?_))
      · dsimp only [adj₀]
        simp only [Functor.map_comp]
      · rw [hpath]
      · rw [hnatE, H.map_comp]
        exact congrArg (fun t =>
          (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) q P).inv ≫ t) hnatH'
      · dsimp only [φ]
        rw [HomologicalComplex.homologyMap_comp]
        simp only [← Category.assoc]
        rw [hnatS]
        rw [hδFmap]
        dsimp only [η, mF, adj₀]
        exact (Category.comp_id _).symm
    have hsingle : (DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat.{max v u} B) q).inv.app P =
        (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) q P).inv ≫
          (DerivedCategory.homologyFunctorFactors (ModuleCat.{max v u} B) q).inv.app T :=
      singleFunctorCompHomologyFunctorIso_inv_app P q
    rw [htotal, hsingle]
    have hσ : σ.hom.app P = 𝟙 _ := rfl
    have hσA : ((DerivedCategory.singleFunctorIsoCompQ
      (ModuleCat.{max v u} A) q).inv.app M) = 𝟙 _ := rfl
    rw [hσ, hσA]
    simp only [Category.id_comp, Functor.map_comp]
    dsimp only [F₀] at hsource
    have hjoined := congrArg (fun t =>
      t ≫ H.map (α.app V) ≫ H.map (RF.map (eA.hom.app Ta)) ≫
        H.map (RF.map (𝟙 ((CochainComplex.singleFunctor
          (ModuleCat.{max v u} A) q ⋙ DerivedCategory.Q).obj M)))) hsource
    let mid := ((ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f).unit.app P ≫
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) q (F₀.obj M)).inv ≫
      HomologicalComplex.homologyMap
        ((HomologicalComplex.singleMapHomologicalComplex F₀ (.up ℤ) q).inv.app M) q ≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{max v u} B) q).inv.app J ≫
      H.map (eB.inv.app J) ≫
      H.map (DerivedCategory.Qh.map
        ((F₀.mapHomotopyCategoryFactors (.up ℤ)).inv.app Ta))) ≫
      H.map (α.app V) ≫ H.map (RF.map (eA.hom.app Ta)) ≫
      H.map (RF.map (𝟙 ((CochainComplex.singleFunctor
        (ModuleCat.{max v u} A) q ⋙ DerivedCategory.Q).obj M)))
    have hId : H.map (RF.map (𝟙 ((CochainComplex.singleFunctor
        (ModuleCat.{max v u} A) q ⋙ DerivedCategory.Q).obj M))) = 𝟙 _ := by simp
    refine Eq.trans (b := mid) ?_ ?_
    · simp only [mid, Functor.id_obj, Functor.comp_obj,
        CochainComplex.singleFunctor,
        Category.assoc]
      exact Eq.trans (Category.assoc _ _ _) hjoined
    · dsimp only [mid]
      rw [hId]
      dsimp only [F₀, J, V, Ta, eA, eB]
      simp [coextendSingleUnit, Functor.map_comp, Category.assoc]
      rfl
  exact congrArg (fun g : P ⟶ H.obj (RF.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q).obj M)) =>
      g (ULift.up 1)) heq

/-- The additive identification and the normalized map agree. -/
private theorem extHomologyAddEquiv_eq_extToHomology
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ))]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (q : ℤ)
    (h : DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of B (ULift.{v} B)))) K q) :
    extHomologyAddEquiv f RF α K q h = extToHomology f RF α K q h := by
  dsimp [extToHomology]
  rw [← coextendSingleUnit_eq_derivedAdjunctionUnit f RF α q]
  dsimp [extHomologyAddEquiv, freeHomologyLinearEquiv,
    freeHomologyLinearMap]
  let shiftFF := Functor.FullyFaithful.ofFullyFaithful
    (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) q)
  have hpre (t : (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) q).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q).obj
          ((ModuleCat.restrictScalars f).obj (ModuleCat.of B (ULift.{v} B)))) ⟶
        (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) q).obj K) :
      (AddEquiv.ofBijective
        (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) q).mapAddHom
        ⟨fun x y h => shiftFF.map_injective h,
          fun z => shiftFF.map_surjective z⟩).symm t = shiftFF.preimage t :=
    (AddEquiv.symm_apply_eq _).2 (shiftFF.map_preimage t).symm
  simp [hpre, LinearEquiv.ofBijective, Adjunction.homEquiv_apply,
    CategoryTheory.Linear.homCongr_apply, Functor.map_comp]
  rfl

/-- The normalized map is natural in the derived argument. -/
private theorem extToHomology_naturality {K L : DerivedCategory (ModuleCat.{max v u} A)}
    (k : K ⟶ L) (q : ℤ)
    (h : DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of B (ULift.{v} B)))) K q) :
    extToHomology f RF α L q (h ≫ (shiftFunctor _ q).map k) =
      (ModuleCat.restrictScalars f).map
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).map (RF.map k))
        (extToHomology f RF α K q h) := by
  dsimp [extToHomology]
  let M : ModuleCat.{max v u} A :=
    (ModuleCat.restrictScalars f).obj (ModuleCat.of B (ULift.{v} B))
  let e := (DerivedCategory.singleFunctors (ModuleCat.{max v u} A)).shiftIso q 0 q (by simp)
  let shiftFF := Functor.FullyFaithful.ofFullyFaithful
    (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) q)
  change (ModuleCat.restrictScalars f).map
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).map
        (RF.map (shiftFF.preimage (e.hom.app M ≫ (h ≫ (shiftFunctor _ q).map k))))) _ = _
  have hg : shiftFF.preimage (e.hom.app M ≫ (h ≫ (shiftFunctor _ q).map k)) =
      shiftFF.preimage (e.hom.app M ≫ h) ≫ k := by
    apply shiftFF.map_injective
    simp only [Functor.map_comp, shiftFF.map_preimage]
    simp [Category.assoc]
  rw [hg, Functor.map_comp, Functor.map_comp]
  rfl

/-- The normalized map sends the class of a morphism out of `B[-q]` to the image of the derived
unit under that morphism. -/
private theorem extToHomology_unit
    (K : DerivedCategory (ModuleCat.{max v u} A)) (q : ℤ)
    (g : (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q).obj
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of B (ULift.{v} B))) ⟶ K) :
    extToHomology f RF α K q
      (((DerivedCategory.singleFunctors (ModuleCat.{max v u} A)).shiftIso q 0 q
        (by simp)).inv.app _ ≫ (shiftFunctor _ q).map g) =
      (ModuleCat.restrictScalars f).map
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).map (RF.map g))
        (coextendSingleUnit f RF α _ q
          (((ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f).unit.app
            (ModuleCat.of B (ULift.{v} B))) (ULift.up 1))) := by
  dsimp [extToHomology]
  let M : ModuleCat.{max v u} A :=
    (ModuleCat.restrictScalars f).obj (ModuleCat.of B (ULift.{v} B))
  let e := (DerivedCategory.singleFunctors (ModuleCat.{max v u} A)).shiftIso q 0 q (by simp)
  let shiftFF := Functor.FullyFaithful.ofFullyFaithful
    (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) q)
  have hg :
      shiftFF.preimage (e.hom.app M ≫ (e.inv.app M ≫ (shiftFunctor _ q).map g)) = g := by
    apply shiftFF.map_injective
    simp
  rw [hg]

/-- The normalized map from Ext to cohomology, as an `A`-linear map. -/
private noncomputable def extToHomologyLinearMap
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ))]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (q : ℤ) :
    DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of B (ULift.{v} B)))) K q →ₗ[A]
      ((ModuleCat.restrictScalars f).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).obj (RF.obj K))) where
  toFun := extToHomology f RF α K q
  map_add' h k := by
    rw [← extHomologyAddEquiv_eq_extToHomology f RF α K q (h + k),
      ← extHomologyAddEquiv_eq_extToHomology f RF α K q h,
      ← extHomologyAddEquiv_eq_extToHomology f RF α K q k]
    exact map_add (extHomologyAddEquiv f RF α K q) h k
  map_smul' r h := by
    have hscalar : r • h = h ≫
        (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) q).map (r • 𝟙 K) := by
      rw [Functor.map_smul]
      simp
    rw [hscalar, extToHomology_naturality, derivedCoextendScalars_map_smul f RF α r (𝟙 K)]
    let : Functor.Linear B
        (DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q) :=
      DerivedCategory.homologyFunctor_linear (C := ModuleCat.{max v u} B) B q
    simp
    rfl

/-- The cohomology of a derived coextension functor admits a natural, normalized
identification with Ext. -/
theorem homologyExtComparison_nonempty
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ))] :
    Nonempty (HomologyExtComparison f RF α) := by
  let e (K : DerivedCategory (ModuleCat.{max v u} A)) (q : ℤ) :=
    LinearEquiv.ofBijective (extToHomologyLinearMap f RF α K q)
      (by
        refine ⟨fun x y hxy => ?_, fun y => ?_⟩
        · apply (extHomologyAddEquiv f RF α K q).injective
          change extToHomology f RF α K q x = extToHomology f RF α K q y at hxy
          rw [extHomologyAddEquiv_eq_extToHomology,
            extHomologyAddEquiv_eq_extToHomology]
          simpa [ModuleCat.restrictScalars, ModuleCat.RestrictScalars.obj',
            extToHomologyLinearMap] using hxy
        · obtain ⟨x, hx⟩ := (extHomologyAddEquiv f RF α K q).surjective y
          exact ⟨x, by
            change extToHomology f RF α K q x = y
            rw [← extHomologyAddEquiv_eq_extToHomology f RF α K q x]
            simpa [ModuleCat.restrictScalars, ModuleCat.RestrictScalars.obj'] using hx⟩)
  refine ⟨{
    linearEquiv := fun K q => (e K q).symm
    naturality := ?_
    unit_app := ?_ }⟩
  · intro K L g q x
    apply (e L q).injective
    let y : ((ModuleCat.restrictScalars f).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).obj (RF.obj L))) :=
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).map (RF.map g)) x
    change (e L q) ((e L q).symm y) =
      (e L q) ((e K q).symm x ≫ (shiftFunctor _ q).map g)
    rw [(e L q).apply_symm_apply]
    change y = extToHomology f RF α L q
      ((e K q).symm x ≫ (shiftFunctor _ q).map g)
    rw [extToHomology_naturality]
    rw [show extToHomology f RF α K q ((e K q).symm x) = x from (e K q).apply_symm_apply x]
    rfl
  · intro K q g
    apply (e K q).injective
    let y : ((ModuleCat.restrictScalars f).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).obj (RF.obj K))) :=
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).map (RF.map g))
        ((coextendSingleUnit f RF α _ q)
          (((ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f).unit.app
            (ModuleCat.of B (ULift.{v} B))) (ULift.up 1)))
    change (e K q) ((e K q).symm y) = (e K q)
      ((((DerivedCategory.singleFunctors (ModuleCat.{max v u} A)).shiftIso q 0 q
        (by simp)).inv.app _) ≫ (shiftFunctor _ q).map g)
    rw [(e K q).apply_symm_apply]
    change y = extToHomology f RF α K q
      ((((DerivedCategory.singleFunctors (ModuleCat.{max v u} A)).shiftIso q 0 q
        (by simp)).inv.app _) ≫ (shiftFunctor _ q).map g)
    exact (extToHomology_unit f RF α K q g).symm

/-- The cohomology of derived coextension is Ext, naturally and compatibly with the derived
unit (and hence with the restriction comparison).

Derived coextension enters as an arbitrary right derived functor presented by its universal
property, so the statement is independent of the model chosen for it. That data is discharged by
`Dualizing.AnyModel.derivedHom` with `Dualizing.AnyModel.derivedHomUnit`, giving the
unconditional `Dualizing.derivedHomHomologyLinearEquivExt`. -/
@[stacks 0A71 "cohomology as Ext, for an arbitrary right derived functor RF of coextension of \
scalars; the data RF, alpha is discharged by AnyModel.derivedHom with AnyModel.derivedHomUnit, \
giving the unconditional derivedHomHomologyLinearEquivExt"]
def derivedCoextendScalarsHomologyLinearEquivExt
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ))] :
    HomologyExtComparison f RF α :=
  Classical.choice (homologyExtComparison_nonempty f RF α)

end

end Dualizing
