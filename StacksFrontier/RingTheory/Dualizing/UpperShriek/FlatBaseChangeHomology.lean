module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactDerivedHomologyComposition
public import StacksFrontier.Algebra.Homology.TricomplexHomology
public import StacksFrontier.Homology.DerivedComplete.CompleteAdic
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.CompositionGeneral

/-!
# A cohomological criterion for morphisms out of a flat base change

Let `g : R → S` be a flat homomorphism of commutative rings, `X` an object of `D(R)` and `V` an
object of `D(S)`.  A morphism `f : X ⊗_R^L S ⟶ V` is determined by its transpose
`t : X ⟶ V|_R`, and on cohomology `H^n(f)` is the `S`-linear extension of `H^n(t)`: the
cohomology of `X ⊗_R^L S` is `H^n(X) ⊗_R S`.  Consequently two such morphisms `f₁, f₂` whose
transposes differ by an automorphism `θ` of `V|_R`, `t₁ = t₂ ≫ θ`, have the same invertibility as
soon as `θ` commutes with multiplication by every element of `S`: on cohomology `θ` is then an
`S`-linear automorphism, even though `θ` itself need not be the restriction of a morphism of
`D(S)`.

## Main results

* `Dualizing.FlatHomology.homology_map_adj_counit` — the counit of the derived
  extension–restriction adjunction along a flat map induces, on cohomology, the counit of the
  module adjunction.
* `Dualizing.FlatHomology.isIso_of_homEquiv_eq_comp` — the cohomological criterion.
* `Dualizing.FlatHomology.derivedHom_map_smul_id` and
  `Dualizing.FlatHomology.restrictScalars_mapDerivedCategory_map_smul_id` — derived
  coextension and derived restriction of scalars along `f` carry multiplication by `a` to
  multiplication by `f a`, and multiplication by `f a` to multiplication by `a`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Dualizing.FlatHomology

noncomputable section

section ShortComplex

variable {C : Type*} [Category* C] [Abelian C] (S : ShortComplex C)

/-- The homology comparison for the identity functor is the identity. -/
theorem mapHomologyIso_id_hom :
    (S.mapHomologyIso (𝟭 C)).hom = 𝟙 _ := by
  let d : ShortComplex.LeftHomologyMapData (𝟙 S) S.homologyData.left
      (S.homologyData.left.map (𝟭 C)) :=
    { φK := 𝟙 _
      φH := 𝟙 _
      commi := (Category.id_comp _).trans (Category.comp_id _).symm
      commf' := by
        rw [ShortComplex.LeftHomologyData.map_f']
        exact (Category.comp_id _).trans (Category.id_comp _).symm
      commπ := (Category.comp_id _).trans (Category.id_comp _).symm }
  have hcomm := d.homologyMap_comm
  rw [ShortComplex.homologyMap_id, Category.id_comp,
    show S.homologyData.left.homologyIso.hom = 𝟙 _ from
      CategoryTheory.Iso.inv_hom_id S.homologyData.left.leftHomologyIso] at hcomm
  exact hcomm.trans (Category.id_comp _)

end ShortComplex

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

section Core

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) (G : D ⥤ C) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- On homology of complexes, a natural transformation `G ⋙ F ⟶ 𝟭` between exact functors is
read through the two homology comparisons. -/
theorem homologyMap_mapHomologicalComplex_counit (ε : G ⋙ F ⟶ 𝟭 D) {ι : Type*}
    (c : ComplexShape ι) (K : HomologicalComplex D c) (n : ι) :
    HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex ε c).app K) n =
      (Stacks.DerivedFunctor.complexHomologyIso F c n).hom.app ((G.mapHomologicalComplex c).obj K) ≫
        F.map ((Stacks.DerivedFunctor.complexHomologyIso G c n).hom.app K) ≫
          ε.app (K.homology n) := by
  have h1 := Stacks.DerivedFunctor.complexHomologyIso_comp_hom_app c n G F K
  have h3 := Stacks.DerivedFunctor.complexHomologyIso_hom_app c n (G ⋙ F) K
  have h2 := HomologicalComplex.mapHomologyIso_hom_naturality_natTrans ε K n
  have h4 := congrArg (fun t => t ≫ ε.app (K.homology n)) (h3.symm.trans h1.symm)
  exact (Category.comp_id _).symm.trans ((congrArg (fun t =>
    HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex ε c).app K) n ≫ t)
    (mapHomologyIso_id_hom (K.sc n)).symm).trans (h2.trans (h4.trans (Category.assoc _ _ _))))

end Core

section Linear

/-- A linear functor carries multiplication by `r` on `X` to multiplication by `r`. -/
private theorem functor_map_smul_id {R : Type*} [CommRing R] {C D : Type*} [Category* C]
    [Category* D] [Preadditive C] [Preadditive D] [Linear R C] [Linear R D] (F : C ⥤ D)
    [F.Additive] [F.Linear R] (r : R) (X : C) : F.map (r • 𝟙 X) = r • 𝟙 (F.obj X) := by
  rw [Functor.map_smul, F.map_id]

/-- The homology functor on cochain complexes of `R`-modules is `R`-linear. -/
private theorem homologicalHomologyFunctor_linear {R : Type u} [CommRing R] (i : ℤ) :
    Functor.Linear R
      (HomologicalComplex.homologyFunctor (ModuleCat.{w} R) (ComplexShape.up ℤ) i) where
  map_smul f r := by
    show ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{w} R) (ComplexShape.up ℤ) i).map
        (r • f)) = _
    rw [show (HomologicalComplex.shortComplexFunctor (ModuleCat.{w} R)
      (ComplexShape.up ℤ) i).map (r • f) = r •
        (HomologicalComplex.shortComplexFunctor (ModuleCat.{w} R)
          (ComplexShape.up ℤ) i).map f by rfl]
    apply ShortComplex.homologyMap_smul

attribute [local instance] homologicalHomologyFunctor_linear

/-- The homology functor on `D(R)` is `R`-linear. Alias of `derivedHomologyFunctorLinear`. -/
private alias derivedHomologyFunctor_linear := derivedHomologyFunctorLinear

/-- On cohomology, multiplication by `s` on an object of `D(S)` is multiplication by `s`. -/
theorem homology_map_smul_id {S : Type u} [CommRing S] (i : ℤ) (s : S)
    (V : DerivedCategory (ModuleCat.{w} S)) :
    (DerivedCategory.homologyFunctor (ModuleCat.{w} S) i).map (s • 𝟙 V) = s • 𝟙 _ := by
  let := derivedHomologyFunctor_linear (R := S) i
  exact functor_map_smul_id _ s V

section ScalarAction

universe uA uB

variable {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] (f : A →+* B)

/-- Coextension of scalars is additive. -/
local instance coextendScalarsAdditive {S : Type uA} {T : Type uB} [CommRing S] [CommRing T]
    (f : S →+* T) : (ModuleCat.coextendScalars.{uA, uB, max v uA uB} f).Additive where
  map_add := by intros; ext; rfl

/-- Coextension of scalars carries multiplication by `a` to multiplication by `f a`. -/
theorem coextendScalars_map_smul_id (a : A) (M : ModuleCat.{max v uA uB} A) :
    (ModuleCat.coextendScalars.{uA, uB, max v uA uB} f).map (a • 𝟙 M) = f a • 𝟙 _ := by
  ext φ x
  let x' : B := x
  show a • φ x = φ (x' * f a)
  rw [mul_comm]
  exact (φ.map_smul a x).symm

/-- Restriction of scalars carries multiplication by `f a` to multiplication by `a`. -/
theorem restrictScalars_map_smul_id (a : A) (M : ModuleCat.{max v uA uB} B) :
    (ModuleCat.restrictScalars.{max v uA uB} f).map (f a • 𝟙 M) = a • 𝟙 _ := rfl

/-- Derived coextension of scalars carries multiplication by `a` to multiplication by `f a`. -/
theorem derivedHom_map_smul_id (a : A)
    (Y : DerivedCategory (ModuleCat.{max v uA uB} A)) :
    (derivedHom.{uA, v, uB} f).map (a • 𝟙 Y) = f a • 𝟙 _ := by
  have := coextendScalars_hasPointwiseRightDerivedFunctor.{uA, v, uB} f
  let W := HomotopyCategory.quasiIso (ModuleCat.{max v uA uB} A) (.up ℤ)
  have : (derivedHom.{uA, v, uB} f).IsRightDerivedFunctor (derivedHomComparison.{uA, uB, v} f)
      W := by
    dsimp [derivedHom, derivedHomComparison, W]
    infer_instance
  let I := derivedHom.{uA, v, uB} f
  let γ₁ : I ⟶ I :=
    { app := fun Z => I.map (a • 𝟙 Z)
      naturality := fun Z Z' h => by
        rw [← I.map_comp, ← I.map_comp, Linear.comp_smul, Linear.smul_comp, Category.comp_id,
          Category.id_comp] }
  let γ₂ : I ⟶ I :=
    { app := fun Z => f a • 𝟙 (I.obj Z)
      naturality := fun Z Z' h => by
        rw [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp] }
  have key : γ₁ = γ₂ := by
    refine Functor.rightDerived_ext I (derivedHomComparison.{uA, uB, v} f) W I γ₁ γ₂ ?_
    ext K
    obtain ⟨K₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, γ₁, γ₂]
    have h1 : a • 𝟙 (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K₀)) =
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map (a • 𝟙 K₀)) := by
      rw [functor_map_smul_id _ a, functor_map_smul_id _ a]
    have h2 : ((ModuleCat.coextendScalars.{uA, uB, max v uA uB} f).mapHomologicalComplex
        (.up ℤ)).map (a • 𝟙 K₀) = f a • 𝟙 _ := by
      ext i : 1
      exact coextendScalars_map_smul_id f a (K₀.X i)
    have hn := (derivedHomComparison.{uA, uB, v} f).naturality
      ((HomotopyCategory.quotient _ _).map (a • 𝟙 K₀))
    dsimp only [Functor.comp_map] at hn
    rw [h1, ← hn, Functor.mapHomotopyCategory_map, h2]
    simp only [Functor.map_smul, CategoryTheory.Functor.map_id, Linear.comp_smul]
    rw [Linear.smul_comp]
    congr 1
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  exact congrArg (fun γ : I ⟶ I => γ.app Y) key

/-- Derived restriction of scalars carries multiplication by `f a` to multiplication by `a`. -/
theorem restrictScalars_mapDerivedCategory_map_smul_id (a : A)
    (Z : DerivedCategory (ModuleCat.{max v uA uB} B)) :
    (ModuleCat.restrictScalars.{max v uA uB} f).mapDerivedCategory.map (f a • 𝟙 Z) =
      a • 𝟙 _ := by
  let F := (ModuleCat.restrictScalars.{max v uA uB} f).mapDerivedCategory
  let K := DerivedCategory.Q.objPreimage Z
  let e : DerivedCategory.Q.obj K ≅ Z := DerivedCategory.Q.objObjPreimageIso Z
  have hZ : f a • 𝟙 Z = e.inv ≫ DerivedCategory.Q.map (f a • 𝟙 K) ≫ e.hom := by
    rw [functor_map_smul_id _ (f a), Linear.smul_comp, Linear.comp_smul, Category.id_comp,
      e.inv_hom_id]
  have hK : ((ModuleCat.restrictScalars.{max v uA uB} f).mapHomologicalComplex
      (.up ℤ)).map (f a • 𝟙 K) = a • 𝟙 _ := by
    ext i : 1
    exact restrictScalars_map_smul_id f a (K.X i)
  have hn := (ModuleCat.restrictScalars.{max v uA uB} f).mapDerivedCategoryFactors.hom.naturality
    (f a • 𝟙 K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  have hQK : DerivedCategory.Q.map (f a • 𝟙 K) = f a • 𝟙 (DerivedCategory.Q.obj K) :=
    functor_map_smul_id _ (f a) K
  rw [hK, functor_map_smul_id _ a, hQK, Linear.comp_smul, Category.comp_id] at hn
  have h4 : F.map (f a • 𝟙 (DerivedCategory.Q.obj K)) = a • 𝟙 _ := by
    rw [← cancel_mono ((ModuleCat.restrictScalars.{max v uA uB} f).mapDerivedCategoryFactors.hom.app
      K), hn, Linear.smul_comp, Category.id_comp]
  rw [hZ, hQK, F.map_comp, F.map_comp, h4, Linear.smul_comp, Linear.comp_smul, Category.id_comp,
    ← F.map_comp, e.inv_hom_id, F.map_id]

end ScalarAction

end Linear

section Flat

variable {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S)

/-- Extension of scalars along `g`. -/
abbrev E : ModuleCat.{max v u} R ⥤ ModuleCat.{max v u} S :=
  ModuleCat.extendScalars.{u, u, max v u} g

/-- Extension of scalars is a left adjoint. -/
instance : (E.{u, v} g).IsLeftAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{max v u, u, u} g).isLeftAdjoint

/-- Extension of scalars is additive. -/
instance : (E.{u, v} g).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{max v u, u, u} g).left_adjoint_additive

/-- Restriction of scalars along `g`. -/
abbrev Rs : ModuleCat.{max v u} S ⥤ ModuleCat.{max v u} R := ModuleCat.restrictScalars.{max v u} g

variable [PreservesFiniteLimits (E.{u, v} g)]

/-- `(E g).mapDerivedCategory` is a left derived functor of extension of scalars along `g`. -/
instance : (E.{u, v} g).mapDerivedCategory.IsLeftDerivedFunctor
    (E.{u, v} g).mapDerivedCategoryFactors.hom
    (HomologicalComplex.quasiIso (ModuleCat.{max v u} R) (ComplexShape.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _ (E g).mapDerivedCategoryFactors

/-- The adjunction between derived extension of scalars `(E g).mapDerivedCategory` and derived
restriction of scalars along `g`. -/
abbrev adj : (E.{u, v} g).mapDerivedCategory ⊣ (Rs.{u, v} g).mapDerivedCategory :=
  CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, v} g
    (E g).mapDerivedCategory (E g).mapDerivedCategoryFactors.hom

/-- **Cohomology of the counit of the derived extension–restriction adjunction.**  Along a flat
map, the counit `(V|_R) ⊗_R^L S ⟶ V` induces on cohomology the counit of the module adjunction,
read through the two comparisons of cohomology with the exact functors. -/
theorem homology_map_adj_counit (n : ℤ) (V : DerivedCategory (ModuleCat.{max v u} S)) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max v u} S) n).map ((adj g).counit.app V) =
      (Stacks.DerivedFunctor.derivedHomologyIso (E g) n).hom.app
          ((Rs g).mapDerivedCategory.obj V) ≫
        (E g).map ((Stacks.DerivedFunctor.derivedHomologyIso (Rs g) n).hom.app V) ≫
          (ModuleCat.extendRestrictScalarsAdj.{max v u, u, u} g).counit.app
            ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} S) n).obj V) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max v u} S) n
  let HR := DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) n
  let adj₀ := ModuleCat.extendRestrictScalarsAdj.{max v u, u, u} g
  have key : Functor.whiskerRight (adj g).counit H =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (Rs g).mapDerivedCategory
          (Stacks.DerivedFunctor.derivedHomologyIso (E g) n).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Stacks.DerivedFunctor.derivedHomologyIso (Rs g) n).hom (E g) ≫
        (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft H adj₀.counit := by
    refine Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} S) (ComplexShape.up ℤ)) (fun K => ?_)
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj, Functor.id_obj]
    rw [Category.id_comp, Category.id_comp]
    let W := ((Rs g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
    let f : (Rs g).mapDerivedCategory.obj (DerivedCategory.Q.obj K) ⟶ DerivedCategory.Q.obj W :=
      (Rs g).mapDerivedCategoryFactors.hom.app K
    let κ : ((E g).mapHomologicalComplex (ComplexShape.up ℤ)).obj W ⟶ K :=
      ((ModuleCat.extendRestrictScalarsAdj.{max v u, u, u} g).mapHomologicalComplex
        (ComplexShape.up ℤ)).counit.app K
    let hS := DerivedCategory.homologyFunctorFactors (ModuleCat.{max v u} S) n
    let hRf := DerivedCategory.homologyFunctorFactors (ModuleCat.{max v u} R) n
    let cE : (((E g).mapHomologicalComplex (ComplexShape.up ℤ)).obj W).homology n ⟶
        (E g).obj (W.homology n) :=
      (Stacks.DerivedFunctor.complexHomologyIso (E g) (ComplexShape.up ℤ) n).hom.app W
    let cR : W.homology n ⟶ (Rs g).obj (K.homology n) :=
      (Stacks.DerivedFunctor.complexHomologyIso (Rs g) (ComplexShape.up ℤ) n).hom.app K
    have hc : (adj g).counit.app (DerivedCategory.Q.obj K) =
        (E g).mapDerivedCategory.map f ≫ (E g).mapDerivedCategoryFactors.hom.app W ≫
          DerivedCategory.Q.map κ :=
      CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_counit_app_eq.{u, u,
        v}
        g (E g).mapDerivedCategory (E g).mapDerivedCategoryFactors.hom K
    have hcore : HomologicalComplex.homologyMap κ n = cE ≫ (E g).map cR ≫
        adj₀.counit.app (K.homology n) :=
      homologyMap_mapHomologicalComplex_counit (E g) (Rs g) adj₀.counit (ComplexShape.up ℤ) K n
    have hQ : H.map (DerivedCategory.Q.map κ) =
        hS.hom.app (((E g).mapHomologicalComplex (ComplexShape.up ℤ)).obj W) ≫
          (cE ≫ (E g).map cR ≫ adj₀.counit.app (K.homology n)) ≫ hS.inv.app K := by
      have N := DerivedCategory.homologyFunctorFactors_hom_naturality κ n
      exact ((Iso.eq_comp_inv (hS.app K)).2 (N.trans (congrArg _ hcore))).trans
        (Category.assoc _ _ _)
    have hR : (Stacks.DerivedFunctor.derivedHomologyIso (Rs g) n).hom.app
        (DerivedCategory.Q.obj K) = HR.map f ≫ hRf.hom.app W ≫ cR ≫ (Rs g).map (hS.inv.app K) :=
      Stacks.DerivedFunctor.derivedHomologyIso_hom_app_Q (Rs g) n K
    have hE : (Stacks.DerivedFunctor.derivedHomologyIso (E g) n).hom.app
        (DerivedCategory.Q.obj W) = H.map ((E g).mapDerivedCategoryFactors.hom.app W) ≫
          hS.hom.app (((E g).mapHomologicalComplex (ComplexShape.up ℤ)).obj W) ≫ cE ≫
            (E g).map (hRf.inv.app W) :=
      Stacks.DerivedFunctor.derivedHomologyIso_hom_app_Q (E g) n W
    have hN : (Stacks.DerivedFunctor.derivedHomologyIso (E g) n).hom.app
        ((Rs g).mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫ (E g).map (HR.map f) =
        H.map ((E g).mapDerivedCategory.map f) ≫
          (Stacks.DerivedFunctor.derivedHomologyIso (E g) n).hom.app (DerivedCategory.Q.obj W) :=
      ((Stacks.DerivedFunctor.derivedHomologyIso (E g) n).hom.naturality f).symm
    have hnat : (E g).map ((Rs g).map (hS.inv.app K)) ≫
        adj₀.counit.app (H.obj (DerivedCategory.Q.obj K)) =
        adj₀.counit.app (K.homology n) ≫ hS.inv.app K :=
      adj₀.counit.naturality (hS.inv.app K)
    have hcancel : (E g).map (hRf.inv.app W) ≫ (E g).map (hRf.hom.app W) = 𝟙 _ := by
      rw [← Functor.map_comp, Iso.inv_hom_id_app]
      exact (E g).map_id _
    dsimp only [Functor.comp_obj, Functor.id_obj, HomologicalComplex.homologyFunctor_obj]
      at hc hQ hR hE hN hnat hcancel hcore ⊢
    rw [hc, Functor.map_comp, Functor.map_comp, hQ, hR]
    simp only [Functor.map_comp, Category.assoc, Category.id_comp]
    simp only [reassoc_of% hN, hE, Category.assoc]
    have hnat2 : (E g).map (cR ≫ (Rs g).map (hS.inv.app K)) ≫
        adj₀.counit.app (H.obj (DerivedCategory.Q.obj K)) =
        (E g).map cR ≫ adj₀.counit.app (K.homology n) ≫ hS.inv.app K :=
      (congrArg (fun t => t ≫ adj₀.counit.app (H.obj (DerivedCategory.Q.obj K)))
        ((E g).map_comp cR ((Rs g).map (hS.inv.app K)))).trans
          ((Category.assoc _ _ _).trans (congrArg (fun t => (E g).map cR ≫ t) hnat))
    refine whisker_eq _ (whisker_eq _ (whisker_eq _ ?_))
    refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
    refine whisker_eq cE ?_
    exact (Category.assoc _ _ _).trans (hnat2.symm.trans ((Category.id_comp _).symm.trans
      ((congrArg (fun t => t ≫ _) hcancel.symm).trans (Category.assoc _ _ _))))
  have := NatTrans.congr_app key V
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj,
    Functor.id_obj] at this
  rwa [Category.id_comp, Category.id_comp] at this

/-- A morphism out of a derived extension of scalars, read on cohomology through its transpose:
`H^n(f)` is the base change of `H^n` of the transpose of `f`, followed by the module counit. -/
theorem homology_map_homEquiv_symm (n : ℤ) {X : DerivedCategory (ModuleCat.{max v u} R)}
    {V : DerivedCategory (ModuleCat.{max v u} S)} (t : X ⟶ (Rs g).mapDerivedCategory.obj V) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max v u} S) n).map
        (((adj g).homEquiv _ _).symm t) =
      (Stacks.DerivedFunctor.derivedHomologyIso (E g) n).hom.app X ≫
        (E g).map ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) n).map t ≫
          (Stacks.DerivedFunctor.derivedHomologyIso (Rs g) n).hom.app V) ≫
          (ModuleCat.extendRestrictScalarsAdj.{max v u, u, u} g).counit.app
            ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} S) n).obj V) := by
  rw [Adjunction.homEquiv_counit, Functor.map_comp, homology_map_adj_counit]
  have hN := (Stacks.DerivedFunctor.derivedHomologyIso (E g) n).hom.naturality t
  dsimp only [Functor.comp_map] at hN
  rw [reassoc_of% hN, Functor.map_comp, Category.assoc]

/-- **The cohomological criterion.**  Let `g : R → S` be flat, and let `f₁, f₂ : X ⊗_R^L S ⟶ V`
be morphisms of `D(S)` whose transposes `t₁, t₂ : X ⟶ V|_R` satisfy `t₁ = t₂ ≫ θ` for an
automorphism `θ` of `V|_R` in `D(R)` commuting with multiplication by every `s ∈ S`.  If `f₂` is
an isomorphism, so is `f₁`. -/
theorem isIso_of_homEquiv_eq_comp {X : DerivedCategory (ModuleCat.{max v u} R)}
    {V : DerivedCategory (ModuleCat.{max v u} S)} (f₁ f₂ : (E g).mapDerivedCategory.obj X ⟶ V)
    (θ : (Rs g).mapDerivedCategory.obj V ⟶ (Rs g).mapDerivedCategory.obj V)
    (hθ : ∀ s : S, (Rs g).mapDerivedCategory.map (s • 𝟙 V) ≫ θ =
      θ ≫ (Rs g).mapDerivedCategory.map (s • 𝟙 V))
    (h : (adj g).homEquiv _ _ f₁ = (adj g).homEquiv _ _ f₂ ≫ θ) [IsIso f₂] [IsIso θ] :
    IsIso f₁ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max v u} S) n
  let HR := DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) n
  let e : HR.obj ((Rs g).mapDerivedCategory.obj V) ≅ (Rs g).obj (H.obj V) :=
    (Stacks.DerivedFunctor.derivedHomologyIso (Rs g) n).app V
  let φ : (Rs g).obj (H.obj V) ⟶ (Rs g).obj (H.obj V) := e.inv ≫ HR.map θ ≫ e.hom
  have hφ : ∀ (s : S) (x : H.obj V), φ (s • x) = s • φ x := by
    intro s x
    let m := HR.map ((Rs g).mapDerivedCategory.map (s • 𝟙 V))
    let μ := (Rs g).map (s • 𝟙 (H.obj V))
    have h1 : m ≫ HR.map θ = HR.map θ ≫ m := by
      simp only [m, ← Functor.map_comp, hθ s]
    have hn : m ≫ e.hom = e.hom ≫ μ := by
      have hn0 := (Stacks.DerivedFunctor.derivedHomologyIso (Rs g) n).hom.naturality (s • 𝟙 V)
      dsimp only [Functor.comp_map] at hn0
      rwa [homology_map_smul_id] at hn0
    have hn' : e.inv ≫ m = μ ≫ e.inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    have h2 : φ ≫ μ = μ ≫ φ := by
      simp only [φ, Category.assoc, ← hn, ← reassoc_of% h1, reassoc_of% hn']
    exact (congrArg (fun m => m.hom x) h2).symm
  let φ' : H.obj V ⟶ H.obj V := ModuleCat.ofHom
    { toFun := fun x => φ x
      map_add' := fun x y => φ.hom.map_add x y
      map_smul' := hφ }
  have hφφ' : (Rs g).map φ' = φ := rfl
  have hiso : IsIso φ' := by
    have : IsIso φ := by simp only [φ]; infer_instance
    rwa [ConcreteCategory.isIso_iff_bijective] at this ⊢
  have hf₁ : f₁ = ((adj g).homEquiv _ _).symm ((adj g).homEquiv _ _ f₂ ≫ θ) := by
    rw [← h, Equiv.symm_apply_apply]
  have key : H.map f₁ = H.map f₂ ≫ φ' := by
    conv_rhs => rw [← ((adj g).homEquiv _ _).symm_apply_apply f₂]
    rw [hf₁, homology_map_homEquiv_symm, homology_map_homEquiv_symm]
    have hθe : HR.map θ ≫ e.hom = e.hom ≫ φ := by
      simp only [φ, Iso.hom_inv_id_assoc]
    have hc := (ModuleCat.extendRestrictScalarsAdj.{max v u, u, u} g).counit.naturality φ'
    dsimp only [Functor.comp_map, Functor.id_map] at hc
    simp only [Functor.map_comp, Category.assoc]
    refine whisker_eq _ (whisker_eq _ ?_)
    show (E g).map (HR.map θ) ≫ (E g).map e.hom ≫ _ = (E g).map e.hom ≫ _ ≫ φ'
    rw [← hc, hφφ', ← Functor.map_comp_assoc, hθe, Functor.map_comp_assoc]
  rw [key]
  infer_instance

end Flat

end

end Dualizing.FlatHomology
