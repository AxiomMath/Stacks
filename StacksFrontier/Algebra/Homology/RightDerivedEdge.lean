module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.CategoryTheory.Abelian.InjectiveResolution.DescHomotopy
public import
  StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.CohomologyOnACofilteredLimit

/-!
# The edge morphism of a composite of right derived functors

Let `P : A ⥤ B` and `Q : B ⥤ D` be additive functors between abelian categories with enough
injectives, and suppose `P` preserves injective objects (for instance because it is the right
adjoint of an exact functor).  There is then a canonical morphism

  `Rⁿ Q (P X) ⟶ Rⁿ (Q ∘ P) X`,

natural in `X`, with *no* exactness hypothesis on `P`.  It is the edge morphism
`E₂^{n,0} ⟶ H^n` of the Grothendieck spectral sequence of the pair `(P, Q)`, and in the
geometric case `P = f_*`, `Q = Γ(Y, -)` it is the pullback map `H^n(Y, f_* F) ⟶ H^n(X, F)` on
sheaf cohomology.

The construction is the comparison theorem for injective resolutions in the asymmetric form: if
`I` is an injective resolution of `X`, then `P` applied to `I` is no longer a resolution of
`P X` (that failure of exactness is exactly what the spectral sequence measures), but it is
still a cochain complex of *injective* objects, so any injective resolution `J` of `P X` admits
a comparison `J ⟶ P I` extending `P` applied to the augmentation of `I`.  Applying `Q` and
taking homology gives the edge morphism; the comparison is unique up to homotopy, which is what
makes the result independent of all choices and natural in `X`.

The two halves of that comparison theorem are already available:
`Stacks.Cohomology.SpectralLimit.descToComplex` builds the comparison, and
`CategoryTheory.InjectiveResolution.homologyMap_mapHomologicalComplex_map_eq` says that two
comparisons agreeing on the augmentation induce the same map on homology after an additive
functor.  This file assembles them into a natural transformation.

## Main definitions

* `Stacks.Cohomology.RightDerivedEdge.resolutionComparison`: the comparison `J ⟶ P I` between
  the chosen injective resolutions.
* `Stacks.Cohomology.RightDerivedEdge.edge`: the edge morphism
  `P ⋙ Q.rightDerived n ⟶ (P ⋙ Q).rightDerived n`.

## Main results

* `Stacks.Cohomology.RightDerivedEdge.edge_app_eq`: *any* augmentation-preserving comparison of
  *any* injective resolutions computes the edge morphism.  This is the characterisation
  consumers use, since it frees them from the globally chosen resolutions.

## Implementation notes

`(P ⋙ Q).mapHomologicalComplex c` and `P.mapHomologicalComplex c ⋙ Q.mapHomologicalComplex c`
agree by definition but not syntactically, and the objects they produce sit in the middle of the
composites below, so neither `Category.assoc` nor `simp` can be applied to those composites as
spelled with `Functor.rightDerived (P ⋙ Q)`.  `isoRightDerivedObjComp` and
`isoRightDerivedObjComp_inv_naturality` are definitional restatements of
`CategoryTheory.InjectiveResolution.isoRightDerivedObj` and its naturality in which the middle
object is spelled as the iterated image, which is the form the rewriting tactics can handle.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Stacks.Cohomology.RightDerivedEdge

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {D : Type u₃} [Category.{v₃} D] [Abelian D]

/-- `P` applied termwise to a cochain complex of injective objects is again a cochain complex of
injective objects, because `P` preserves injective objects. -/
theorem injective_mapHomologicalComplex_obj (P : A ⥤ B) [P.Additive]
    [P.PreservesInjectiveObjects] (K : CochainComplex A ℕ) (hK : ∀ n, Injective (K.X n)) (n : ℕ) :
    Injective (((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).X n) :=
  P.injective_obj_of_injective (hK n)

omit [Abelian A] [Abelian B] in
/-- A functor sends a commuting square to a commuting square.  Stated over variable objects, so
that `rw` can be used in its proof: at the concrete objects of interest the two spellings of a
source involve `CochainComplex.single₀`, across which `rw` cannot see. -/
theorem map_comp_eq_map_comp (P : A ⥤ B) {W X Y Z : A} (a : W ⟶ X) (b : X ⟶ Z) (c : W ⟶ Y)
    (d : Y ⟶ Z) (h : a ≫ b = c ≫ d) :
    P.map a ≫ P.map b = P.map c ≫ P.map d := by
  rw [← P.map_comp, ← P.map_comp, h]

omit [Abelian A] [Abelian B] in
/-- The augmentation chase behind the edge morphism: from `i ≫ a = u ≫ j`, `j ≫ r = m`,
`i ≫ c = k` and `k ≫ e = u ≫ m` one gets `i ≫ a ≫ r = i ≫ c ≫ e`.  Stated over variable
objects and morphisms, because at the concrete data of interest several of these composites are
only definitionally type-correct (their middle objects are the degree-zero terms of single
complexes) and the rewriting tactics cannot be applied to them, while this statement can be
applied by `exact`. -/
theorem comp_aug_eq {W V V' U T₀ T₁ : B} (i : W ⟶ V) (a : V ⟶ V') (u : W ⟶ U) (j : U ⟶ V')
    (r : V' ⟶ T₁) (m : U ⟶ T₁) (c : V ⟶ T₀) (k : W ⟶ T₀) (e : T₀ ⟶ T₁)
    (ha : i ≫ a = u ≫ j) (hj : j ≫ r = m) (hc : i ≫ c = k) (hk : k ≫ e = u ≫ m) :
    i ≫ a ≫ r = i ≫ c ≫ e := by
  rw [← Category.assoc, ha, Category.assoc, hj, ← Category.assoc, hc, hk]

omit [Abelian A] [Abelian B] in
/-- The variant of `comp_aug_eq` in which `u` is an identity, so does not appear. -/
theorem comp_aug_eq' {W V V' T₀ T₁ : B} (i : W ⟶ V) (a : V ⟶ V') (j : W ⟶ V') (r : V' ⟶ T₁)
    (m : W ⟶ T₁) (c : V ⟶ T₀) (k : W ⟶ T₀) (e : T₀ ⟶ T₁)
    (ha : i ≫ a = j) (hj : j ≫ r = m) (hc : i ≫ c = k) (hk : k ≫ e = m) :
    i ≫ a ≫ r = i ≫ c ≫ e := by
  rw [← Category.assoc, ha, hj, ← Category.assoc, hc, hk]

omit [Abelian A] [Abelian B] in
/-- A functor sends a commuting triangle to a commuting triangle. -/
theorem map_comp_eq_map (P : A ⥤ B) {W X Z : A} (a : W ⟶ X) (b : X ⟶ Z) (d : W ⟶ Z)
    (h : a ≫ b = d) : P.map a ≫ P.map b = P.map d := by
  rw [← P.map_comp, h]

/-- `CategoryTheory.InjectiveResolution.desc_commutes_zero` for the identity morphism, with the
identity cancelled.  The primed restatement is needed because at the identity the composite
`𝟙 Z ≫ I.ι.f 0` is only definitionally type-correct, so `Category.id_comp` cannot be used by
`rw` at the point of application. -/
theorem ι_f_zero_comp_desc_id {C : Type*} [Category C] [Abelian C] {Z : C}
    (I J : InjectiveResolution Z) :
    J.ι.f 0 ≫ (InjectiveResolution.desc (𝟙 Z) I J).f 0 = I.ι.f 0 := by
  rw [InjectiveResolution.desc_commutes_zero]
  exact Category.id_comp _

/-- `P` applied to the augmentation of an injective resolution is killed by the first
differential of `P` applied to that resolution. -/
theorem map_ι_f_zero_comp_d (P : A ⥤ B) [P.Additive] {X : A} (I : InjectiveResolution X) :
    P.map (I.ι.f 0) ≫
        ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).d 0 1 = 0 :=
  calc P.map (I.ι.f 0) ≫
        ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).d 0 1
      = P.map (I.ι.f 0 ≫ I.cocomplex.d 0 1) := (P.map_comp _ _).symm
    _ = P.map 0 := congrArg (fun t => P.map t) I.ι_f_zero_comp_complex_d
    _ = 0 := P.map_zero _ _

/-- Two comparisons from an injective resolution of `Z` into a cochain complex of injective
objects which agree on the augmentation induce the same map on the homology of the image under
`Q`.  This is `CategoryTheory.InjectiveResolution.homologyMap_mapHomologicalComplex_map_eq` with
the injectivity of the target supplied as an ordinary argument and the hypothesis checked in
degree zero. -/
theorem homologyMap_map_eq_of_aug (Q : B ⥤ D) [Q.Additive] {Z : B} (J : InjectiveResolution Z)
    {K : CochainComplex B ℕ} (hK : ∀ n, Injective (K.X n)) (g h : J.cocomplex ⟶ K)
    (w : J.ι.f 0 ≫ g.f 0 = J.ι.f 0 ≫ h.f 0) (n : ℕ) :
    HomologicalComplex.homologyMap ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map g) n =
      HomologicalComplex.homologyMap ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map h) n :=
  have := hK
  InjectiveResolution.homologyMap_mapHomologicalComplex_map_eq Q g h
    (InjectiveResolution.ι_comp_ext g h w) n

section

variable [HasInjectiveResolutions A] [HasInjectiveResolutions B]
  (P : A ⥤ B) [P.Additive] [P.PreservesInjectiveObjects]

/-- The comparison of resolutions underlying the edge morphism: the chosen injective resolution
of `P X` maps to `P` applied to the chosen injective resolution of `X`, compatibly with the two
augmentations. -/
def resolutionComparison (X : A) :
    (injectiveResolution (P.obj X)).cocomplex ⟶
      (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution X).cocomplex :=
  SpectralLimit.descToComplex (injectiveResolution (P.obj X)) _
    (injective_mapHomologicalComplex_obj P _ (injectiveResolution X).injective)
    (P.map ((injectiveResolution X).ι.f 0)) (map_ι_f_zero_comp_d P (injectiveResolution X))

/-- The comparison `resolutionComparison` extends the augmentation of the chosen resolution of
`P X` along `P` applied to the augmentation of the chosen resolution of `X`. -/
@[reassoc]
theorem ι_f_zero_comp_resolutionComparison (X : A) :
    (injectiveResolution (P.obj X)).ι.f 0 ≫ (resolutionComparison P X).f 0 =
      P.map ((injectiveResolution X).ι.f 0) :=
  SpectralLimit.ι_comp_descToComplex _ _ _ _ _

variable (Q : B ⥤ D) [Q.Additive]

/-- `CategoryTheory.InjectiveResolution.isoRightDerivedObj` for the composite `P ⋙ Q`, with the
target complex spelled as `Q` applied to `P` applied to the resolution.  This is the same
morphism, retyped: the two spellings of the complex are definitionally equal, but only this one
can be matched against the image of a comparison of complexes. -/
def isoRightDerivedObjComp {X : A} (I : InjectiveResolution X) (n : ℕ) :
    ((P ⋙ Q).rightDerived n).obj X ≅
      (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).obj
        ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)) :=
  I.isoRightDerivedObj (P ⋙ Q) n

omit [HasInjectiveResolutions B] [P.PreservesInjectiveObjects] in
/-- `CategoryTheory.InjectiveResolution.isoRightDerivedObj_inv_naturality` in the spelling of
`isoRightDerivedObjComp`. -/
@[reassoc]
theorem isoRightDerivedObjComp_inv_naturality {X Y : A} (g : X ⟶ Y) (I : InjectiveResolution X)
    (J : InjectiveResolution Y) (φ : I.cocomplex ⟶ J.cocomplex)
    (comm : I.ι.f 0 ≫ φ.f 0 = g ≫ J.ι.f 0) (n : ℕ) :
    (isoRightDerivedObjComp P Q I n).inv ≫ ((P ⋙ Q).rightDerived n).map g =
      (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).map
          ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map
            ((P.mapHomologicalComplex (ComplexShape.up ℕ)).map φ)) ≫
        (isoRightDerivedObjComp P Q J n).inv :=
  InjectiveResolution.isoRightDerivedObj_inv_naturality g I J φ comm (P ⋙ Q) n

/-- **The edge morphism of a composite of right derived functors.**  For additive functors
`P : A ⥤ B` and `Q : B ⥤ D` with `P` preserving injective objects, this is the natural
transformation `Rⁿ Q ∘ P ⟶ Rⁿ (Q ∘ P)`, with no exactness hypothesis on `P`.  It is the edge
morphism `E₂^{n,0} ⟶ H^n` of the Grothendieck spectral sequence of `(P, Q)`. -/
def edge (n : ℕ) : P ⋙ Q.rightDerived n ⟶ (P ⋙ Q).rightDerived n where
  app X := ((injectiveResolution (P.obj X)).isoRightDerivedObj Q n).hom ≫
    (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).map
      ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map (resolutionComparison P X)) ≫
    (isoRightDerivedObjComp P Q (injectiveResolution X) n).inv
  naturality X Y g := by
    dsimp only [Functor.comp_map]
    simp only [Category.assoc]
    rw [InjectiveResolution.isoRightDerivedObj_hom_naturality_assoc (P.map g)
        (injectiveResolution (P.obj X)) (injectiveResolution (P.obj Y))
        (InjectiveResolution.desc (P.map g) (injectiveResolution (P.obj Y))
          (injectiveResolution (P.obj X)))
        (InjectiveResolution.desc_commutes_zero _ _ _) Q n,
      isoRightDerivedObjComp_inv_naturality P Q g (injectiveResolution X)
        (injectiveResolution Y)
        (InjectiveResolution.desc g (injectiveResolution Y) (injectiveResolution X))
        (InjectiveResolution.desc_commutes_zero _ _ _) n]
    refine (cancel_epi _).mpr ?_
    simp only [← Category.assoc]
    refine (cancel_mono _).mpr ?_
    simp only [← CategoryTheory.Functor.map_comp]
    refine homologyMap_map_eq_of_aug Q (injectiveResolution (P.obj X))
      (injective_mapHomologicalComplex_obj P _ (injectiveResolution Y).injective)
      (InjectiveResolution.desc (P.map g) (injectiveResolution (P.obj Y))
        (injectiveResolution (P.obj X)) ≫ resolutionComparison P Y)
      (resolutionComparison P X ≫ (P.mapHomologicalComplex (ComplexShape.up ℕ)).map
        (InjectiveResolution.desc g (injectiveResolution Y) (injectiveResolution X))) ?_ n
    exact comp_aug_eq ((injectiveResolution (P.obj X)).ι.f 0)
      ((InjectiveResolution.desc (P.map g) (injectiveResolution (P.obj Y))
        (injectiveResolution (P.obj X))).f 0) (P.map g)
      ((injectiveResolution (P.obj Y)).ι.f 0) ((resolutionComparison P Y).f 0)
      (P.map ((injectiveResolution Y).ι.f 0)) ((resolutionComparison P X).f 0)
      (P.map ((injectiveResolution X).ι.f 0))
      (((P.mapHomologicalComplex (ComplexShape.up ℕ)).map
        (InjectiveResolution.desc g (injectiveResolution Y) (injectiveResolution X))).f 0)
      (InjectiveResolution.desc_commutes_zero _ _ _)
      (ι_f_zero_comp_resolutionComparison P Y)
      (ι_f_zero_comp_resolutionComparison P X)
      (map_comp_eq_map_comp P ((injectiveResolution X).ι.f 0)
        ((InjectiveResolution.desc g (injectiveResolution Y)
          (injectiveResolution X)).f 0) g ((injectiveResolution Y).ι.f 0)
        (InjectiveResolution.desc_commutes_zero _ _ _))

/-- Any augmentation-preserving comparison of any injective resolutions computes the edge
morphism.  This frees consumers from the globally chosen resolutions: given `I` resolving `X`,
`J` resolving `P X`, and any `φ : J ⟶ P I` extending `P` applied to the augmentation of `I`,
the component of `edge` at `X` is read off from `φ`. -/
theorem edge_app_eq (n : ℕ) {X : A} (I : InjectiveResolution X)
    (J : InjectiveResolution (P.obj X))
    (φ : J.cocomplex ⟶ (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
    (hφ : J.ι.f 0 ≫ φ.f 0 = P.map (I.ι.f 0)) :
    (edge P Q n).app X = (J.isoRightDerivedObj Q n).hom ≫
      HomologicalComplex.homologyMap
        ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) n ≫
      (I.isoRightDerivedObj (P ⋙ Q) n).inv := by
  change (edge P Q n).app X = (J.isoRightDerivedObj Q n).hom ≫
    (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).map
      ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) ≫
    (isoRightDerivedObjComp P Q I n).inv
  have hJ := InjectiveResolution.isoRightDerivedObj_hom_naturality (𝟙 (P.obj X))
    (injectiveResolution (P.obj X)) J
    (InjectiveResolution.desc (𝟙 (P.obj X)) J (injectiveResolution (P.obj X)))
    (InjectiveResolution.desc_commutes_zero _ _ _) Q n
  have hI := isoRightDerivedObjComp_inv_naturality P Q (𝟙 X) (injectiveResolution X) I
    (InjectiveResolution.desc (𝟙 X) I (injectiveResolution X))
    (InjectiveResolution.desc_commutes_zero _ _ _) n
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at hJ
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at hI
  dsimp only [edge]
  rw [hI, hJ]
  simp only [Category.assoc]
  refine (cancel_epi _).mpr ?_
  simp only [← Category.assoc]
  refine (cancel_mono _).mpr ?_
  simp only [Functor.comp_map, ← CategoryTheory.Functor.map_comp]
  refine homologyMap_map_eq_of_aug Q (injectiveResolution (P.obj X))
    (injective_mapHomologicalComplex_obj P _ I.injective)
    (resolutionComparison P X ≫ (P.mapHomologicalComplex (ComplexShape.up ℕ)).map
      (InjectiveResolution.desc (𝟙 X) I (injectiveResolution X)))
    (InjectiveResolution.desc (𝟙 (P.obj X)) J (injectiveResolution (P.obj X)) ≫ φ) ?_ n
  exact (comp_aug_eq' ((injectiveResolution (P.obj X)).ι.f 0)
    ((InjectiveResolution.desc (𝟙 (P.obj X)) J (injectiveResolution (P.obj X))).f 0)
    (J.ι.f 0) (φ.f 0) (P.map (I.ι.f 0)) ((resolutionComparison P X).f 0)
    (P.map ((injectiveResolution X).ι.f 0))
    (((P.mapHomologicalComplex (ComplexShape.up ℕ)).map
      (InjectiveResolution.desc (𝟙 X) I (injectiveResolution X))).f 0)
    (ι_f_zero_comp_desc_id J (injectiveResolution (P.obj X))) hφ
    (ι_f_zero_comp_resolutionComparison P X)
    (map_comp_eq_map P ((injectiveResolution X).ι.f 0)
      ((InjectiveResolution.desc (𝟙 X) I (injectiveResolution X)).f 0) (I.ι.f 0)
      (ι_f_zero_comp_desc_id I (injectiveResolution X)))).symm

end

section

variable [HasInjectiveResolutions A]

/-- **Restriction along a transformation `η : 𝟭 ⟶ P`, followed by the edge morphism, is the
right derived functor of `Q η`.** For `X` in `𝒜`, the composite
`R ⁿQ(X) ⟶ R ⁿQ(P X) ⟶ R ⁿ(P ⋙ Q)(X)` of the map induced by `η_X` and the edge morphism of
the pair `(P, Q)` is the component at `X` of the morphism of right derived functors induced by
`Q η : Q ⟶ P ⋙ Q`. On a chosen injective resolution `I` of `X` both are induced by a map
`I ⟶ P(I)` extending `η_X` on the augmentation, and any two such maps are homotopic, the terms
of `P(I)` being injective. -/
theorem rightDerived_map_comp_edge_app (P : A ⥤ A) [P.Additive] [P.PreservesInjectiveObjects]
    (Q : A ⥤ D) [Q.Additive] (η : 𝟭 A ⟶ P) (n : ℕ) (X : A) :
    (Q.rightDerived n).map (η.app X) ≫ (edge P Q n).app X =
      (NatTrans.rightDerived (Functor.whiskerRight η Q) n).app X := by
  let I := injectiveResolution X
  let J := injectiveResolution (P.obj X)
  let φ := resolutionComparison P X
  let ψ := InjectiveResolution.desc (η.app X) J I
  rw [edge_app_eq P Q n I J φ (ι_f_zero_comp_resolutionComparison P X),
    Functor.rightDerived_map_eq Q n (η.app X) ψ (InjectiveResolution.desc_commutes _ _ _),
    InjectiveResolution.rightDerived_app_eq _ I n]
  have key : HomologicalComplex.homologyMap ((Q.mapHomologicalComplex
      (ComplexShape.up ℕ)).map ψ) n ≫
      HomologicalComplex.homologyMap ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) n =
      HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex (Functor.whiskerRight η Q)
        (ComplexShape.up ℕ)).app I.cocomplex) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← Functor.map_comp]
    have h : I.ι.f 0 ≫ ψ.f 0 = η.app X ≫ J.ι.f 0 := InjectiveResolution.desc_commutes_zero _ J I
    exact homologyMap_map_eq_of_aug Q I (injective_mapHomologicalComplex_obj P _ I.injective)
      (ψ ≫ φ) ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℕ)).app I.cocomplex)
      ((congrArg (fun z => I.ι.f 0 ≫ z) (HomologicalComplex.comp_f ψ φ 0)).trans
        (((reassoc_of% h) (φ.f 0)).trans ((Category.assoc _ _ _).trans
          ((congrArg (fun z => η.app X ≫ z) (ι_f_zero_comp_resolutionComparison P X)).trans
            (η.naturality (I.ι.f 0)).symm)))) n
  have h : (HomologicalComplex.homologyMap ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map ψ) n ≫
        (J.isoRightDerivedObj Q n).inv) ≫ (J.isoRightDerivedObj Q n).hom ≫
        HomologicalComplex.homologyMap ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) n ≫
          (I.isoRightDerivedObj (P ⋙ Q) n).inv =
      HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex (Functor.whiskerRight η Q)
        (ComplexShape.up ℕ)).app I.cocomplex) n ≫ (I.isoRightDerivedObj (P ⋙ Q) n).inv :=
    (Category.assoc _ _ _).trans ((congrArg (fun z =>
      HomologicalComplex.homologyMap ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map ψ) n ≫ z)
        (Iso.inv_hom_id_assoc (J.isoRightDerivedObj Q n) _)).trans ((reassoc_of% key) _))
  exact (Category.assoc _ _ _).trans (congrArg (fun z => (I.isoRightDerivedObj Q n).hom ≫ z) h)

end

end Stacks.Cohomology.RightDerivedEdge

end
