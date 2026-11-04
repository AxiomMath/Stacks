module

public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothDeRhamBaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.PullbackComplexDegreewise
public import StacksFrontier.AlgebraicGeometry.DeRham.Functoriality
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.RealizationChernClass
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PushforwardComparisonAgreesWithOrdinary
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupProductAndDerivedPushforward
public import StacksFrontier.CategoryTheory.Localization.MapHomotopyCategoryAdjunctionCounit

/-!
# The transpose of the canonical comparison `Lg₀^*Ω^•_{X/S} ⟶ Ω^•_{X'/S'}`

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a commutative square of schemes and let `g₀ : (X', f'^{-1}𝒪_{S'}) ⟶ (X, f^{-1}𝒪_S)` be the
induced morphism of inverse-image ringed spaces
(`Stacks.DeRhamDirectImage.inverseImageBaseMap`). This file identifies the transpose of the
canonical comparison
`AlgebraicGeometry.ProperSmoothDeRham.deRhamBaseChangeComparison : Lg₀^*Ω^•_{X/S} ⟶ Ω^•_{X'/S'}`
under `Lg₀^* ⊣ Rg₀_*` with the class of the canonical map `Ω^•_{X/S} ⟶ (g₀)_*Ω^•_{X'/S'}`
followed by the comparison of degreewise and derived pushforward, and identifies that canonical
map with the map of complexes of abelian sheaves
`AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMap`.

## Main definitions

* `Stacks.DeRhamBaseChange.deRhamPushforwardInt`: the canonical map
  `Ω^•_{X/S} ⟶ (g₀)_*Ω^•_{X'/S'}` of `ℤ`-indexed complexes of `f^{-1}𝒪_S`-modules, the transpose
  of `deRhamPullbackInt` under the degreewise adjunction `g₀^* ⊣ (g₀)_*`.
* `Stacks.DeRhamBaseChange.deRhamPushforwardPlusIso`: the identification of the bounded-below
  complex of abelian sheaves `g'_*Ω^•_{X'/S'}` with the underlying complex of
  `(g₀)_*Ω^•_{X'/S'}`.

## Main results

* `Stacks.DeRhamBaseChange.formsAdjoint_eq_deRhamFormsPushforwardHom`: the adjoint
  `Ω^p_{X/S} ⟶ g'_*Ω^p_{X'/S'}` of the canonical map on forms is the degree-`p` component of the
  graded-algebra homomorphism of Tag 07HX.
* `Stacks.DeRhamBaseChange.deRhamAbelianPushforwardMap_eq_toSheaf_map`: the abelian de Rham
  pushforward map is the image of `deRhamPushforwardChain` under the forgetful functor.
* `Stacks.DeRhamBaseChange.deRhamPushforwardInt_eq`: `deRhamPushforwardInt` is the extension by
  zero of `deRhamPushforwardChain`.
* `Stacks.DeRhamBaseChange.deRhamAbelianPushforwardMapPlus_comp_iso`: the square comparing the
  abelian de Rham pushforward map with the forgetful image of `deRhamPushforwardInt`.
* `Stacks.DeRhamBaseChange.homEquiv_deRhamBaseChangeComparison`: the transpose of
  `deRhamBaseChangeComparison` under the derived adjunction is the class of
  `deRhamPushforwardInt` followed by the comparison `(g₀)_* ⟶ Rg₀_*`;
  `homEquiv_deRhamBaseChangeComparison_pushforwardComparisonQ` is the same statement read at the
  localization functor `Q` with `pushforwardComparisonQ`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage AlgebraicGeometry.ProperSmoothDeRham

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.DeRhamBaseChange

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-! ### The degreewise maps -/

/-- **The adjoint of the canonical map on forms is the graded homomorphism of Tag 07HX in
degree `p`**: the map `Ω^p_{X/S} ⟶ g'_*Ω^p_{X'/S'}` adjoint to
`(g')^*Ω^p_{X/S} ⟶ Ω^p_{X'/S'}` is the degree-`p` component of
`⋀ Ω_{X/S} ⟶ g'_*(⋀ Ω_{X'/S'})`. -/
theorem formsAdjoint_eq_deRhamFormsPushforwardHom (p : ℕ) :
    formsAdjoint g' f' f g w p = (Scheme.Hom.deRhamFormsPushforwardHom g' f f' g w).app (p : ℤ) :=
  (formsAdjoint_eq g' f' f g w p).trans
    (((modulePullbackPushforwardAdjunction g'.toLRSHom.toShHom).homEquiv_unit _ _ _).symm.trans
      (Scheme.Hom.homEquiv_relativeDifferentialFormsMap g' f f' g w (p : ℤ)))

/-- **The abelian de Rham pushforward map is the forgetful image of its module refinement**, in
each degree: the degree-`n` component of `Ω^•_{X/S} ⟶ g'_*Ω^•_{X'/S'}` read in abelian sheaves is
the underlying map of abelian sheaves of the degree-`n` component of `deRhamPushforwardChain`. -/
theorem deRhamAbelianPushforwardMap_f (n : ℕ) :
    (Scheme.Hom.deRhamAbelianPushforwardMap g' f f' g w).f n =
      (_root_.SheafOfModules.toSheaf.{u}
            (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
              ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))).map
        ((deRhamPushforwardChain g' f' f g w).f n) := by
  ext U x
  exact (congrArg (fun φ => φ.val.app U x)
    (formsAdjoint_eq_deRhamFormsPushforwardHom g' f' f g w n)).symm.trans
    (pushforwardSquareIso_inv_val_app g' f' f g w
      (Scheme.Hom.relativeDifferentialForms f' (n : ℤ)) U
      ((formsAdjoint g' f' f g w n).val.app U x)).symm

/-- **The abelian de Rham pushforward map is the forgetful image of `deRhamPushforwardChain`**:
the canonical map `Ω^•_{X/S} ⟶ g'_*Ω^•_{X'/S'}` of complexes of abelian sheaves is the image of
the map `Ω^•_{X/S} ⟶ (g₀)_*Ω^•_{X'/S'}` of complexes of `f^{-1}𝒪_S`-modules under the forgetful
functor to abelian sheaves. -/
theorem deRhamAbelianPushforwardMap_eq_toSheaf_map :
    Scheme.Hom.deRhamAbelianPushforwardMap g' f f' g w =
      ((_root_.SheafOfModules.toSheaf.{u}
            (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
              ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
                S.sheaf))).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (deRhamPushforwardChain g' f' f g w) :=
  HomologicalComplex.hom_ext _ _ fun n => deRhamAbelianPushforwardMap_f g' f' f g w n

/-! ### The extended canonical map on the pushforward side -/

/-- **The canonical map of extended de Rham complexes `Ω^•_{X/S} ⟶ (g₀)_*Ω^•_{X'/S'}`** of
`f^{-1}𝒪_S`-modules: the transpose of `deRhamPullbackInt` under the adjunction
`g₀^* ⊣ (g₀)_*` applied degreewise to complexes. -/
def deRhamPushforwardInt :
    deRhamComplexInt f ⟶
      ((modulePushforward (inverseImageBaseMap g' f' f g w)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (deRhamComplexInt f') :=
  (((modulePullbackPushforwardAdjunction (inverseImageBaseMap g' f' f g w)).mapHomologicalComplex
    (ComplexShape.up ℤ)).homEquiv _ _) (deRhamPullbackInt g' f' f g w)

/-- The transpose of a morphism of complexes under the degreewise adjunction is, in each degree,
the transpose of its component. -/
private theorem mapHomologicalComplex_homEquiv_apply_f {A B : Type*} [Category A] [Abelian A]
    [Category B] [Abelian B] {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive] (adj : F ⊣ G)
    {ι : Type*} (c : ComplexShape ι) {K : HomologicalComplex A c} {L : HomologicalComplex B c}
    (ψ : (F.mapHomologicalComplex c).obj K ⟶ L) (n : ι) :
    (((adj.mapHomologicalComplex c).homEquiv K L) ψ).f n =
      (adj.homEquiv (K.X n) (L.X n)) (ψ.f n) :=
  rfl

/-- Transposing a morphism that is conjugate, through isomorphisms of its source and target, to
a morphism with a known transpose. -/
private theorem homEquiv_eq_of_map_hom_comp {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) {A A' : C} {B B' : D} (a : A ≅ A') (b : B ≅ B')
    (x : L.obj A ⟶ B) (y : L.obj A' ⟶ B') (y' : A' ⟶ R.obj B') (hy : adj.homEquiv _ _ y = y')
    (h : L.map a.hom ≫ y = x ≫ b.hom) :
    adj.homEquiv _ _ x = a.hom ≫ y' ≫ R.map b.inv := by
  have hx : x = L.map a.hom ≫ y ≫ b.inv := by
    rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hx, Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right, hy]

/-- **The degree-`p` component of the extended canonical map** is the degree-`p` component of
`deRhamPushforwardChain`, read through the canonical identifications of the extended complexes
with `Ω^p_{X/S}` and `Ω^p_{X'/S'}`. -/
theorem deRhamPushforwardInt_f (p : ℕ) :
    (deRhamPushforwardInt g' f' f g w).f p =
      ((deRhamComplexNat f).extendXIso ComplexShape.embeddingUpNat (i := p) rfl).hom ≫
        (deRhamPushforwardChain g' f' f g w).f p ≫
          (modulePushforward (inverseImageBaseMap g' f' f g w)).map
            ((deRhamComplexNat f').extendXIso ComplexShape.embeddingUpNat (i := p) rfl).inv :=
  (mapHomologicalComplex_homEquiv_apply_f _ _ _ _).trans
    (homEquiv_eq_of_map_hom_comp
      (modulePullbackPushforwardAdjunction (inverseImageBaseMap g' f' f g w))
      ((deRhamComplexNat f).extendXIso ComplexShape.embeddingUpNat (i := p) rfl)
      ((deRhamComplexNat f').extendXIso ComplexShape.embeddingUpNat (i := p) rfl)
      ((deRhamPullbackInt g' f' f g w).f p) ((deRhamPullbackChain g' f' f g w).f p)
      ((deRhamPushforwardChain g' f' f g w).f p)
      (((modulePullbackPushforwardAdjunction (inverseImageBaseMap g' f' f g w)).homEquiv
        _ _).apply_symm_apply ((deRhamPushforwardChain g' f' f g w).f p))
      (deRhamPullbackInt_f w p))

/-- Two morphisms of `ℤ`-indexed cochain complexes that vanish in negative degrees agree if they
agree in each degree `n : ℕ`. -/
private theorem hom_ext_of_isZero_neg_of_nat {C : Type*} [Category C] [Preadditive C]
    {K L : CochainComplex C ℤ} (φ ψ : K ⟶ L) (hK : ∀ i : ℤ, i < 0 → IsZero (K.X i))
    (h : ∀ n : ℕ, φ.f n = ψ.f n) : φ = ψ := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  rcases lt_or_ge i 0 with hi | hi
  · exact (hK i hi).eq_of_src _ _
  · lift i to ℕ using hi
    exact h i

/-- **The extended canonical map is the extension by zero of `deRhamPushforwardChain`**: it is
`deRhamPushforwardChain` extended along `ℕ ⊆ ℤ`, followed by the identification of the extension
of `(g₀)_*Ω^•_{X'/S'}` with `(g₀)_*` of the extension of `Ω^•_{X'/S'}`. -/
theorem deRhamPushforwardInt_eq :
    deRhamPushforwardInt g' f' f g w =
      HomologicalComplex.extendMap (deRhamPushforwardChain g' f' f g w)
          ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.mapHomologicalComplexExtendIso
          (modulePushforward (inverseImageBaseMap g' f' f g w)) (deRhamComplexNat f')
          ComplexShape.embeddingUpNat).hom := by
  refine hom_ext_of_isZero_neg_of_nat _ _ (isZero_deRhamComplexInt_X_of_neg f) fun i => ?_
  exact (deRhamPushforwardInt_f g' f' f g w i).trans
    (HomologicalComplex.extendMap_mapHomologicalComplexExtendIso_f
      (F := modulePushforward (inverseImageBaseMap g' f' f g w)) (L := deRhamComplexNat f)
      (deRhamComplexNat f') (deRhamPushforwardChain g' f' f g w) ComplexShape.embeddingUpNat
      (i := i) rfl).symm

/-! ### The square for the realization comparison -/

/-- The pushforward `(g₀)_*Ω^•_{X'/S'}` of the extended de Rham complex is concentrated in
nonnegative degrees. -/
instance isStrictlyGE_modulePushforward_deRhamComplexInt :
    CochainComplex.IsStrictlyGE
      (((modulePushforward (inverseImageBaseMap g' f' f g w)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (deRhamComplexInt f')) 0 where
  isZero i hi := (modulePushforward (inverseImageBaseMap g' f' f g w)).map_isZero
    (isZero_deRhamComplexInt_X_of_neg f' i (by
      by_contra h
      exact hi i.toNat (by simp only [ComplexShape.embeddingUpIntGE_f]; omega)))

/-- `(g₀)_*Ω^•_{X'/S'}`, as a bounded-below complex of `f^{-1}𝒪_S`-modules. -/
abbrev deRhamPushforwardIntPlus :
    CochainComplex.Plus (_root_.SheafOfModules.{u}
      (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))) :=
  ⟨((modulePushforward (inverseImageBaseMap g' f' f g w)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (deRhamComplexInt f'), 0,
    isStrictlyGE_modulePushforward_deRhamComplexInt g' f' f g w⟩

/-- **The bounded-below complex `g'_*Ω^•_{X'/S'}` of abelian sheaves is the underlying complex
of `(g₀)_*Ω^•_{X'/S'}`.** -/
def deRhamPushforwardPlusIso :
    Scheme.Hom.deRhamPushforwardPlus g' f' ≅
      (_root_.SheafOfModules.toSheaf (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))).mapCochainComplexPlus.obj
        (deRhamPushforwardIntPlus g' f' f g w) :=
  ObjectProperty.isoMk _
    (((Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u} g'.base).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso
      (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexIntIso (Scheme.Hom.deRhamAlgebras f')
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f'))))

/-- `deRhamPushforwardInt` as a morphism of bounded-below complexes of `f^{-1}𝒪_S`-modules. -/
abbrev deRhamPushforwardIntPlusHom :
    AlgebraicGeometry.SheafOfModules.deRhamComplexPlus (Scheme.Hom.deRhamAlgebras f)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) ⟶
      deRhamPushforwardIntPlus g' f' f g w :=
  ⟨deRhamPushforwardInt g' f' f g w⟩

/-- Cancellation of the image of the inverse of an isomorphism against the image of the
isomorphism. -/
private theorem comp_map_inv_comp_map_hom_comp {A M₀ : Type*} [Category A] [Category M₀]
    (T : M₀ ⥤ A) {P : A} {R R' V W : M₀} (a : P ⟶ T.obj R') (k : R ≅ R') (ch : R' ⟶ V)
    (y : V ⟶ W) :
    (a ≫ T.map k.inv) ≫ T.map (k.hom ≫ ch ≫ y) = a ≫ T.map ch ≫ T.map y := by
  simp [← Functor.map_comp]

/-- **The abelian de Rham pushforward map is the underlying map of `deRhamPushforwardInt`**, as a
commutative square of bounded-below complexes of abelian sheaves on `X`: followed by
`deRhamPushforwardPlusIso`, the canonical map `Ω^•_{X/S} ⟶ g'_*Ω^•_{X'/S'}` is the identification
`AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlusIso` of `Ω^•_{X/S}` followed by the
underlying map of `deRhamPushforwardInt`. -/
theorem deRhamAbelianPushforwardMapPlus_comp_iso :
    Scheme.Hom.deRhamAbelianPushforwardMapPlus g' f f' g w ≫
        (deRhamPushforwardPlusIso g' f' f g w).hom =
      (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlusIso (Scheme.Hom.deRhamAlgebras f)
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f))).hom ≫
        (_root_.SheafOfModules.toSheaf (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))).mapCochainComplexPlus.map
          (deRhamPushforwardIntPlusHom g' f' f g w) := by
  refine ObjectProperty.hom_ext _ ?_
  refine hom_ext_of_isZero_neg_of_nat _ _ (fun i hi => HomologicalComplex.isZero_extend_X _ _ i
    fun j hj => by change (j : ℤ) = i at hj; omega) fun i => ?_
  refine (HomologicalComplex.comp_f _ _ _).trans ?_
  refine (congrArg₂ (· ≫ ·)
    (HomologicalComplex.extendMap_mapHomologicalComplexExtendIso_f _ _ _ _ (i := i) rfl)
    ((Functor.mapHomologicalComplex_map_f _ _ _ _).trans (congrArg _
      (HomologicalComplex.mapHomologicalComplexExtendIso_hom_f _ _ _ (i := i) rfl)))).trans ?_
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_assoc]
  refine Eq.symm ((HomologicalComplex.comp_f _ _ _).trans ?_)
  refine (congrArg₂ (· ≫ ·)
    (HomologicalComplex.mapHomologicalComplexExtendIso_hom_f
      (_root_.SheafOfModules.toSheaf (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)))
      (Scheme.Hom.deRhamComplex f) ComplexShape.embeddingUpNat (i := i) rfl)
    ((Functor.mapHomologicalComplex_map_f _ _ _ _).trans
      (congrArg _ (deRhamPushforwardInt_f g' f' f g w i)))).trans ?_
  refine (comp_map_inv_comp_map_hom_comp _ _ _ _ _).trans ?_
  refine congrArg (_ ≫ ·) (congrArg₂ (· ≫ ·)
    (deRhamAbelianPushforwardMap_f g' f' f g w i).symm ?_)
  ext U s
  rfl

/-! ### The transpose of the derived comparison -/

/-- The extended canonical map is the degreewise unit of `g₀^* ⊣ (g₀)_*` followed by the
pushforward of `deRhamPullbackInt`. -/
theorem deRhamPushforwardInt_eq_unit_comp :
    deRhamPushforwardInt g' f' f g w =
      (Adjunction.mapHomologicalComplexAdjunction
          (modulePullbackPushforwardAdjunction (inverseImageBaseMap g' f' f g w))
          (ComplexShape.up ℤ)).unit.app (deRhamComplexInt f) ≫
        ((modulePushforward (inverseImageBaseMap g' f' f g w)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (deRhamPullbackInt g' f' f g w) :=
  HomologicalComplex.hom_ext _ _ fun n =>
    (mapHomologicalComplex_homEquiv_apply_f _ _ _ n).trans (Adjunction.homEquiv_unit _ _ _ _)

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedBaseChange in
/-- **The transpose of the canonical comparison `Lg₀^*Ω^•_{X/S} ⟶ Ω^•_{X'/S'}`** under the
derived adjunction `Lg₀^* ⊣ Rg₀_*` is the class of the canonical map
`Ω^•_{X/S} ⟶ (g₀)_*Ω^•_{X'/S'}` followed by the comparison `(g₀)_*Ω^•_{X'/S'} ⟶ Rg₀_*Ω^•_{X'/S'}`
of degreewise and derived pushforward. -/
theorem homEquiv_deRhamBaseChangeComparison :
    (derivedAdjunction (inverseImageBaseMap g' f' f g w)).homEquiv _ _
        (deRhamBaseChangeComparison g' f' f g w) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          (deRhamPushforwardInt g' f' f g w)) ≫
        (derivedPushforwardUnit (inverseImageBaseMap g' f' f g w)).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (deRhamComplexInt f')) := by
  have hq : (homotopyPullbackPushforwardAdjunction (inverseImageBaseMap g' f' f g w)).unit.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (deRhamComplexInt f)) ≫
      ((modulePushforward (inverseImageBaseMap g' f' f g w)).mapHomotopyCategory
        (ComplexShape.up ℤ)).map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          (deRhamPullbackInt g' f' f g w)) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (deRhamPushforwardInt g' f' f g w) :=
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_comp _ _).symm.trans
      (congrArg (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (deRhamPushforwardInt_eq_unit_comp g' f' f g w).symm)
  refine ((derivedAdjunction (inverseImageBaseMap g' f' f g w)).homEquiv_naturality_right
    _ _).trans ?_
  refine (congrArg (· ≫ _) (derivedPullbackComparison_homEquiv
    (inverseImageBaseMap g' f' f g w) _)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((derivedPushforwardUnit (inverseImageBaseMap g' f' f g w)).naturality
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      (deRhamPullbackInt g' f' f g w))).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ _) ((DerivedCategory.Qh.map_comp _ _).symm.trans
    (congrArg DerivedCategory.Qh.map hq))

/-- Moving a naturality square past the first factor of a composite. -/
private theorem comp_comp_comp_eq_of_comp_eq {C : Type*} [Category C] {P P' Q R T U : C}
    (a : P ⟶ P') (b : P' ⟶ Q) (c : Q ⟶ R) (d : R ⟶ T) (e : P ⟶ U) (k : U ⟶ Q)
    (h : e ≫ k = a ≫ b) : a ≫ (b ≫ c) ≫ d = e ≫ k ≫ c ≫ d := by
  rw [← Category.assoc e, h]
  simp only [Category.assoc]

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces in
/-- **The transpose of the canonical comparison, read at the localization functor `Q`**: after
conjugating by `DerivedCategory.quotientCompQhIso`, the transpose of
`deRhamBaseChangeComparison` under `Lg₀^* ⊣ Rg₀_*` is `Q` of the canonical map
`Ω^•_{X/S} ⟶ (g₀)_*Ω^•_{X'/S'}` followed by the comparison `pushforwardComparisonQ` of degreewise
and derived pushforward. -/
theorem homEquiv_deRhamBaseChangeComparison_pushforwardComparisonQ :
    (DerivedCategory.quotientCompQhIso _).inv.app (deRhamComplexInt f) ≫
        (derivedAdjunction (inverseImageBaseMap g' f' f g w)).homEquiv _ _
          (deRhamBaseChangeComparison g' f' f g w) ≫
        (derivedPushforward (inverseImageBaseMap g' f' f g w)).map
          ((DerivedCategory.quotientCompQhIso _).hom.app (deRhamComplexInt f')) =
      DerivedCategory.Q.map (deRhamPushforwardInt g' f' f g w) ≫
        pushforwardComparisonQ (inverseImageBaseMap g' f' f g w) (deRhamComplexInt f') :=
  (congrArg (fun t => (DerivedCategory.quotientCompQhIso _).inv.app (deRhamComplexInt f) ≫ t ≫
      (derivedPushforward (inverseImageBaseMap g' f' f g w)).map
        ((DerivedCategory.quotientCompQhIso _).hom.app (deRhamComplexInt f')))
    (homEquiv_deRhamBaseChangeComparison g' f' f g w)).trans
    (comp_comp_comp_eq_of_comp_eq _ _ _ _ _ _
      (DerivedCategory.quotientCompQhIso_inv_naturality (deRhamPushforwardInt g' f' f g w)))

end Stacks.DeRhamBaseChange
