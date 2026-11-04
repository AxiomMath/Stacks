module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitComparisonCospan
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStageComparison
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitSquareIsoInvariance
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.OneGeneratorColimVectCornerCompat

/-!
# Stacks Tag 0EXC on finite locally free `colim_F 𝒪`-modules

Stacks Tag 0EXC is proved, as `AlgebraicGeometry.colimVectComparison_isEquivalence`, for the
explicit model `colim_F Vect(-)` of Stacks Tag 0EXA. This file moves it to the categories of
finite locally free `colim_F 𝒪`-modules, which are the fibres of the category fibred in groupoids
of Stacks Tag 0EXE.

## Main definitions

* `AlgebraicGeometry.colimVectSquareCatCommSqOver`: the square of transition functors on the model
  `colim_F Vect(-)` attached to a commutative square of schemes.

## Main results

* `AlgebraicGeometry.frobeniusColimitVectComparisonPullbackIso_inv_comp`: the commutation of the
  comparison functor of Stacks Tag 0EXB with restriction is compatible with composition.
* `AlgebraicGeometry.frobeniusColimitVectComparison_square_cube`: the cube coherence of those
  commutations over a commutative square.
* `AlgebraicGeometry.isEquivalence_frobeniusColimitVectorBundlesComparison_of_colimVect`: for a
  commutative square of quasi-compact quasi-separated schemes, the comparison functor on finite
  locally free `colim_F 𝒪`-modules is an equivalence as soon as the one on the models is.
* `AlgebraicGeometry.isEquivalence_frobeniusColimitVectorBundlesComparison_oneGeneratorSquare`:
  **Stacks Tag 0EXC for finite locally free `colim_F 𝒪`-modules**, at the square of Example 0EVG.

## Implementation notes

The transport is `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.isEquivalence_of_cube`
for the cube whose vertical functors are the comparison functors of Stacks Tag 0EXB at the four
corners. These are equivalences by Stacks Tag 0EXB, the four corners being affine. The side faces
of the cube are `AlgebraicGeometry.frobeniusColimitVectComparisonPullbackIso`. The cube
coherence reduces, on an object `(ℰ, n)`, to the compatibility of the stage bridge with
composition, `AlgebraicGeometry.frobeniusStageFunctorPullbackIso_comp`, read on the two legs of
the square.

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
* [Stacks Project, Tag 0EXC](https://stacks.math.columbia.edu/tag/0EXC)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]

/-- The comparison functor of Stacks Tag 0EXB on a morphism presented at a stage is the stage
functor on that morphism. -/
lemma frobeniusColimitVectComparison_map_stageHomOf (X : Scheme.{u}) (hX : IsInCharacteristic X p)
    (n : ℕ) {E G : X.Vect} (g : E ⟶ G) :
    (frobeniusColimitVectComparison X p hX).map (EndoColim.stageHomOf _ n g) =
      (frobeniusStageFunctor X p hX n).map g :=
  (frobeniusColimitVectPseudococone X p hX).homMap_stageFunctor_map n g

/-- The inverse of the commutation of the comparison functor of Stacks Tag 0EXB with restriction,
at an object `(ℰ, n)`, is the inverse of the stage bridge. -/
lemma frobeniusColimitVectComparisonPullbackIso_inv_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (A : frobeniusColimitVectModel Y p hY) :
    (frobeniusColimitVectComparisonPullbackIso p f hX hY).inv.app A =
      (frobeniusStageFunctorPullbackIso p f hX hY A.stage).inv.app A.obj :=
  Iso.inv_ext (f := (frobeniusColimitVectComparisonPullbackIso p f hX hY).app A) (by
    simp only [Iso.app_hom, frobeniusColimitVectComparisonPullbackIso_hom_app]
    exact Iso.hom_inv_id_app _ _)

/-- **The inverse stage bridges compose**: the inverse form of
`AlgebraicGeometry.frobeniusStageFunctorPullbackIso_comp`. -/
lemma frobeniusStageFunctorPullbackIso_inv_comp {X Y W : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ W)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (hW : IsInCharacteristic W p)
    (n : ℕ) (E : W.Vect) :
    (frobeniusStageFunctorPullbackIso p g hX hY n).inv.app ((Scheme.Vect.pullback h).obj E) ≫
        (frobeniusColimitVectorBundlesPullback p g hX hY).map
          ((frobeniusStageFunctorPullbackIso p h hY hW n).inv.app E) =
      (frobeniusStageFunctor X p hX n).map ((Scheme.Vect.pullbackComp g h).hom.app E) ≫
        (frobeniusStageFunctorPullbackIso p (g ≫ h) hX hW n).inv.app E ≫
          (frobeniusColimitVectorBundlesPullbackComp p g h hX hY hW).inv.app
            ((frobeniusStageFunctor W p hW n).obj E) := by
  have hc := frobeniusStageFunctorPullbackIso_comp p g h hX hY hW n E
  have key : ((frobeniusStageFunctorPullbackIso p g hX hY n).inv.app
          ((Scheme.Vect.pullback h).obj E) ≫
        (frobeniusColimitVectorBundlesPullback p g hX hY).map
          ((frobeniusStageFunctorPullbackIso p h hY hW n).inv.app E)) ≫
      (frobeniusColimitVectorBundlesPullbackComp p g h hX hY hW).hom.app
          ((frobeniusStageFunctor W p hW n).obj E) ≫
        (frobeniusStageFunctorPullbackIso p (g ≫ h) hX hW n).hom.app E =
      (frobeniusStageFunctor X p hX n).map ((Scheme.Vect.pullbackComp g h).hom.app E) := by
    rw [hc]
    simp only [Category.assoc]
    have e := ((frobeniusColimitVectorBundlesPullback p g hX hY).mapIso
      ((frobeniusStageFunctorPullbackIso p h hY hW n).app E)).inv_hom_id_assoc
      ((frobeniusStageFunctorPullbackIso p g hX hY n).hom.app ((Scheme.Vect.pullback h).obj E) ≫
        (frobeniusStageFunctor X p hX n).map ((Scheme.Vect.pullbackComp g h).hom.app E))
    simp only [Functor.mapIso_inv, Functor.mapIso_hom, Iso.app_inv, Iso.app_hom] at e
    rw [e, Iso.inv_hom_id_app_assoc]
  rw [← key]
  simp

/-- **The commutation of the comparison functor of Stacks Tag 0EXB with restriction is compatible
with composition.** -/
lemma frobeniusColimitVectComparisonPullbackIso_inv_comp {X Y W : Scheme.{u}} (g : X ⟶ Y)
    (h : Y ⟶ W) (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (hW : IsInCharacteristic W p) (x : frobeniusColimitVectModel W p hW) :
    (frobeniusColimitVectComparisonPullbackIso p g hX hY).inv.app
          ((OneGeneratorSquare.colimVectPullback p hY hW h).obj x) ≫
        (frobeniusColimitVectorBundlesPullback p g hX hY).map
          ((frobeniusColimitVectComparisonPullbackIso p h hY hW).inv.app x) =
      (frobeniusColimitVectComparison X p hX).map
          ((OneGeneratorSquare.colimVectPullbackComp p hX hY hW g h).hom.app x) ≫
        (frobeniusColimitVectComparisonPullbackIso p (g ≫ h) hX hW).inv.app x ≫
          (frobeniusColimitVectorBundlesPullbackComp p g h hX hY hW).inv.app
            ((frobeniusColimitVectComparison W p hW).obj x) := by
  obtain ⟨E, n⟩ := x
  have e1 := frobeniusColimitVectComparisonPullbackIso_inv_app p g hX hY
    ⟨(Scheme.Vect.pullback h).obj E, n⟩
  have e2 := frobeniusColimitVectComparisonPullbackIso_inv_app p h hY hW ⟨E, n⟩
  have e3 := frobeniusColimitVectComparisonPullbackIso_inv_app p (g ≫ h) hX hW ⟨E, n⟩
  have e4 := frobeniusColimitVectComparison_map_stageHomOf p X hX n
    ((Scheme.Vect.pullbackComp g h).hom.app E)
  have e5 := OneGeneratorSquare.colimVectPullbackComp_hom_app p hX hY hW g h E n
  have key := frobeniusStageFunctorPullbackIso_inv_comp p g h hX hY hW n E
  exact (congrArg₂ (· ≫ ·) e1 (congrArg _ e2)).trans (key.trans
    (congrArg₂ (· ≫ ·) (e4.symm.trans (congrArg _ e5.symm)) (congrArg₂ (· ≫ ·) e3.symm rfl)))

/-- The commutation of the comparison functor of Stacks Tag 0EXB with restriction along two equal
morphisms differs by the two transports along the equality. -/
lemma frobeniusColimitVectComparisonPullbackIso_inv_congr {X Y : Scheme.{u}} {m m' : X ⟶ Y}
    (h : m = m') (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (h₁ : OneGeneratorSquare.colimVectPullback p hX hY m =
      OneGeneratorSquare.colimVectPullback p hX hY m')
    (h₂ : frobeniusColimitVectorBundlesPullback p m hX hY =
      frobeniusColimitVectorBundlesPullback p m' hX hY)
    (x : frobeniusColimitVectModel Y p hY) :
    (frobeniusColimitVectComparison X p hX).map ((eqToIso h₁).hom.app x) ≫
        (frobeniusColimitVectComparisonPullbackIso p m' hX hY).inv.app x =
      (frobeniusColimitVectComparisonPullbackIso p m hX hY).inv.app x ≫
        (eqToIso h₂).hom.app ((frobeniusColimitVectComparison Y p hY).obj x) := by
  subst h
  simp

/-- The components of `AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso`, written out. -/
lemma frobeniusColimitVectorBundlesSquareIso_hom_app_eq {X X' Z E : Scheme.{u}}
    (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
    (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p)
    (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p) (hw : q ≫ b = e ≫ z)
    (M : frobeniusColimitVectorBundles X p hX) :
    (frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).hom.app M =
      (frobeniusColimitVectorBundlesPullbackComp p e z hE hZ hX).hom.app M ≫
        (eqToIso (congrArg (fun g : E ⟶ X => frobeniusColimitVectorBundlesPullback p g hE hX)
          hw.symm)).hom.app M ≫
        (frobeniusColimitVectorBundlesPullbackComp p q b hE hX' hX).inv.app M :=
  rfl

/-- A functor applied to a component of a composite of three isomorphisms, the last one
inverted. -/
lemma map_trans_trans_symm_hom_app {C D E : Type*} [Category C] [Category D] [Category E]
    (Φ : D ⥤ E) {F G H K : C ⥤ D} (α : F ≅ G) (β : G ≅ H) (γ : K ≅ H) (x : C) :
    Φ.map ((α ≪≫ β ≪≫ γ.symm).hom.app x) =
      Φ.map (α.hom.app x) ≫ Φ.map (β.hom.app x) ≫ Φ.map (γ.inv.app x) := by
  simp

/-- The pasting identity behind the cube coherence of
`AlgebraicGeometry.isEquivalence_frobeniusColimitVectorBundlesComparison_oneGeneratorSquare`,
in an arbitrary category: two composites which agree after cancelling two pairs of inverse
morphisms and moving one commutation across. -/
lemma oneGeneratorSquare_cube_aux {D : Type*} [Category D]
    {P₀ P₁ P₂ P₃ Q R T U : D} (s : P₀ ⟶ P₃) (s₁ : U ⟶ T)
    (a : P₀ ⟶ P₁) (m : P₁ ⟶ P₂) (ci : P₂ ⟶ P₃) (ch : P₃ ⟶ P₂) (pqb : P₂ ⟶ Q) (vqi : Q ⟶ T)
    (pez : P₁ ⟶ R) (vei : R ⟶ U) (veh : U ⟶ R) (evb : R ⟶ Q) (tq : P₃ ⟶ T) {V : D}
    (te₁ : P₀ ⟶ V) (te₂ : V ⟶ U)
    (hs : s = a ≫ m ≫ ci) (hs₁ : s₁ = veh ≫ evb ≫ vqi) (hc : ci ≫ ch = 𝟙 _)
    (hv : vei ≫ veh = 𝟙 _) (h₁ : tq = ch ≫ pqb ≫ vqi) (h₂ : te₁ ≫ te₂ = a ≫ pez ≫ vei)
    (h₃ : m ≫ pqb = pez ≫ evb) :
    s ≫ tq = te₁ ≫ te₂ ≫ s₁ := by
  subst hs hs₁ h₁
  rw [← Category.assoc te₁, h₂]
  simp only [Category.assoc, reassoc_of% hc, reassoc_of% hv, reassoc_of% h₃]

section Square

variable {X X' Z E : Scheme.{u}} (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
  (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p)
  (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p)

/-- **The cube coherence of the comparison functors of Stacks Tag 0EXB over a commutative
square.** For a commutative square `q ≫ b = e ≫ z` of schemes in characteristic `p`, the square
comparison on the model `colim_F Vect(-)`, carried to `colim_F 𝒪_E`-modules, followed by the
commutations of the comparison functors with restriction along the two legs through `X'`, agrees
with the commutations along the two legs through `Z` followed by the square comparison
`AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso`. -/
theorem frobeniusColimitVectComparison_square_cube (hw : q ≫ b = e ≫ z)
    (x : frobeniusColimitVectModel X p hX) :
    (frobeniusColimitVectComparison E p hE).map
        ((OneGeneratorSquare.colimVectPullbackComp p hE hZ hX e z ≪≫
          eqToIso (congrArg (OneGeneratorSquare.colimVectPullback p hE hX) hw.symm) ≪≫
          (OneGeneratorSquare.colimVectPullbackComp p hE hX' hX q b).symm).hom.app x) ≫
      (frobeniusColimitVectComparisonPullbackIso p q hE hX').inv.app
        ((OneGeneratorSquare.colimVectPullback p hX' hX b).obj x) ≫
      (frobeniusColimitVectorBundlesPullback p q hE hX').map
        ((frobeniusColimitVectComparisonPullbackIso p b hX' hX).inv.app x) =
    (frobeniusColimitVectComparisonPullbackIso p e hE hZ).inv.app
        ((OneGeneratorSquare.colimVectPullback p hZ hX z).obj x) ≫
      (frobeniusColimitVectorBundlesPullback p e hE hZ).map
        ((frobeniusColimitVectComparisonPullbackIso p z hZ hX).inv.app x) ≫
      (frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).hom.app
        ((frobeniusColimitVectComparison X p hX).obj x) :=
  oneGeneratorSquare_cube_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (map_trans_trans_symm_hom_app _ _ _ _ x)
    (frobeniusColimitVectorBundlesSquareIso_hom_app_eq p b z q e hX hX' hZ hE hw _)
    (by rw [← Functor.map_comp, Iso.inv_hom_id_app]; exact CategoryTheory.Functor.map_id _ _)
    (Iso.inv_hom_id_app _ _)
    (frobeniusColimitVectComparisonPullbackIso_inv_comp p q b hE hX' hX x)
    (frobeniusColimitVectComparisonPullbackIso_inv_comp p e z hE hZ hX x)
    (frobeniusColimitVectComparisonPullbackIso_inv_congr p hw.symm hE hX _ _ x)

/-- **The square of transition functors on the model `colim_F Vect(-)`** attached to a commutative
square of schemes in characteristic `p`, as a categorical commutative square. -/
def colimVectSquareCatCommSqOver (hw : q ≫ b = e ≫ z) :
    CategoricalPullback.CatCommSqOver (OneGeneratorSquare.colimVectPullback p hE hZ e)
      (OneGeneratorSquare.colimVectPullback p hE hX' q) (frobeniusColimitVectModel X p hX) where
  fst := OneGeneratorSquare.colimVectPullback p hZ hX z
  snd := OneGeneratorSquare.colimVectPullback p hX' hX b
  iso := OneGeneratorSquare.colimVectPullbackComp p hE hZ hX e z ≪≫
    eqToIso (congrArg (OneGeneratorSquare.colimVectPullback p hE hX) hw.symm) ≪≫
    (OneGeneratorSquare.colimVectPullbackComp p hE hX' hX q b).symm

/-- The structural isomorphism of `AlgebraicGeometry.colimVectSquareCatCommSqOver`. -/
lemma colimVectSquareCatCommSqOver_iso (hw : q ≫ b = e ≫ z) :
    (colimVectSquareCatCommSqOver p b z q e hX hX' hZ hE hw).iso =
      OneGeneratorSquare.colimVectPullbackComp p hE hZ hX e z ≪≫
        eqToIso (congrArg (OneGeneratorSquare.colimVectPullback p hE hX) hw.symm) ≪≫
        (OneGeneratorSquare.colimVectPullbackComp p hE hX' hX q b).symm :=
  rfl

/-- The structural isomorphism of
`AlgebraicGeometry.frobeniusColimitVectorBundlesCatCommSqOver`. -/
lemma frobeniusColimitVectorBundlesCatCommSqOver_iso (hw : q ≫ b = e ≫ z) :
    (frobeniusColimitVectorBundlesCatCommSqOver p b z q e hX hX' hZ hE hw).iso =
      frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw :=
  rfl

/-- **Transport of the equivalence of comparison functors from the model `colim_F Vect(-)` to
finite locally free `colim_F 𝒪`-modules.** For a commutative square of quasi-compact and
quasi-separated schemes in characteristic `p`, if the comparison functor of the square of
transition functors on the models is an equivalence, then so is the comparison functor
`𝒮_X ⟶ 𝒮_Z ×_{𝒮_E} 𝒮_{X'}` on finite locally free `colim_F 𝒪`-modules. -/
theorem isEquivalence_frobeniusColimitVectorBundlesComparison_of_colimVect
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace X'] [QuasiSeparatedSpace X']
    [CompactSpace Z] [QuasiSeparatedSpace Z] [CompactSpace E] [QuasiSeparatedSpace E]
    (hw : q ≫ b = e ≫ z)
    (h : ((CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback _ _ _).obj
      (colimVectSquareCatCommSqOver p b z q e hX hX' hZ hE hw)).IsEquivalence) :
    (frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw).IsEquivalence := by
  have := isEquivalence_frobeniusColimitVectComparison X p hX
  have := isEquivalence_frobeniusColimitVectComparison X' p hX'
  have := isEquivalence_frobeniusColimitVectComparison Z p hZ
  have := isEquivalence_frobeniusColimitVectComparison E p hE
  exact CategoricalPullback.CatCommSqOver.isEquivalence_of_cube
    (colimVectSquareCatCommSqOver p b z q e hX hX' hZ hE hw)
    (frobeniusColimitVectorBundlesCatCommSqOver p b z q e hX hX' hZ hE hw)
    (frobeniusColimitVectComparison X p hX) (frobeniusColimitVectComparison Z p hZ)
    (frobeniusColimitVectComparison E p hE) (frobeniusColimitVectComparison X' p hX')
    (frobeniusColimitVectComparisonPullbackIso p z hZ hX).symm
    (frobeniusColimitVectComparisonPullbackIso p b hX' hX).symm
    (frobeniusColimitVectComparisonPullbackIso p e hE hZ).symm
    (frobeniusColimitVectComparisonPullbackIso p q hE hX').symm
    (fun x => by
      rw [colimVectSquareCatCommSqOver_iso, frobeniusColimitVectorBundlesCatCommSqOver_iso,
        Iso.symm_hom, Iso.symm_hom, Iso.symm_hom, Iso.symm_hom]
      exact frobeniusColimitVectComparison_square_cube p b z q e hX hX' hZ hE hw x) h

end Square

/-- **Stacks Tag 0EXC for finite locally free `colim_F 𝒪`-modules.** Let `A` be a ring in
characteristic `p`, `f ∈ A`, and `J ⊆ A` an ideal annihilated by `f ^ n`, so that the spectra of
`A`, `A ⧸ fA`, `A ⧸ J` and `A ⧸ (J + fA)` form the almost blowup square of Example 0EVG. Then the
comparison functor `𝒮_X ⟶ 𝒮_Z ×_{𝒮_E} 𝒮_{X'}` of that square, on the categories of finite locally
free `colim_F 𝒪`-modules, is an equivalence. -/
theorem isEquivalence_frobeniusColimitVectorBundlesComparison_oneGeneratorSquare (A : Type u)
    [CommRing A] (f : A) (J : Ideal A) (n : ℕ) (hann : ∀ x ∈ J, f ^ n * x = 0)
    (hp : (p : A) = 0) :
    (frobeniusColimitVectorBundlesComparison p (Spec.map (OneGeneratorSquare.toMod A J))
      (Spec.map (OneGeneratorSquare.toCtr A f)) (Spec.map (OneGeneratorSquare.modToExc A f J))
      (Spec.map (OneGeneratorSquare.ctrToExc A f J)) (OneGeneratorSquare.charBase A p hp)
      (OneGeneratorSquare.charMod A J p hp) (OneGeneratorSquare.charCtr A f p hp)
      (OneGeneratorSquare.charExc A f J p hp)
      (OneGeneratorSquare.specMap_square A f J)).IsEquivalence := by
  have hS : colimVectCatCommSqOver A f J p hp =
      colimVectSquareCatCommSqOver p (Spec.map (OneGeneratorSquare.toMod A J))
        (Spec.map (OneGeneratorSquare.toCtr A f)) (Spec.map (OneGeneratorSquare.modToExc A f J))
        (Spec.map (OneGeneratorSquare.ctrToExc A f J)) (OneGeneratorSquare.charBase A p hp)
        (OneGeneratorSquare.charMod A J p hp) (OneGeneratorSquare.charCtr A f p hp)
        (OneGeneratorSquare.charExc A f J p hp) (OneGeneratorSquare.specMap_square A f J) := rfl
  refine isEquivalence_frobeniusColimitVectorBundlesComparison_of_colimVect p _ _ _ _ _ _ _ _ _ ?_
  rw [← hS]
  exact colimVectComparison_isEquivalence A f J n hann p hp

end AlgebraicGeometry

end
