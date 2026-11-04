module

public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredComplexSpectralSequence.PushforwardFirstDifferential
public import StacksFrontier.Algebra.Homology.DerivedCategory.TriangleOfSESDerivedComparison
public import StacksFrontier.Algebra.Homology.TriangleOfSESHomology
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift

/-!
# The first differential of the relative spectral sequence, in the derived category

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, `Rf_*` the total right derived
functor of the pushforward, `K` a filtered complex of `𝒪_X`-modules and `J` a filtered
K-injective resolution of `K`. The first differential of the spectral sequence of `f_*J` is the
connecting morphism, in the cohomology of `f_*` of the graded pieces of `J`, of `f_*` of
`0 ⟶ gr^{p + 1}J ⟶ F^pJ/F^{p + 2}J ⟶ gr^pJ ⟶ 0`
(`Stacks.Cohomology.FilteredComplex.pushforwardSpectralSequence_d`). This file shows that it is
`R^nf_*` of the connecting morphism of the distinguished triangle of
`0 ⟶ gr^{p + 1}K ⟶ F^pK/F^{p + 2}K ⟶ gr^pK ⟶ 0` in the derived category: a description that
does not involve the resolution.

## Main definitions

* `CochainComplex.Filtered.derivedGrConnecting`: for a functor `G` of derived categories commuting
  with the shift, `H^n(G(gr^pM)) ⟶ H^{n + 1}(G(gr^{p + 1}M))` induced by `G` of the connecting
  morphism `gr^pM ⟶ gr^{p + 1}M[1]` in the derived category.
* `Stacks.Cohomology.FilteredComplex.derivedPushforward`: the total right derived functor `Rf_*`.
* `Stacks.Cohomology.FilteredComplex.pushforwardDerivedComparison`: the comparison
  `Q ∘ f_* ⟶ Rf_* ∘ Q` of functors on cochain complexes, from the unit of `Rf_*`; it commutes
  with the shift.
* `Stacks.Cohomology.FilteredComplex.higherDirectImageGrConnecting`: `derivedGrConnecting` at
  `Rf_*`, a map `R^nf_*gr^pK ⟶ R^{n + 1}f_*gr^{p + 1}K`.
* `Stacks.Cohomology.FilteredComplex.pushforwardGrHomologyIso`: for a filtered K-injective
  resolution `J` of `K`, `H^n(f_*gr^pJ) ≅ R^nf_*gr^pK`.

## Main results

* `CochainComplex.Filtered.derivedGrConnecting_naturality`: naturality in the filtered complex.
* `CochainComplex.Filtered.shortExact_δ_comp_natTrans`: the snake connecting morphism of `H` of
  the graded short exact sequence is `derivedGrConnecting`, through a comparison
  `Q ∘ H ⟶ G ∘ Q` commuting with the shift.
* `Stacks.Cohomology.FilteredComplex.pushforward_grConnecting`: the connecting morphism of
  `f_*` of the short exact sequence of `J` is `higherDirectImageGrConnecting`, read through
  `pushforwardGrHomologyIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

attribute [local instance 2000] HasDerivedCategory.standard

/-! ### The derived connecting morphism of the graded pieces, for any functor -/

namespace CochainComplex.Filtered

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
  (G : DerivedCategory C ⥤ DerivedCategory D) [G.CommShift ℤ]

/-- **`H^n` of `G` of the connecting morphism of the graded pieces**: for a filtered complex `M`
and `n + 1 = n'`, the map `H^n(G(gr^pM)) ⟶ H^{n'}(G(gr^{p + 1}M))` induced by `G` of the
connecting morphism `gr^pM ⟶ gr^{p + 1}M[1]` of the distinguished triangle of
`0 ⟶ gr^{p + 1}M ⟶ F^pM/F^{p + 2}M ⟶ gr^pM ⟶ 0`. -/
def derivedGrConnecting (M : Filtered C) (p n n' : ℤ) (h : n + 1 = n') :
    (DerivedCategory.homologyFunctor D n).obj
        (G.obj (DerivedCategory.Q.obj ((FilteredObject.gr p).obj M))) ⟶
      (DerivedCategory.homologyFunctor D n').obj
        (G.obj (DerivedCategory.Q.obj ((FilteredObject.gr (p + 1)).obj M))) :=
  (DerivedCategory.homologyFunctor D 0).shiftMap
    (G.map (DerivedCategory.triangleOfSESδ (M.grShortComplex_shortExact p)) ≫
      (G.commShiftIso (1 : ℤ)).hom.app _) n n' (by omega)

/-- `shiftMap` turns a commuting square with vertical maps `g⟦1⟧'` and `f` into a commuting
square. -/
private theorem shiftMap_comp_eq_comp_shiftMap {A : Type*} [Category* A] {E : Type*} [Category* E]
    [HasShift E ℤ] (F : E ⥤ A) [F.ShiftSequence ℤ] {X Y X' Y' : E} (a : X ⟶ Y⟦(1 : ℤ)⟧)
    (g : Y ⟶ Y') (f : X ⟶ X') (b : X' ⟶ Y'⟦(1 : ℤ)⟧) (h : a ≫ g⟦(1 : ℤ)⟧' = f ≫ b)
    (n n' : ℤ) (hn : 1 + n = n') :
    F.shiftMap a n n' hn ≫ (F.shift n').map g = (F.shift n).map f ≫ F.shiftMap b n n' hn := by
  rw [← F.shiftMap_comp, ← F.shiftMap_comp', h]

/-- `derivedGrConnecting` is natural in the filtered complex. -/
theorem derivedGrConnecting_naturality {M N : Filtered C} (φ : M ⟶ N) (p n n' : ℤ)
    (h : n + 1 = n') :
    derivedGrConnecting G M p n n' h ≫ (DerivedCategory.homologyFunctor D n').map
        (G.map (DerivedCategory.Q.map ((FilteredObject.gr (p + 1)).map φ))) =
      (DerivedCategory.homologyFunctor D n).map
          (G.map (DerivedCategory.Q.map ((FilteredObject.gr p).map φ))) ≫
        derivedGrConnecting G N p n n' h := by
  have hnat := DerivedCategory.triangleOfSESδ_naturality (M.grShortComplex_shortExact p)
    (N.grShortComplex_shortExact p) (grShortComplexMap φ p)
  have hG : G.map (DerivedCategory.triangleOfSESδ (M.grShortComplex_shortExact p)) ≫
        (G.commShiftIso (1 : ℤ)).hom.app _ ≫
        (G.map (DerivedCategory.Q.map ((FilteredObject.gr (p + 1)).map φ)))⟦(1 : ℤ)⟧' =
      G.map (DerivedCategory.Q.map ((FilteredObject.gr p).map φ)) ≫
        G.map (DerivedCategory.triangleOfSESδ (N.grShortComplex_shortExact p)) ≫
        (G.commShiftIso (1 : ℤ)).hom.app _ := by
    rw [← Functor.commShiftIso_hom_naturality, ← Functor.map_comp_assoc,
      ← Functor.map_comp_assoc]
    exact congrArg (fun x => G.map x ≫ _) hnat
  show (DerivedCategory.homologyFunctor D 0).shiftMap _ n n' _ ≫
      ((DerivedCategory.homologyFunctor D 0).shift n').map
        (G.map (DerivedCategory.Q.map ((FilteredObject.gr (p + 1)).map φ))) =
    ((DerivedCategory.homologyFunctor D 0).shift n).map
        (G.map (DerivedCategory.Q.map ((FilteredObject.gr p).map φ))) ≫
      (DerivedCategory.homologyFunctor D 0).shiftMap _ n n' _
  exact shiftMap_comp_eq_comp_shiftMap _ _ _ _ _ ((Category.assoc _ _ _).trans hG) _ _ _

/-- **The snake connecting morphism of `H` applied to the graded short exact sequence is
`derivedGrConnecting`**, read through a comparison `σ : Q ∘ H ⟶ G ∘ Q` commuting with the
shift, for `H` additive and `H` of the graded short exact sequence of `M` short exact. -/
theorem shortExact_δ_comp_natTrans (H : C ⥤ D)
    [H.Additive]
    (σ : H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ G) [NatTrans.CommShift σ ℤ] (M : Filtered C) (p n n' : ℤ)
    (h : n + 1 = n')
    (hΨS : ((M.grShortComplex p).map (H.mapHomologicalComplex (ComplexShape.up ℤ))).ShortExact) :
    hΨS.δ n n' (by simp; omega) ≫
        (DerivedCategory.homologyFunctorFactors D n').inv.app _ ≫
          (DerivedCategory.homologyFunctor D n').map (σ.app (M.grShortComplex p).X₁) =
      (DerivedCategory.homologyFunctorFactors D n).inv.app _ ≫
        (DerivedCategory.homologyFunctor D n).map (σ.app (M.grShortComplex p).X₃) ≫
          derivedGrConnecting G M p n n' h := by
  have hsnake := DerivedCategory.homologySequenceδ_triangleOfSES hΨS n n' (by simp; omega)
  have hsq := DerivedCategory.triangleOfSESδ_comp_natTrans_map_of_mapHomologicalComplex G
    (M.grShortComplex_shortExact p) H σ hΨS
  have hsnake' : hΨS.δ n n' (by simp; omega) ≫
      (DerivedCategory.homologyFunctorFactors D n').inv.app _ =
      (DerivedCategory.homologyFunctorFactors D n).inv.app _ ≫
        DerivedCategory.HomologySequence.δ (DerivedCategory.triangleOfSES hΨS) n n'
          (by omega) :=
    (Iso.comp_inv_eq ((DerivedCategory.homologyFunctorFactors D n').app _)).mpr
      (((Iso.eq_inv_comp ((DerivedCategory.homologyFunctorFactors D n).app _)).mpr hsnake).trans
        (Category.assoc _ _ _).symm)
  have hδ : DerivedCategory.HomologySequence.δ (DerivedCategory.triangleOfSES hΨS) n n'
        (by omega) ≫
        (DerivedCategory.homologyFunctor D n').map (σ.app (M.grShortComplex p).X₁) =
      (DerivedCategory.homologyFunctor D n).map (σ.app (M.grShortComplex p).X₃) ≫
        derivedGrConnecting G M p n n' h :=
    shiftMap_comp_eq_comp_shiftMap _ _ _ _ _ hsq n n' (by omega)
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hsnake')).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hδ))

end CochainComplex.Filtered

namespace Stacks.Cohomology.FilteredComplex

attribute [local instance] modulePushforward_isRightAdjoint

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The total right derived functor `Rf_*` of the pushforward along `f`. -/
abbrev derivedPushforward :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) :=
  (homotopyPushforward f).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))

/-- The derived-functor unit of `derivedPushforward`. -/
abbrev derivedPushforwardUnit :
    homotopyPushforward f ⟶ DerivedCategory.Qh ⋙ derivedPushforward f :=
  (homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))

/-- **The comparison `Q ∘ f_* ⟶ Rf_* ∘ Q`** on cochain complexes of `𝒪_X`-modules: the unit of
`Rf_*`, read on cochain complexes through `DerivedCategory.quotientCompQhIso` and
`Functor.mapHomotopyCategoryFactors`. -/
def pushforwardDerivedComparison :
    pushforwardComplexFunctor f ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ derivedPushforward f :=
  Functor.whiskerLeft (pushforwardComplexFunctor f)
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing Y))).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight ((modulePushforward f).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      (HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
      (derivedPushforwardUnit f) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).hom
      (derivedPushforward f)

/-- The comparison `pushforwardDerivedComparison f` commutes with the shifts by `ℤ`. -/
instance : NatTrans.CommShift (pushforwardDerivedComparison f) ℤ := by
  dsimp only [pushforwardDerivedComparison]
  infer_instance

/-- The comparison of the cohomology of `f_*K` with `R^nf_*K`
(`pushforwardToHigherDirectImage`) is the cohomology of `pushforwardDerivedComparison`. -/
lemma pushforwardToHigherDirectImage_app_eq
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (n : ℤ) :
    (pushforwardToHigherDirectImage f (derivedPushforward f) (derivedPushforwardUnit f) n).app K =
      (DerivedCategory.homologyFunctorFactors _ n).inv.app ((pushforwardComplexFunctor f).obj K) ≫
        (DerivedCategory.homologyFunctor _ n).map ((pushforwardDerivedComparison f).app K) := by
  simp only [pushforwardToHigherDirectImage, pushforwardDerivedComparison, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.comp_obj, Functor.comp_map,
    DerivedCategory.homologyFunctorFactorsh_inv_app_quotient_obj, Functor.map_comp,
    Functor.map_id, Category.id_comp, Category.assoc, Iso.inv_hom_id_app_assoc]

/-- **`R^nf_*` of the connecting morphism of the graded pieces**: for a filtered complex `K`, the
map `R^nf_*gr^pK ⟶ R^{n'}f_*gr^{p + 1}K`, `n + 1 = n'`, induced by the connecting morphism
`gr^pK ⟶ gr^{p + 1}K[1]` of the distinguished triangle of
`0 ⟶ gr^{p + 1}K ⟶ F^pK/F^{p + 2}K ⟶ gr^pK ⟶ 0` in the derived category
(`CochainComplex.Filtered.derivedGrConnecting` at `Rf_*`). -/
abbrev higherDirectImageGrConnecting
    (K : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))) (p n n' : ℤ)
    (h : n + 1 = n') :
    higherDirectImage (derivedPushforward f) ((FilteredObject.gr p).obj K) n ⟶
      higherDirectImage (derivedPushforward f) ((FilteredObject.gr (p + 1)).obj K) n' :=
  CochainComplex.Filtered.derivedGrConnecting (derivedPushforward f) K p n n' h

/-- `H^n(f_*gr^pJ) ≅ R^nf_*gr^pK` for a filtered K-injective resolution `J` of `K`: the cohomology
of `f_*` of the K-injective complex `gr^pJ` is `R^nf_*gr^pJ`, which is `R^nf_*gr^pK` through the
quasi-isomorphism `gr^pK ⟶ gr^pJ`. -/
def pushforwardGrHomologyIso
    {K : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))}
    (R : FilteredKInjectiveResolution X K) (p n : ℤ) :
    ((pushforwardComplexFunctor f).obj ((FilteredObject.gr p).obj R.obj)).homology n ≅
      higherDirectImage (derivedPushforward f) ((FilteredObject.gr p).obj K) n :=
  have := R.isKInjective_gr p
  have := R.quasiIso_gr p
  (higherDirectImageIsoPushforwardHomology f (derivedPushforward f) (derivedPushforwardUnit f)
      ((FilteredObject.gr p).obj R.obj) n).symm ≪≫
    ((DerivedCategory.homologyFunctor _ n).mapIso ((derivedPushforward f).mapIso
      (asIso (DerivedCategory.Q.map ((FilteredObject.gr p).map R.map))))).symm

/-- `pushforwardGrHomologyIso` followed by `R^nf_*` of the quasi-isomorphism `gr^pK ⟶ gr^pJ` is
the comparison `pushforwardToHigherDirectImage` at `gr^pJ`. -/
@[reassoc]
lemma pushforwardGrHomologyIso_hom_comp
    {K : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))}
    (R : FilteredKInjectiveResolution X K) (p n : ℤ) :
    (pushforwardGrHomologyIso f R p n).hom ≫
        higherDirectImageMap (derivedPushforward f) ((FilteredObject.gr p).map R.map) n =
      (pushforwardToHigherDirectImage f (derivedPushforward f) (derivedPushforwardUnit f) n).app
        ((FilteredObject.gr p).obj R.obj) := by
  have := R.quasiIso_gr p
  have := R.isKInjective_gr p
  simp only [pushforwardGrHomologyIso, higherDirectImageIsoPushforwardHomology, Iso.trans_hom,
    Iso.symm_hom, Iso.symm_inv, asIso_hom, Functor.mapIso_inv, asIso_inv, Category.assoc,
    higherDirectImageMap, ← Functor.map_comp, IsIso.inv_hom_id, Functor.map_id,
    Category.comp_id, Iso.symm_symm_eq]
  exact (congrArg (_ ≫ ·) ((congrArg (DerivedCategory.homologyFunctor _ n).map
    ((derivedPushforward f).map_id _)).trans (CategoryTheory.Functor.map_id _ _))).trans
    (Category.comp_id _)

/-- **The connecting morphism of `f_*` of the graded short exact sequence of a resolution is
`R^nf_*` of the derived connecting morphism of the graded pieces**: for a filtered K-injective
resolution `J` of `K`, the connecting morphism `H^n(f_*gr^pJ) ⟶ H^{n'}(f_*gr^{p + 1}J)` of
`f_*(0 ⟶ gr^{p + 1}J ⟶ F^pJ/F^{p + 2}J ⟶ gr^pJ ⟶ 0)` is `higherDirectImageGrConnecting`, read
through `pushforwardGrHomologyIso`. -/
theorem pushforward_grConnecting
    {K : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))}
    (R : FilteredKInjectiveResolution X K) (p n n' : ℤ) (h : n + 1 = n') :
    (shortExact_pushforward_grShortComplex f R.obj R.injective_step p).δ n n'
        (by simp; omega) ≫ (pushforwardGrHomologyIso f R (p + 1) n').hom =
      (pushforwardGrHomologyIso f R p n).hom ≫ higherDirectImageGrConnecting f K p n n' h := by
  have key := CochainComplex.Filtered.shortExact_δ_comp_natTrans (derivedPushforward f)
    (modulePushforward f) (pushforwardDerivedComparison f) R.obj p n n' h
    (shortExact_pushforward_grShortComplex f R.obj R.injective_step p)
  have hnat := CochainComplex.Filtered.derivedGrConnecting_naturality (derivedPushforward f)
    R.map p n n' h
  have e₁ := pushforwardToHigherDirectImage_app_eq f ((FilteredObject.gr (p + 1)).obj R.obj) n'
  have e₃ := pushforwardToHigherDirectImage_app_eq f ((FilteredObject.gr p).obj R.obj) n
  have := R.quasiIso_gr p
  have := R.quasiIso_gr (p + 1)
  have := R.isKInjective_gr p
  have := R.isKInjective_gr (p + 1)
  rw [← cancel_mono (higherDirectImageMap (derivedPushforward f)
    ((FilteredObject.gr (p + 1)).map R.map) n'), Category.assoc, Category.assoc,
    pushforwardGrHomologyIso_hom_comp, higherDirectImageGrConnecting, hnat,
    pushforwardGrHomologyIso_hom_comp_assoc, e₁, e₃]
  exact key

end Stacks.Cohomology.FilteredComplex

end
