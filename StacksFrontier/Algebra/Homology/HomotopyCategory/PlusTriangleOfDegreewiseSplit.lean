module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The triangle of a degreewise split short exact sequence of bounded below complexes

Let `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence of cochain complexes in an abelian
category which is split in every degree, with all three complexes bounded below. The
distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` of the homotopy category attached to the splitting
(`HomotopyCategory.trianglehOfDegreewiseSplit`) lies in the bounded below homotopy category, and
its image in the bounded below derived category is distinguished.

For an additive functor `F` which is exact, the right derived functor `RF` on bounded below
derived categories carries this triangle to the triangle of the image sequence, through its
derived-functor unit. More generally a morphism `ψ : F(S) ⟶ S'` of short exact sequences which
is compatible with given splittings induces a morphism of triangles from `RF` of the triangle of
`S` to the triangle of `S'`, whose components are the inverse of the unit followed by the class
of the components of `ψ`.

## Main definitions

* `CochainComplex.plusHomotopyObj`, `CochainComplex.plusDerivedObj`: a complex vanishing in
  degrees `< a`, as an object of the bounded below homotopy and derived categories.
* `CochainComplex.trianglehPlusOfDegreewiseSplit`: the triangle of a degreewise split short exact
  sequence of bounded below complexes, in the bounded below homotopy category.
* `CochainComplex.trianglehPlusOfDegreewiseSplitMap`: the morphism of triangles in the bounded
  below homotopy category induced by a morphism `F(S) ⟶ S'` compatible with the splittings.
* `CochainComplex.rightDerivedFunctorPlusTriangleOfDegreewiseSplitHom`: the morphism of triangles
  `RF(T(S)) ⟶ T(S')` in the bounded below derived category.

## Main results

* `CochainComplex.trianglehPlusOfDegreewiseSplit_distinguished`: the triangle is distinguished.
* `CochainComplex.homOfDegreewiseSplit_map_naturality`: the connecting morphism of complexes of
  a degreewise split sequence is natural in morphisms compatible with the splittings, after
  applying an additive functor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CochainComplex

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

/-- A cochain complex vanishing in degrees `< a`, as an object of the bounded below homotopy
category. -/
def plusHomotopyObj (a : ℤ) (F : CochainComplex C ℤ) [F.IsStrictlyGE a] :
    HomotopyCategory.Plus C :=
  ⟨(HomotopyCategory.quotient _ _).obj F, by
    rw [HomotopyCategory.plus_quotient_obj_iff]; exact ⟨a, inferInstance⟩⟩

/-- A cochain complex vanishing in degrees `< a`, as an object of the bounded below derived
category. -/
abbrev plusDerivedObj [HasDerivedCategory C] (a : ℤ) (F : CochainComplex C ℤ)
    [F.IsStrictlyGE a] : DerivedCategory.Plus C :=
  DerivedCategory.Plus.Qh.obj (plusHomotopyObj a F)

section Naturality

variable (F : C ⥤ D) [F.Additive] {S : ShortComplex (CochainComplex C ℤ)}
  (σ : ∀ n, (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting)
  {S' : ShortComplex (CochainComplex D ℤ)}
  (σ' : ∀ n, (S'.map (HomologicalComplex.eval D (ComplexShape.up ℤ) n)).Splitting)
  (ψ : S.map (F.mapHomologicalComplex _) ⟶ S')

/-- **The connecting morphism of complexes of a degreewise split sequence is natural** in a
morphism `ψ : F(S) ⟶ S'` of short complexes whose middle component is compatible with the
sections and the retractions of the two splittings. -/
theorem homOfDegreewiseSplit_map_naturality
    (hs : ∀ n, F.map (σ n).s ≫ ψ.τ₂.f n = ψ.τ₃.f n ≫ (σ' n).s)
    (hr : ∀ n, F.map (σ n).r ≫ ψ.τ₁.f n = ψ.τ₂.f n ≫ (σ' n).r) :
    (F.mapHomologicalComplex _).map (homOfDegreewiseSplit S σ) ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app S.X₁ ≫
          ψ.τ₁⟦(1 : ℤ)⟧' =
      ψ.τ₃ ≫ homOfDegreewiseSplit S' σ' := by
  ext n
  have hd := ψ.τ₂.comm n (n + 1)
  simp only [ShortComplex.map_X₂, Functor.mapHomologicalComplex_obj_d] at hd
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    homOfDegreewiseSplit_f, Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    shiftFunctor_map_f']
  simp only [cocycleOfDegreewiseSplit, HomComplex.Cocycle.mk_coe, HomComplex.Cochain.mk_v,
    Functor.map_comp, Category.assoc]
  refine (congrArg (fun z => F.map (σ n).s ≫ F.map (S.X₂.d n (n + 1)) ≫
    F.map (σ (n + 1)).r ≫ z) (Category.id_comp (ψ.τ₁.f (n + 1)))).trans ?_
  rw [hr, ← reassoc_of% hd, reassoc_of% hs]

/-- **The morphism of triangles of complexes induced by a morphism of degreewise split
sequences** compatible with the splittings, from `F` of the triangle of `S` to the triangle of
`S'`. -/
def triangleOfDegreewiseSplitMapHom
    (hs : ∀ n, F.map (σ n).s ≫ ψ.τ₂.f n = ψ.τ₃.f n ≫ (σ' n).s)
    (hr : ∀ n, F.map (σ n).r ≫ ψ.τ₁.f n = ψ.τ₂.f n ≫ (σ' n).r) :
    (F.mapHomologicalComplex _).mapTriangle.obj (triangleOfDegreewiseSplit S σ) ⟶
      triangleOfDegreewiseSplit S' σ' where
  hom₁ := ψ.τ₁
  hom₂ := ψ.τ₂
  hom₃ := ψ.τ₃
  comm₁ := ψ.comm₁₂.symm
  comm₂ := ψ.comm₂₃.symm
  comm₃ := (Category.assoc _ _ _).trans (homOfDegreewiseSplit_map_naturality F σ σ' ψ hs hr)

end Naturality

section Triangle

variable (a : ℤ) (S : ShortComplex (CochainComplex C ℤ))
  (σ : ∀ n, (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting)
  [S.X₁.IsStrictlyGE a] [S.X₂.IsStrictlyGE a] [S.X₃.IsStrictlyGE a]

/-- The connecting morphism of the triangle of a degreewise split short exact sequence of bounded
below complexes, in the bounded below homotopy category. -/
@[sga "4½ Etat_0 1.2.4" "special case"]
def trianglehPlusOfDegreewiseSplitδ :
    plusHomotopyObj a S.X₃ ⟶ (plusHomotopyObj a S.X₁)⟦(1 : ℤ)⟧ :=
  (HomotopyCategory.Plus.ι C).preimage
    (((HomotopyCategory.quotient _ _).map (homOfDegreewiseSplit S σ) ≫
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app S.X₁ :
          (HomotopyCategory.Plus.ι C).obj (plusHomotopyObj a S.X₃) ⟶
            ((HomotopyCategory.Plus.ι C).obj (plusHomotopyObj a S.X₁))⟦(1 : ℤ)⟧) ≫
      ((HomotopyCategory.Plus.ι C).commShiftIso (1 : ℤ)).inv.app (plusHomotopyObj a S.X₁))

omit [S.X₂.IsStrictlyGE a] in
/-- The image of `CochainComplex.trianglehPlusOfDegreewiseSplitδ` in the homotopy category,
followed by the commutation of the inclusion with the shift, is the class of
`CochainComplex.homOfDegreewiseSplit` followed by the commutation of the quotient functor with
the shift. -/
theorem ι_map_trianglehPlusOfDegreewiseSplitδ :
    (HomotopyCategory.Plus.ι C).map (trianglehPlusOfDegreewiseSplitδ a S σ) ≫
        ((HomotopyCategory.Plus.ι C).commShiftIso (1 : ℤ)).hom.app (plusHomotopyObj a S.X₁) =
      (HomotopyCategory.quotient _ _).map (homOfDegreewiseSplit S σ) ≫
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app S.X₁ := by
  rw [trianglehPlusOfDegreewiseSplitδ, Functor.map_preimage, Category.assoc,
    Iso.inv_hom_id_app]
  exact Category.comp_id _

/-- **The triangle of a degreewise split short exact sequence of bounded below complexes**, in
the bounded below homotopy category: the triangle `CochainComplex.trianglehOfDegreewiseSplit`
read in the full subcategory. -/
def trianglehPlusOfDegreewiseSplit : Triangle (HomotopyCategory.Plus C) :=
  Triangle.mk
    (ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map S.f) :
      plusHomotopyObj a S.X₁ ⟶ plusHomotopyObj a S.X₂)
    (ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map S.g) :
      plusHomotopyObj a S.X₂ ⟶ plusHomotopyObj a S.X₃)
    (trianglehPlusOfDegreewiseSplitδ a S σ)

/-- The image of `trianglehPlusOfDegreewiseSplit` in the homotopy category is the triangle of
the degreewise split sequence. -/
def trianglehPlusOfDegreewiseSplitιIso :
    (HomotopyCategory.Plus.ι C).mapTriangle.obj (trianglehPlusOfDegreewiseSplit a S σ) ≅
      trianglehOfDegreewiseSplit S σ :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((congrArg (fun z => _ ≫ z) (CategoryTheory.Functor.map_id _ _)).trans
      ((Category.comp_id _).trans
        ((ι_map_trianglehPlusOfDegreewiseSplitδ a S σ).trans (Category.id_comp _).symm)))

/-- **The triangle of a degreewise split short exact sequence of bounded below complexes is
distinguished** in the bounded below homotopy category. -/
theorem trianglehPlusOfDegreewiseSplit_distinguished :
    trianglehPlusOfDegreewiseSplit a S σ ∈ distTriang _ :=
  isomorphic_distinguished _ (trianglehOfDegreewiseSplit_distinguished S σ) _
    (trianglehPlusOfDegreewiseSplitιIso a S σ)

end Triangle

section Map

variable (F : C ⥤ D) [F.Additive] (a : ℤ) {S : ShortComplex (CochainComplex C ℤ)}
  (σ : ∀ n, (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting)
  [S.X₁.IsStrictlyGE a] [S.X₂.IsStrictlyGE a] [S.X₃.IsStrictlyGE a]
  {S' : ShortComplex (CochainComplex D ℤ)}
  (σ' : ∀ n, (S'.map (HomologicalComplex.eval D (ComplexShape.up ℤ) n)).Splitting)
  [S'.X₁.IsStrictlyGE a] [S'.X₂.IsStrictlyGE a] [S'.X₃.IsStrictlyGE a]
  (ψ : S.map (F.mapHomologicalComplex _) ⟶ S')
  (hs : ∀ n, F.map (σ n).s ≫ ψ.τ₂.f n = ψ.τ₃.f n ≫ (σ' n).s)
  (hr : ∀ n, F.map (σ n).r ≫ ψ.τ₁.f n = ψ.τ₂.f n ≫ (σ' n).r)

/-- The class `F(X) ⟶ X'` of a map of bounded below complexes, as a morphism out of the image
under `F` in the bounded below homotopy category. -/
abbrev plusHomotopyMapHom {X : CochainComplex C ℤ} [X.IsStrictlyGE a] {X' : CochainComplex D ℤ}
    [X'.IsStrictlyGE a] (φ : (F.mapHomologicalComplex _).obj X ⟶ X') :
    F.mapHomotopyCategoryPlus.obj (plusHomotopyObj a X) ⟶ plusHomotopyObj a X' :=
  ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map φ)

private theorem δ_chain {𝒳 : Type*} [Category* 𝒳]
    {o₀ o₁ o₂ o₃ o₄ o₅ o₆ o₇ o₈ o₉ o₁₀ : 𝒳} {A : o₀ ⟶ o₁} {C : o₁ ⟶ o₄} {E1 : o₁ ⟶ o₁}
    {B : o₁ ⟶ o₃} {E2 : o₃ ⟶ o₃} {B₁ : o₁ ⟶ o₂} {B₂ : o₂ ⟶ o₃} {Binv : o₃ ⟶ o₄}
    {Bh : o₄ ⟶ o₃} {H1 : o₃ ⟶ o₅} {Q1 : o₀ ⟶ o₆} {Q2 : o₆ ⟶ o₂} {I1 : o₃ ⟶ o₃} {I2 : o₆ ⟶ o₆}
    {R1 : o₆ ⟶ o₇} {R2 : o₇ ⟶ o₃} {P1 : o₇ ⟶ o₈} {P2 : o₈ ⟶ o₅} {Ψ : o₀ ⟶ o₉}
    {Hh' : o₉ ⟶ o₈} {D' : o₉ ⟶ o₁₀} {Dh : o₁₀ ⟶ o₅}
    (hC : C = E1 ≫ B ≫ E2 ≫ Binv) (hE1 : E1 = 𝟙 _) (hE2 : E2 = 𝟙 _) (hBB : Binv ≫ Bh = 𝟙 _)
    (hB : B = B₁ ≫ B₂) (hAB : A ≫ B₁ = Q1 ≫ Q2) (hQB : (Q2 ≫ B₂) ≫ I1 = I2 ≫ R1 ≫ R2)
    (hI1 : I1 = 𝟙 _) (hI2 : I2 = 𝟙 _) (hRH : R2 ≫ H1 = P1 ≫ P2)
    (hQRP : Q1 ≫ R1 ≫ P1 = Ψ ≫ Hh') (hD : D' ≫ Dh = Hh' ≫ P2) :
    A ≫ C ≫ Bh ≫ H1 = Ψ ≫ D' ≫ Dh := by
  rw [hI1, hI2, Category.comp_id, Category.id_comp] at hQB
  rw [hD, hC, hE1, hE2]
  simp only [Category.assoc, Category.id_comp]
  rw [reassoc_of% hBB, hB, Category.assoc, reassoc_of% hAB, reassoc_of% hQB, hRH,
    ← reassoc_of% hQRP]

omit [S.X₂.IsStrictlyGE a] [S'.X₂.IsStrictlyGE a] in
include hs hr in
/-- The square of connecting morphisms of `CochainComplex.trianglehPlusOfDegreewiseSplitMap`. -/
theorem map_trianglehPlusOfDegreewiseSplitδ_comm :
    (F.mapHomotopyCategoryPlus.map (trianglehPlusOfDegreewiseSplitδ a S σ) ≫
        (F.mapHomotopyCategoryPlus.commShiftIso (1 : ℤ)).hom.app (plusHomotopyObj a S.X₁)) ≫
      (plusHomotopyMapHom F a ψ.τ₁)⟦(1 : ℤ)⟧' =
    plusHomotopyMapHom F a ψ.τ₃ ≫ trianglehPlusOfDegreewiseSplitδ a S' σ' := by
  apply (HomotopyCategory.Plus.ι D).map_injective
  rw [← cancel_mono (((HomotopyCategory.Plus.ι D).commShiftIso (1 : ℤ)).hom.app
    (plusHomotopyObj a S'.X₁))]
  have h1 := ((HomotopyCategory.Plus.ι D).commShiftIso (1 : ℤ)).hom.naturality
    (plusHomotopyMapHom F a ψ.τ₁)
  have h2 := Functor.CommShift.OfComp.map_iso_hom_app ((HomotopyCategory.plus D).liftCompιIso
    (HomotopyCategory.Plus.ι C ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ))
    (fun X => (F.mapHomotopyCategoryPlus.obj X).2)) (1 : ℤ) (plusHomotopyObj a S.X₁)
  have h4 := NatTrans.shift_app_comm (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom
    (1 : ℤ) S.X₁
  have h5 := ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.naturality
    ψ.τ₁
  have h6 := homOfDegreewiseSplit_map_naturality F σ σ' ψ hs hr
  have h3 := ι_map_trianglehPlusOfDegreewiseSplitδ a S σ
  have h3' := ι_map_trianglehPlusOfDegreewiseSplitδ a S' σ'
  simp only [Functor.commShiftIso_comp_hom_app, Functor.mapHomotopyCategoryFactors,
    Quotient.lift.isLift_hom] at h4
  simp only [Functor.comp_map] at h1
  simp only [Functor.map_comp, Category.assoc]
  rw [h1]
  exact δ_chain h2 rfl (CategoryTheory.Functor.map_id _ _) (Iso.inv_hom_id_app _ _)
    (Functor.commShiftIso_comp_hom_app _ _ _ _)
    ((Functor.map_comp _ _ _).symm.trans ((congrArg (F.mapHomotopyCategory _).map h3).trans
      (Functor.map_comp _ _ _))) h4 (CategoryTheory.Functor.map_id _ _) rfl h5.symm
    (by
      refine Eq.trans ?_ ((congrArg (HomotopyCategory.quotient D _).map h6).trans
        ((HomotopyCategory.quotient D _).map_comp _ _))
      simp only [Functor.map_comp]
      rfl) h3'


/-- **The morphism of triangles of the bounded below homotopy category induced by a morphism of
degreewise split sequences** compatible with the splittings. -/
def trianglehPlusOfDegreewiseSplitMap :
    F.mapHomotopyCategoryPlus.mapTriangle.obj (trianglehPlusOfDegreewiseSplit a S σ) ⟶
      trianglehPlusOfDegreewiseSplit a S' σ' where
  hom₁ := plusHomotopyMapHom F a ψ.τ₁
  hom₂ := plusHomotopyMapHom F a ψ.τ₂
  hom₃ := plusHomotopyMapHom F a ψ.τ₃
  comm₁ := by
    ext
    exact ((HomotopyCategory.quotient _ _).map_comp _ _).symm.trans
      ((congrArg (HomotopyCategory.quotient _ _).map ψ.comm₁₂.symm).trans
        ((HomotopyCategory.quotient _ _).map_comp _ _))
  comm₂ := by
    ext
    exact ((HomotopyCategory.quotient _ _).map_comp _ _).symm.trans
      ((congrArg (HomotopyCategory.quotient _ _).map ψ.comm₂₃.symm).trans
        ((HomotopyCategory.quotient _ _).map_comp _ _))
  comm₃ := map_trianglehPlusOfDegreewiseSplitδ_comm F a σ σ' ψ hs hr

end Map

section Derived

variable [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

attribute [local instance] Functor.commShiftRightDerivedFunctorPlus

variable (F : C ⥤ D) [F.Additive] [IsIso F.rightDerivedFunctorPlusUnith] (a : ℤ)
  {S : ShortComplex (CochainComplex C ℤ)}
  (σ : ∀ n, (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting)
  [S.X₁.IsStrictlyGE a] [S.X₂.IsStrictlyGE a] [S.X₃.IsStrictlyGE a]
  {S' : ShortComplex (CochainComplex D ℤ)}
  (σ' : ∀ n, (S'.map (HomologicalComplex.eval D (ComplexShape.up ℤ) n)).Splitting)
  [S'.X₁.IsStrictlyGE a] [S'.X₂.IsStrictlyGE a] [S'.X₃.IsStrictlyGE a]
  (ψ : S.map (F.mapHomologicalComplex _) ⟶ S')
  (hs : ∀ n, F.map (σ n).s ≫ ψ.τ₂.f n = ψ.τ₃.f n ≫ (σ' n).s)
  (hr : ∀ n, F.map (σ n).r ≫ ψ.τ₁.f n = ψ.τ₂.f n ≫ (σ' n).r)

/-- **The morphism of triangles `RF(T(S)) ⟶ T(S')` of the bounded below derived category**
induced by a morphism `F(S) ⟶ S'` of degreewise split sequences compatible with the splittings,
when the derived-functor unit of `RF` is invertible (as it is for an exact functor): the inverse
of the unit followed by the class of the morphism of triangles of
`CochainComplex.trianglehPlusOfDegreewiseSplitMap`. -/
def rightDerivedFunctorPlusTriangleOfDegreewiseSplitHom :
    F.rightDerivedFunctorPlus.mapTriangle.obj
        (DerivedCategory.Plus.Qh.mapTriangle.obj (trianglehPlusOfDegreewiseSplit a S σ)) ⟶
      DerivedCategory.Plus.Qh.mapTriangle.obj (trianglehPlusOfDegreewiseSplit a S' σ') :=
  letI : NatTrans.CommShift (asIso F.rightDerivedFunctorPlusUnith).hom ℤ :=
    Functor.natTransCommShiftRightDerivedFunctorPlusUnit F
  (Functor.mapTriangleCompIso DerivedCategory.Plus.Qh F.rightDerivedFunctorPlus).inv.app _ ≫
    (Functor.mapTriangleIso (asIso F.rightDerivedFunctorPlusUnith)).inv.app _ ≫
      (Functor.mapTriangleCompIso F.mapHomotopyCategoryPlus DerivedCategory.Plus.Qh).hom.app _ ≫
        DerivedCategory.Plus.Qh.mapTriangle.map (trianglehPlusOfDegreewiseSplitMap F a σ σ' ψ hs hr)

/-- The first and third components of the derived morphism of triangles. -/
private theorem rightDerivedFunctorPlusTriangleOfDegreewiseSplitHom_hom₁_and_hom₃ :
    (rightDerivedFunctorPlusTriangleOfDegreewiseSplitHom F a σ σ' ψ hs hr).hom₁ =
      (asIso F.rightDerivedFunctorPlusUnith).inv.app (plusHomotopyObj a S.X₁) ≫
        DerivedCategory.Plus.Qh.map (plusHomotopyMapHom F a ψ.τ₁) ∧
    (rightDerivedFunctorPlusTriangleOfDegreewiseSplitHom F a σ σ' ψ hs hr).hom₃ =
      (asIso F.rightDerivedFunctorPlusUnith).inv.app (plusHomotopyObj a S.X₃) ≫
        DerivedCategory.Plus.Qh.map (plusHomotopyMapHom F a ψ.τ₃) := by
  simp only [trianglehPlusOfDegreewiseSplit, rightDerivedFunctorPlusTriangleOfDegreewiseSplitHom,
    Functor.mapTriangleCompIso, Triangle.isoMk, Functor.comp_obj, Triangle.homMk, Iso.refl_hom,
    Iso.refl_inv, NatIso.ofComponents_inv_app, Functor.mapTriangleIso, Iso.app_hom, asIso_hom,
    Iso.app_inv, asIso_inv, NatIso.isIso_inv_app, Triangle.mk_obj₁, Triangle.mk_obj₂,
    Triangle.mk_obj₃, NatIso.ofComponents_hom_app, trianglehPlusOfDegreewiseSplitMap,
    triangleCategory_comp, TriangleMorphism.comp_hom₁, Functor.mapTriangle_map_hom₁,
    TriangleMorphism.comp_hom₃, Functor.mapTriangle_map_hom₃]
  constructor <;> exact (Category.id_comp _).trans (congrArg (_ ≫ ·) (Category.id_comp _))

/-- The first component of `CochainComplex.rightDerivedFunctorPlusTriangleOfDegreewiseSplitHom`
is the inverse of the derived-functor unit at `S.X₁` followed by the class of `ψ.τ₁`. -/
theorem rightDerivedFunctorPlusTriangleOfDegreewiseSplitHom_hom₁ :
    (rightDerivedFunctorPlusTriangleOfDegreewiseSplitHom F a σ σ' ψ hs hr).hom₁ =
      (asIso F.rightDerivedFunctorPlusUnith).inv.app (plusHomotopyObj a S.X₁) ≫
        DerivedCategory.Plus.Qh.map (plusHomotopyMapHom F a ψ.τ₁) :=
  (rightDerivedFunctorPlusTriangleOfDegreewiseSplitHom_hom₁_and_hom₃ F a σ σ' ψ hs hr).1

/-- The third component of `CochainComplex.rightDerivedFunctorPlusTriangleOfDegreewiseSplitHom`
is the inverse of the derived-functor unit at `S.X₃` followed by the class of `ψ.τ₃`. -/
theorem rightDerivedFunctorPlusTriangleOfDegreewiseSplitHom_hom₃ :
    (rightDerivedFunctorPlusTriangleOfDegreewiseSplitHom F a σ σ' ψ hs hr).hom₃ =
      (asIso F.rightDerivedFunctorPlusUnith).inv.app (plusHomotopyObj a S.X₃) ≫
        DerivedCategory.Plus.Qh.map (plusHomotopyMapHom F a ψ.τ₃) :=
  (rightDerivedFunctorPlusTriangleOfDegreewiseSplitHom_hom₁_and_hom₃ F a σ σ' ψ hs hr).2

end Derived

end CochainComplex
