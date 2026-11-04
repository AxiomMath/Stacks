module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Cube.Chart
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.PullbackSectionCalculus
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.DegreewiseBaseChange

/-!
# The theorem of the cube: restriction of Čech cochains to a face

Let `j : A × A ⟶ (A × A) × A` be a face of the triple product compatible with the projection
to the third factor, and let `g` generate the pullback of `N` along `j`. Restricting a Čech
cochain of `N` over the chart `P_V` to the face, along a selection of the indices of the cover,
and dividing by `g`, gives a cochain of functions on the face over the chart
(`Stacks.Cube.faceMap`). This is linear over the ring of the chart (`Stacks.Cube.faceMap_smul`)
and commutes with the differentials (`Stacks.Cube.faceD_faceMap`).

## References

* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace Stacks.Cube

open Stacks.KunnethCech Stacks.TrivialGenerator

/-! ### Pulling sections back, additively -/

section Pullback

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)

/-- Pulling a section back, as an additive map: the unit of `f^* ⊣ f_*` followed by
restriction. -/
noncomputable def pbS (U : X.Opens) (W : Y.Opens) (h : W ≤ f ⁻¹ᵁ U) :
    Γ(M, U) →+ Γ((Scheme.Modules.pullback f).obj M, W) :=
  (((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE h).op).hom.comp
    (Stacks.Cech.pullbackSections f M U).hom

/-- `pbS f M U W h a` is the pullback of `a` restricted from `f ⁻¹ᵁ U` to `W`. -/
theorem pbS_apply (U : X.Opens) (W : Y.Opens) (h : W ≤ f ⁻¹ᵁ U) (a : Γ(M, U)) :
    pbS f M U W h a = ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE h).op
      (Stacks.Cech.pullbackSections f M U a) := rfl

/-- Restricting a pulled-back section is pulling back to the smaller open. -/
theorem pbS_res (U : X.Opens) {W W' : Y.Opens} (h : W ≤ f ⁻¹ᵁ U) (hW : W' ≤ W)
    (a : Γ(M, U)) :
    ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE hW).op (pbS f M U W h a) =
      pbS f M U W' (hW.trans h) a := by
  rw [pbS_apply, pbS_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

/-- Pulling a section back is compatible with restricting it first. -/
theorem pbS_map {U U' : X.Opens} (hU : U' ≤ U) (W : Y.Opens) (h : W ≤ f ⁻¹ᵁ U')
    (a : Γ(M, U)) :
    pbS f M U' W h (M.presheaf.map (homOfLE hU).op a) =
      pbS f M U W (h.trans (Scheme.Hom.preimage_mono f hU)) a := by
  rw [pbS_apply, Stacks.Cech.pullbackSections_map, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← op_comp]
  rfl

/-- Pulling a section back is semilinear. -/
theorem pbS_smul (U : X.Opens) (W : Y.Opens) (h : W ≤ f ⁻¹ᵁ U) (r : Γ(X, U)) (a : Γ(M, U)) :
    pbS f M U W h (r • a) = f.appLE U W h r • pbS f M U W h a := by
  rw [pbS_apply, pbS_apply, Stacks.Cech.pullbackSections_smul, Scheme.Modules.map_smul]
  rfl

end Pullback

/-! ### Division by a generator, additively -/

section Div

variable {X : Scheme.{u}} {G : X.Modules} {g : Γ(G, ⊤)} (hg : IsGen G g)

/-- Division by a generator, as an additive map. -/
noncomputable def divGenHom (O : X.Opens) : Γ(G, O) →+ Γ(X, O) :=
  AddMonoidHom.mk' (divGen hg O) (divGen_add hg O)

/-- `divGenHom hg O` sends a section `m` to `divGen hg O m`. -/
theorem divGenHom_apply (O : X.Opens) (m : Γ(G, O)) : divGenHom hg O m = divGen hg O m := rfl

end Div

/-! ### Restriction to a face, divided by a generator -/

/-- The Čech differential of a cochain `s`, evaluated at `i`, is the alternating sum of the
restrictions of the values of `s` at the faces of `i`. -/
theorem cechD_apply {X : TopCat} {I : Type*} (U : I → Opens X) (ℱ : TopCat.Presheaf Ab X)
    (p : ℕ) (s : CechCochains.Cochain U ℱ p) (i : Fin (p + 2) → I) :
    CechCochains.cechD U ℱ p s i = ∑ l : Fin (p + 2), ((-1 : ℤ) ^ (l : ℕ)) •
      CechCochains.restr ℱ (CechCochains.inter_le_omit U i l) (s (i ∘ l.succAbove)) := rfl

section FaceMap

variable {k : Type u} [Field k] {A : Over (Spec (.of k))}

attribute [local instance] faceModule

variable (N : (P A).Modules) (j : B A ⟶ P A)
  {g : Γ((Scheme.Modules.pullback j).obj N, ⊤)} (hg : IsGen _ g)

/-- Restriction of a section of `N` to the face over an open `W`, divided by the generator. -/
noncomputable def faceRes (O : (P A).Opens) (W : (B A).Opens) (h : W ≤ j ⁻¹ᵁ O) :
    Γ(N, O) →+ Γ(B A, W) :=
  (divGenHom hg W).comp (pbS j N O W h)

/-- `faceRes N j hg O W h a` is the pullback of `a` to `W`, divided by the generator `g`. -/
theorem faceRes_apply (O : (P A).Opens) (W : (B A).Opens) (h : W ≤ j ⁻¹ᵁ O) (a : Γ(N, O)) :
    faceRes N j hg O W h a = divGen hg W (pbS j N O W h a) := rfl

/-- Restricting a section of `N` before restricting it to the face gives the same function. -/
theorem faceRes_map {O O' : (P A).Opens} (hO : O' ≤ O) (W : (B A).Opens) (h : W ≤ j ⁻¹ᵁ O')
    (a : Γ(N, O)) :
    faceRes N j hg O' W h (N.presheaf.map (homOfLE hO).op a) =
      faceRes N j hg O W (h.trans (Scheme.Hom.preimage_mono j hO)) a := by
  rw [faceRes_apply, faceRes_apply, pbS_map]

/-- Restricting the function `faceRes N j hg O W h a` to `W' ≤ W` gives
`faceRes N j hg O W' _ a`. -/
theorem res_faceRes (O : (P A).Opens) {W W' : (B A).Opens} (h : W ≤ j ⁻¹ᵁ O) (hW : W' ≤ W)
    (a : Γ(N, O)) :
    res hW (faceRes N j hg O W h a) = faceRes N j hg O W' (hW.trans h) a := by
  rw [faceRes_apply, faceRes_apply, ← pbS_res j N O h hW a, divGen_map]
  rfl

/-- Restriction to the face is semilinear along `j.appLE O W h`. -/
theorem faceRes_smul (O : (P A).Opens) (W : (B A).Opens) (h : W ≤ j ⁻¹ᵁ O) (r : Γ(P A, O))
    (a : Γ(N, O)) :
    faceRes N j hg O W h (r • a) = j.appLE O W h r * faceRes N j hg O W h a := by
  rw [faceRes_apply, faceRes_apply, pbS_smul, divGen_smul]

variable {V : A.left.Opens} (hV : IsAffineOpen V) {ι : Type u} (U : ι → A.left.Opens)
  (sel : ι → ι × ι)
  (hsel : ∀ {n : ℕ} (i : Fin n → ι),
    faceOpen V U i ≤ j ⁻¹ᵁ ((PV V).ι ''ᵁ CechCochains.inter (chartCover U V) (sel ∘ i)))

/-- **The restriction of a Čech cochain of `N` over the chart to a face, divided by a
generator.** -/
noncomputable def faceMap (p : ℕ) :
    CechCochains.Cochain (chartCover U V) (chartModule N V).presheaf p →+ FaceCochain V U p where
  toFun c i := faceRes N j hg _ (faceOpen V U i) (hsel i) (c (sel ∘ i))
  map_zero' := by
    funext i
    exact map_zero (faceRes N j hg _ (faceOpen V U i) (hsel i))
  map_add' c c' := by
    funext i
    exact map_add (faceRes N j hg _ (faceOpen V U i) (hsel i)) (c (sel ∘ i)) (c' (sel ∘ i))

/-- The value of `faceMap` on a cochain `c` at `i` is the restriction to the face of the value of
`c` at `sel ∘ i`. -/
theorem faceMap_apply (p : ℕ)
    (c : CechCochains.Cochain (chartCover U V) (chartModule N V).presheaf p)
    (i : Fin (p + 1) → ι) :
    faceMap N j hg U sel hsel p c i =
      faceRes N j hg _ (faceOpen V U i) (hsel i) (c (sel ∘ i)) := rfl

include hV in
/-- Scalars of the chart act on sections of the chart module through `r`. -/
theorem faceRes_chart_smul (hj : j ≫ r A = bz A) (O' : (PV V).toScheme.Opens) (W : (B A).Opens)
    (h : W ≤ j ⁻¹ᵁ ((PV V).ι ''ᵁ O')) (a : chartRing V) (x : Γ(chartModule N V, O')) :
    faceRes N j hg ((PV V).ι ''ᵁ O') W h ((Stacks.Cech.baseRingHom (chartMap hV) O').hom a • x) =
      (bz A).appLE V W (h.trans (by
        rw [← hj, Scheme.Hom.comp_preimage]
        exact Scheme.Hom.preimage_mono j (image_le_preimage V O'))) a *
        faceRes N j hg ((PV V).ι ''ᵁ O') W h x := by
  have happ : ((PV V).ι.appIso O').inv.hom ((Stacks.Cech.baseRingHom (chartMap hV) O').hom a) =
      (Stacks.Cech.baseRingHom (chartMap hV) O').hom a := by
    rw [Scheme.Opens.ι_appIso]; rfl
  have hsm := faceRes_smul N j hg ((PV V).ι ''ᵁ O') W h
    (((PV V).ι.appIso O').inv.hom ((Stacks.Cech.baseRingHom (chartMap hV) O').hom a))
    (show Γ(N, (PV V).ι ''ᵁ O') from x)
  refine hsm.trans ?_
  congr 1
  rw [happ]
  have h1 := baseRingHom_chartMap_apply hV O' a
  have h2 := appLE_comp (r A) j (image_le_preimage V O') h a
  have h3 := appLE_congr hj
    (h.trans (Scheme.Hom.preimage_mono j (image_le_preimage V O'))) a
  exact (congrArg _ h1).trans (h2.trans h3)

include hV in
/-- **The face map is linear over the ring of the chart**, when the face lies over the second
factor. -/
theorem faceMap_smul (hj : j ≫ r A = bz A) (p : ℕ) (a : chartRing V)
    (c : CechCochains.Cochain (chartCover U V) (chartModule N V).presheaf p) :
    letI := Stacks.Cech.cochainModule (chartMap hV) (chartCover U V) (chartModule N V) p
    faceMap N j hg U sel hsel p (a • c) = a • faceMap N j hg U sel hsel p c := by
  let := Stacks.Cech.cochainModule (chartMap hV) (chartCover U V) (chartModule N V) p
  funext i
  rw [face_smul_apply]
  exact faceRes_chart_smul N j hg hV hj _ (faceOpen V U i) (hsel i) a _

/-- Restricting the face value of a section `x` to a smaller open of the face agrees with the face
value of the restriction of `x`. -/
theorem res_faceRes_map {O O' : (P A).Opens} (hO : O' ≤ O) {W W' : (B A).Opens}
    (h : W ≤ j ⁻¹ᵁ O) (h' : W' ≤ j ⁻¹ᵁ O') (hW : W' ≤ W) (x : Γ(N, O)) :
    res hW (faceRes N j hg O W h x) =
      faceRes N j hg O' W' h' (N.presheaf.map (homOfLE hO).op x) := by
  rw [faceRes_map, res_faceRes]

/-- **The face map commutes with the differentials.** -/
theorem faceD_faceMap (p : ℕ)
    (c : CechCochains.Cochain (chartCover U V) (chartModule N V).presheaf p) :
    faceD V U p (faceMap N j hg U sel hsel p c) =
      faceMap N j hg U sel hsel (p + 1) (CechCochains.cechD _ _ p c) := by
  funext i
  rw [faceD_apply, faceMap_apply _ _ _ _ _ _ _ (CechCochains.cechD _ _ p c), cechD_apply]
  refine Eq.trans ?_ (map_sum (faceRes N j hg _ (faceOpen V U i) (hsel i)) _ _).symm
  refine Finset.sum_congr rfl fun l _ => ?_
  refine Eq.trans ?_ (map_zsmul (faceRes N j hg _ (faceOpen V U i) (hsel i)) _ _).symm
  congr 1
  exact res_faceRes_map N j hg (Scheme.Hom.image_mono _
    (CechCochains.inter_le_omit _ (sel ∘ i) l)) _ _ _ _

end FaceMap

end Stacks.Cube

end
