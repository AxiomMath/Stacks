module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.StabilizerLocal
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Separated
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# The right stabiliser of a function is a closed subscheme of finite type

Let `G` be a quasi-compact, geometrically irreducible group scheme over a field `k`, `U` a
nonempty affine open of `G` satisfying Perrin's content hypothesis, and `f ∈ Γ(U)`. This file
glues the local computation of
`StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.StabilizerLocal` to an ideal sheaf `K` of
finite type on `G` representing the right stabiliser of `f`: a `T`-point `h` right-stabilises `f`
if and only if `K ≤ ker h`, i.e. `h` factors through `V(K)`
(`AlgebraicGeometry.exists_idealSheafData_rightStabilises`).

The ideal sheaf is the finite infimum of the kernels of the closed subschemes `V(J_i)` of a
finite cover of `G` by charts `V_i` carrying universal chart data, `J_i` the coordinate ideal of
the data; on `V_i` it is `J_i` itself, because every `V(J_j)` stabilises `f` and therefore kills
`J_i` on its part over `V_i`.

## Main results

* `AlgebraicGeometry.affineOpenSubschemeι` and `AlgebraicGeometry.ker_app_affineOpenSubschemeι`:
  the closed subscheme `V(J)` of an affine open and the kernel of its sections over the open.
* `AlgebraicGeometry.StabilizerChartData.rightStabilises_chartSubschemeOverι`: `V(J)` stabilises
  `f`.
* `AlgebraicGeometry.exists_idealSheafData_rightStabilises`: **H13 for one function** —
  representability of the right stabiliser by a closed subscheme of finite type.

## References

* D. Perrin, *Schémas en groupes quasi-compacts sur un corps*, thèse, I §2 and IV §1.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory TensorProduct

namespace AlgebraicGeometry

universe u

/-- The closed subscheme `V(J)` of an affine open `V` of a scheme, as a morphism to the scheme. -/
noncomputable def affineOpenSubschemeι {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)
    (J : Ideal Γ(X, V)) : Spec (CommRingCat.of (Γ(X, V) ⧸ J)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ hV.fromSpec

/-- The preimage of `V` under the closed immersion `V(J) ⟶ X` is all of `V(J)`. -/
theorem affineOpenSubschemeι_preimage {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)
    (J : Ideal Γ(X, V)) : affineOpenSubschemeι hV J ⁻¹ᵁ V = ⊤ := by
  rw [affineOpenSubschemeι, Scheme.Hom.comp_preimage, hV.fromSpec_preimage_self,
    Scheme.Hom.preimage_top]

/-- On sections, the map `Γ(X, V) ⟶ Γ(V(J), ⊤)` induced by `V(J) ⟶ X` is the quotient map
`Γ(X, V) ⟶ Γ(X, V) ⧸ J` followed by the inverse of `Scheme.ΓSpecIso`. -/
theorem affineOpenSubschemeι_appLE {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)
    (J : Ideal Γ(X, V)) (e : ⊤ ≤ affineOpenSubschemeι hV J ⁻¹ᵁ V) :
    (affineOpenSubschemeι hV J).appLE V ⊤ e =
      CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ (Scheme.ΓSpecIso _).inv := by
  have e₁ : ⊤ ≤ hV.fromSpec ⁻¹ᵁ V := hV.fromSpec_preimage_self.ge
  have e₂ : (⊤ : (Spec (CommRingCat.of (Γ(X, V) ⧸ J))).Opens) ≤
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ⁻¹ᵁ ⊤ := le_top
  have hsplit := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    hV.fromSpec V ⊤ ⊤ e₁ e₂
  have hfrom : hV.fromSpec.appLE V ⊤ e₁ = (Scheme.ΓSpecIso Γ(X, V)).inv := by
    simp only [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc,
      ← Functor.map_comp]
    convert Category.comp_id _
    exact (congrArg _ (Subsingleton.elim _ _)).trans (CategoryTheory.Functor.map_id _ _)
  have hspec : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appLE ⊤ ⊤ e₂ =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
    rw [show (Spec (CommRingCat.of (Γ(X, V) ⧸ J))).presheaf.map (homOfLE e₂).op = 𝟙 _ from
      (congrArg (Spec (CommRingCat.of (Γ(X, V) ⧸ J))).presheaf.map
        (Subsingleton.elim (homOfLE e₂).op (𝟙 _))).trans (CategoryTheory.Functor.map_id _ _)]
    exact Category.comp_id _
  calc (affineOpenSubschemeι hV J).appLE V ⊤ e
      = hV.fromSpec.appLE V ⊤ e₁ ≫
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appLE ⊤ ⊤ e₂ := hsplit.symm
    _ = (Scheme.ΓSpecIso Γ(X, V)).inv ≫
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop := by rw [hfrom, hspec]
    _ = _ := (Scheme.ΓSpecIso_inv_naturality _).symm

/-- The kernel of the map on sections over `V` induced by `V(J) ⟶ X` is `J`. -/
theorem ker_app_affineOpenSubschemeι {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)
    (J : Ideal Γ(X, V)) : RingHom.ker ((affineOpenSubschemeι hV J).app V).hom = J := by
  ext x
  have e := (affineOpenSubschemeι_preimage hV J).ge
  have hsplit : (affineOpenSubschemeι hV J).appLE V ⊤ e =
      (affineOpenSubschemeι hV J).app V ≫
        (Spec (CommRingCat.of (Γ(X, V) ⧸ J))).presheaf.map (homOfLE e).op := rfl
  have hiso : Function.Injective
      ((Spec (CommRingCat.of (Γ(X, V) ⧸ J))).presheaf.map (homOfLE e).op).hom := by
    have : (homOfLE e).op = eqToHom (by rw [affineOpenSubschemeι_preimage]) := Subsingleton.elim _ _
    rw [this]
    exact (asIso ((Spec (CommRingCat.of (Γ(X, V) ⧸ J))).presheaf.map
      (eqToHom (by rw [affineOpenSubschemeι_preimage])))).commRingCatIsoToRingEquiv.injective
  rw [RingHom.mem_ker]
  constructor
  · intro hx
    have : (affineOpenSubschemeι hV J).appLE V ⊤ e x = 0 := by
      rw [hsplit, CommRingCat.comp_apply, hx, map_zero]
    rw [affineOpenSubschemeι_appLE, CommRingCat.comp_apply] at this
    have h2 :=
      (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, V) ⧸ J))).commRingCatIsoToRingEquiv.symm.injective
      (this.trans (map_zero _).symm)
    exact Ideal.Quotient.eq_zero_iff_mem.mp h2
  · intro hx
    refine hiso ?_
    rw [map_zero, ← CommRingCat.comp_apply, ← hsplit, affineOpenSubschemeι_appLE,
      CommRingCat.comp_apply]
    change (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, V) ⧸ J))).inv.hom
      (Ideal.Quotient.mk J x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-- **An ideal sheaf which is finitely generated on an affine cover is finitely generated on every
affine open.** -/
theorem Scheme.IdealSheafData.fg_of_iSup_eq_top {X : Scheme.{u}} (K : X.IdealSheafData)
    {n : Type*} (W : n → X.affineOpens) (hW : ⨆ i, (W i : X.Opens) = ⊤)
    (hfg : ∀ i, (K.ideal (W i)).FG) (V : X.affineOpens) : (K.ideal V).FG := by
  have : ∀ x : V.1, ∃ (i : n) (r : Γ(X, V.1)) (rW : Γ(X, W i)),
      X.basicOpen r = X.basicOpen rW ∧ x.1 ∈ X.basicOpen r := by
    intro ⟨x, hxV⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hW.ge (Set.mem_univ x))
    exact ⟨i, exists_basicOpen_le_affine_inter V.2 (W i).2 _ ⟨hxV, hi⟩⟩
  choose i r rW e hxr using this
  have hspan : Ideal.span (Set.range r) = ⊤ := by
    rw [← V.2.self_le_iSup_basicOpen_iff]
    exact fun x hxV ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨_, _, rfl⟩, hxr ⟨x, hxV⟩⟩
  refine Ideal.fg_of_localizationSpan _ hspan fun ⟨_, ⟨x, rfl⟩⟩ ↦ ?_
  have hloc := V.2.isLocalization_basicOpen (r x)
  let eq := IsLocalization.algEquiv (Submonoid.powers (r x)) (Localization.Away (r x))
    Γ(X, X.basicOpen (r x))
  have hmap : (K.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away (r x))) =
      ((K.ideal V).map (X.presheaf.map (homOfLE (X.basicOpen_le (r x))).op).hom).map
        eq.symm.toRingHom := by
    rw [Ideal.map_map]
    congr 1
    ext y
    change _ = eq.symm (algebraMap Γ(X, V.1) Γ(X, X.basicOpen (r x)) y)
    rw [AlgEquiv.commutes]
  rw [hmap]
  refine Ideal.FG.map ?_ _
  let Vr : X.affineOpens := ⟨X.basicOpen (r x), V.2.basicOpen _⟩
  let Wr : X.affineOpens := ⟨X.basicOpen (rW x), (W (i x)).2.basicOpen _⟩
  have hVr : Vr ≤ V := X.basicOpen_le _
  have hWr : Wr ≤ W (i x) := X.basicOpen_le _
  have h1 : (K.ideal V).map (X.presheaf.map (homOfLE (X.basicOpen_le (r x))).op).hom =
      K.ideal Vr := K.map_ideal hVr
  rw [h1]
  have hfgW : (K.ideal Wr).FG := by
    rw [← K.map_ideal hWr]
    exact (hfg (i x)).map _
  have hgen : ∀ (A B : X.affineOpens) (hAB : A = B), (K.ideal A).FG → (K.ideal B).FG := by
    rintro A B rfl h
    exact h
  exact hgen Wr Vr (Subtype.ext (e x)).symm hfgW

section Stabilizer

variable {k : Type u} [Field k] {G T : Over (Spec (.of k))} [GrpObj G] {U V : G.left.Opens}
  {f : Γ(G.left, U)}

/-- The fibre condition on universal chart data making the local representability apply: `b` is
not nilpotent in any fibre over the chart. -/
def StabilizerChartData.IsFibrewiseNonNilpotent (D : StabilizerChartData U V f)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) : Prop :=
  letI := sectionsAlgebra G.hom U
  letI := sectionsAlgebra G.hom V
  ∀ p : PrimeSpectrum Γ(G.left, V), ¬ IsNilpotent
    (Algebra.TensorProduct.map (AlgHom.id k Γ(G.left, U))
      (IsScalarTower.toAlgHom k Γ(G.left, V) p.asIdeal.ResidueField)
      ((prodOpenTensorIso hU hV).inv D.b))

variable (hU : IsAffineOpen U) (hV : IsAffineOpen V)
  (hC : letI := sectionsAlgebra G.hom U
    ∀ (κ : Type u) [Field κ] [Algebra k κ] (z : Γ(G.left, U) ⊗[k] κ),
      z ∉ nonZeroDivisors (Γ(G.left, U) ⊗[k] κ) → IsNilpotent z)

/-- A section pulled back along `φ` vanishes if it vanishes locally on a cover of `φ ⁻¹ᵁ W`. -/
private theorem app_eq_zero_of_forall_exists_appLE_eq_zero {X Y : Scheme.{u}} (φ : X ⟶ Y)
    (W : Y.Opens) (x : Γ(Y, W))
    (h : ∀ t ∈ φ ⁻¹ᵁ W, ∃ (V' : X.Opens) (_ : t ∈ V') (hle : V' ≤ φ ⁻¹ᵁ W),
      φ.appLE W V' hle x = 0) : φ.app W x = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf _ _ _ fun t ht ↦ ?_
  obtain ⟨V', htV', hle, h0⟩ := h t ht
  refine (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hle) t htV' (φ.app W x)).symm.trans ?_
  refine Eq.trans ?_ (map_zero _).symm
  change X.presheaf.germ V' t htV' (φ.appLE W V' hle x) = 0
  rw [h0, map_zero]

include hU hV hC in
/-- A stabilising point kills the coordinate ideal of the chart data on the part of the parameter
scheme over the chart. -/
theorem StabilizerChartData.ideal_le_ker_app (D : StabilizerChartData U V f)
    (hfib : D.IsFibrewiseNonNilpotent hU hV) (φ : T ⟶ G) (hst : RightStabilises φ U f) :
    D.ideal hU hV ≤ RingHom.ker (φ.left.app V).hom := by
  intro x hx
  rw [RingHom.mem_ker]
  refine app_eq_zero_of_forall_exists_appLE_eq_zero _ _ _ fun t ht ↦ ?_
  obtain ⟨V', hV', htV', hV'le⟩ := exists_isAffineOpen_mem_and_subset ht
  have hst' := (rightStabilises_iff_forall_rightStabilisesOn φ U f).mp hst ⟨V', hV'⟩
  exact ⟨V', htV', hV'le, (D.rightStabilisesOn_iff hU hV hC hfib φ hV' hV'le).mp hst' hx⟩

include hU hV hC in
/-- Conversely, a point killing the coordinate ideal on the part over the chart stabilises on
every affine chart of the parameter scheme over the chart. -/
theorem StabilizerChartData.rightStabilisesOn_of_ideal_le_ker_app (D : StabilizerChartData U V f)
    (hfib : D.IsFibrewiseNonNilpotent hU hV) (φ : T ⟶ G)
    (hker : D.ideal hU hV ≤ RingHom.ker (φ.left.app V).hom) {V' : T.left.Opens}
    (hV' : IsAffineOpen V') (hle : V' ≤ φ.left ⁻¹ᵁ V) : RightStabilisesOn φ U V' f := by
  refine (D.rightStabilisesOn_iff hU hV hC hfib φ hV' hle).mpr fun x hx ↦ ?_
  rw [RingHom.mem_ker]
  change (φ.left.app V ≫ T.left.presheaf.map (homOfLE hle).op) x = 0
  rw [CommRingCat.comp_apply, hker hx, map_zero]

/-- The closed subscheme `V(J)` of the chart `V`, as a scheme over `Spec k`. -/
noncomputable def chartSubschemeOver (hV : IsAffineOpen V) (J : Ideal Γ(G.left, V)) :
    Over (Spec (.of k)) :=
  Over.mk (affineOpenSubschemeι hV J ≫ G.hom)

/-- The inclusion of `V(J)` into `G`, over `Spec k`. -/
noncomputable def chartSubschemeOverι (hV : IsAffineOpen V) (J : Ideal Γ(G.left, V)) :
    chartSubschemeOver hV J ⟶ G :=
  Over.homMk (affineOpenSubschemeι hV J) rfl

include hU hC in
/-- **The closed subscheme cut out by the coordinate ideal of chart data stabilises `f`.** -/
theorem StabilizerChartData.rightStabilises_chartSubschemeOverι (D : StabilizerChartData U V f)
    (hfib : D.IsFibrewiseNonNilpotent hU hV) :
    RightStabilises (chartSubschemeOverι hV (D.ideal hU hV)) U f := by
  have : IsAffine (chartSubschemeOver hV (D.ideal hU hV)).left :=
    inferInstanceAs (IsAffine (Spec _))
  refine rightStabilises_of_forall_exists _ U f fun t ↦ ⟨⊤, isAffineOpen_top _, trivial, ?_⟩
  refine D.rightStabilisesOn_of_ideal_le_ker_app hU hV hC hfib _ ?_ (isAffineOpen_top _)
    (affineOpenSubschemeι_preimage hV _).ge
  exact (ker_app_affineOpenSubschemeι hV _).ge

include hU hC in
/-- **H13, representability of the right stabiliser of a function (Perrin, thesis I §2, IV §1).**
Let `G` be a quasi-compact, geometrically irreducible group scheme over a field `k`, `U` a
nonempty affine open of `G` such that every zero divisor of every `Γ(U) ⊗[k] κ` (`κ` a field
over `k`) is nilpotent — Perrin's hypothesis, automatic when `Γ(U)` is geometrically integral and
supplied for any group scheme in characteristic zero by
`AlgebraicGeometry.zeroDivisorsNilpotent_tensor_of_isAffineOpen` — and `f ∈ Γ(U)`.  There
is an ideal sheaf `K` of `G`, of finite type (finitely generated on a finite affine cover), such
that a `T`-point `h` of `G` right-stabilises `f` if and only if `h` factors through the closed
subscheme `V(K)`, that is `K ≤ ker h`. -/
theorem exists_idealSheafData_rightStabilises [GeometricallyIrreducible G.hom]
    [CompactSpace G.left] (hne : (U : Set G.left).Nonempty) (f : Γ(G.left, U)) :
    ∃ K : G.left.IdealSheafData,
      (∃ (n : Type u) (_ : Finite n) (W : n → G.left.affineOpens),
        ⨆ i, (W i : G.left.Opens) = ⊤ ∧ ∀ i, (K.ideal (W i)).FG) ∧
      ∀ (T : Over (Spec (.of k))) (h : T ⟶ G), RightStabilises h U f ↔ K ≤ h.left.ker := by
  have : G.left.IsSeparated := isSeparated_of_groupScheme_over_field (Grp.mk G)
  choose V hV hvV D hD using fun v ↦ exists_stabilizerChartData hU hne f v
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun v ↦ (V v : Set G.left))
    (fun v ↦ (V v).isOpen) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hvV x⟩)
  have hcov : ∀ x : G.left, ∃ i : s, x ∈ V i.1 := by
    intro x
    obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact ⟨⟨v, hv⟩, hxv⟩
  let J (i : s) := (D i.1).ideal hU (hV i.1)
  let π (i : s) := affineOpenSubschemeι (hV i.1) (J i)
  let K : G.left.IdealSheafData := ⨅ i, (π i).ker
  have hK : ∀ i : s, K.ideal ⟨V i.1, hV i.1⟩ = J i := by
    intro i
    rw [Scheme.IdealSheafData.ideal_iInf, iInf_apply]
    refine le_antisymm (iInf_le_of_le i ?_) (le_iInf fun i' ↦ ?_)
    · rw [Scheme.Hom.ker_apply, ker_app_affineOpenSubschemeι]
    · rw [Scheme.Hom.ker_apply]
      exact (D i.1).ideal_le_ker_app hU (hV i.1) hC (hD i.1) (chartSubschemeOverι (hV i'.1) (J i'))
        ((D i'.1).rightStabilises_chartSubschemeOverι hU (hV i'.1) hC (hD i'.1))
  refine ⟨K, ⟨s, inferInstance, fun i ↦ ⟨V i.1, hV i.1⟩, ?_, fun i ↦ ?_⟩, fun T h ↦ ⟨?_, ?_⟩⟩
  · refine eq_top_iff.mpr fun x _ ↦ ?_
    obtain ⟨i, hi⟩ := hcov x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  · rw [hK]
    exact (D i.1).ideal_fg hU (hV i.1)
  · intro hst
    refine Scheme.IdealSheafData.le_ofIdeals_iff.mpr fun W x hx ↦ ?_
    rw [RingHom.mem_ker]
    refine app_eq_zero_of_forall_exists_appLE_eq_zero _ _ _ fun t ht ↦ ?_
    obtain ⟨i, hi⟩ := hcov (h.left t)
    obtain ⟨g, hg, htg⟩ := W.2.exists_basicOpen_le (V := W.1 ⊓ V i.1) ⟨h.left t, ht, hi⟩ ht
    let Wg : G.left.affineOpens := ⟨G.left.basicOpen g, W.2.basicOpen g⟩
    have hWgW : Wg ≤ W := G.left.basicOpen_le g
    have hWgV : (Wg : G.left.Opens) ≤ V i.1 := hg.trans inf_le_right
    obtain ⟨V', hV', htV', hV'le'⟩ := exists_isAffineOpen_mem_and_subset (x := t)
      (U := h.left ⁻¹ᵁ Wg) htg
    have hV'le : V' ≤ h.left ⁻¹ᵁ Wg := hV'le'
    have hV'V : V' ≤ h.left ⁻¹ᵁ V i.1 := fun y hy ↦ hWgV (hV'le hy)
    have hst' := (rightStabilises_iff_forall_rightStabilisesOn h U f).mp hst ⟨V', hV'⟩
    have hJ := ((D i.1).rightStabilisesOn_iff hU (hV i.1) hC (hD i.1) h hV' hV'V).mp hst'
    have hxg : G.left.presheaf.map (homOfLE hWgW).op x ∈ K.ideal Wg :=
      K.map_ideal hWgW ▸ Ideal.mem_map_of_mem _ hx
    rw [← K.map_ideal (U := Wg) (V := ⟨V i.1, hV i.1⟩) hWgV, hK] at hxg
    have hker : Ideal.map (G.left.presheaf.map (homOfLE hWgV).op).hom (J i) ≤
        RingHom.ker (h.left.appLE Wg V' hV'le).hom := by
      refine Ideal.map_le_iff_le_comap.mpr fun y hy ↦ ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
      exact hJ hy
    have h0 := hker hxg
    rw [RingHom.mem_ker, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE] at h0
    have hle' : V' ≤ h.left ⁻¹ᵁ W := fun y hy ↦ hWgW (hV'le hy)
    exact ⟨V', htV', hle', h0⟩
  · intro hle
    refine rightStabilises_of_forall_exists h U f fun t ↦ ?_
    obtain ⟨i, hi⟩ := hcov (h.left t)
    obtain ⟨V', hV', htV', hV'le'⟩ := exists_isAffineOpen_mem_and_subset (x := t)
      (U := h.left ⁻¹ᵁ V i.1) hi
    have hV'le : V' ≤ h.left ⁻¹ᵁ V i.1 := hV'le'
    refine ⟨V', hV', htV', (D i.1).rightStabilisesOn_of_ideal_le_ker_app hU (hV i.1) hC (hD i.1) h
      ?_ hV' hV'le⟩
    exact (hK i).symm.le.trans ((hle ⟨V i.1, hV i.1⟩).trans (h.left.ideal_ker_le _))

include hU hC in
/-- **H13 (Perrin, thesis I §2, IV §1): the right stabiliser of finitely many functions is a
closed subscheme of finite type.**  Let `G` be a quasi-compact, geometrically irreducible group
scheme over a field `k`, `U` a nonempty affine open satisfying Perrin's hypothesis `hC` (see
`AlgebraicGeometry.exists_idealSheafData_rightStabilises`), and `f : n → Γ(U)` a finite family.
There is an ideal sheaf `K` of `G`, finitely generated on every
affine open, such that a `T`-point `h` right-stabilises every `f i` if and only if `K ≤ ker h`,
i.e. `h` factors through `V(K)`. -/
theorem exists_idealSheafData_forall_rightStabilises [GeometricallyIrreducible G.hom]
    [CompactSpace G.left] (hne : (U : Set G.left).Nonempty) {n : Type*} [Finite n]
    (f : n → Γ(G.left, U)) :
    ∃ K : G.left.IdealSheafData, (∀ W : G.left.affineOpens, (K.ideal W).FG) ∧
      ∀ (T : Over (Spec (.of k))) (h : T ⟶ G), (∀ i, RightStabilises h U (f i)) ↔
        K ≤ h.left.ker := by
  choose K hfg hK using fun i ↦ exists_idealSheafData_rightStabilises hU hC hne (f i)
  refine ⟨⨆ i, K i, fun W ↦ ?_, fun T h ↦ ?_⟩
  · rw [Scheme.IdealSheafData.ideal_iSup, iSup_apply]
    refine Submodule.fg_iSup _ fun i ↦ ?_
    obtain ⟨m, _, Wc, hWc, hWfg⟩ := hfg i
    exact (K i).fg_of_iSup_eq_top Wc hWc hWfg W
  · rw [iSup_le_iff]
    exact forall_congr' fun i ↦ hK i T h

/-- For `Γ(U)` geometrically integral, every zero divisor of every `Γ(U) ⊗[k] κ` is nilpotent
(it is zero). -/
theorem zeroDivisors_isNilpotent_of_isGeometricallyIntegral {C : Type u} [CommRing C] [Algebra k C]
    [Algebra.IsGeometricallyIntegral k C] (κ : Type u) [Field κ] [Algebra k κ] (z : C ⊗[k] κ)
    (hz : z ∉ nonZeroDivisors (C ⊗[k] κ)) : IsNilpotent z := by
  have := (Algebra.isGeometricallyIntegral_iff_isDomain_tensorProduct k C).mp inferInstance κ
  by_contra hn
  exact hz (mem_nonZeroDivisors_of_ne_zero fun h0 ↦ hn (h0 ▸ IsNilpotent.zero))

include hU in
/-- `AlgebraicGeometry.exists_idealSheafData_forall_rightStabilises` for `Γ(U)` geometrically
integral (for instance `G` reduced over an algebraically closed field). -/
theorem exists_idealSheafData_forall_rightStabilises_of_isGeometricallyIntegral
    [GeometricallyIrreducible G.hom] [CompactSpace G.left]
    [letI := sectionsAlgebra G.hom U; Algebra.IsGeometricallyIntegral k Γ(G.left, U)]
    (hne : (U : Set G.left).Nonempty) {n : Type*} [Finite n] (f : n → Γ(G.left, U)) :
    ∃ K : G.left.IdealSheafData, (∀ W : G.left.affineOpens, (K.ideal W).FG) ∧
      ∀ (T : Over (Spec (.of k))) (h : T ⟶ G), (∀ i, RightStabilises h U (f i)) ↔
        K ≤ h.left.ker :=
  let := sectionsAlgebra G.hom U
  exists_idealSheafData_forall_rightStabilises hU
    (fun κ _ _ ↦ zeroDivisors_isNilpotent_of_isGeometricallyIntegral κ) hne f

/-- **H14, ideal form (Perrin, thesis IV 1.3).**  Let `G` be a geometrically irreducible group
scheme over a field `k` and `U` a nonempty affine open.  Given ideal sheaves `K i` representing
the right stabilisers of subsets `F i ⊆ Γ(U)` which together contain every function on `U`, the
supremum of the `K i` is the ideal sheaf of the unit section: the stabilisers of finite families
of functions cut out the unit point. -/
theorem iSup_eq_ker_one_of_rightStabilises [GeometricallyIrreducible G.hom] (hU : IsAffineOpen U)
    (hne : (U : Set G.left).Nonempty) {m : Type*} (K : m → G.left.IdealSheafData)
    (F : m → Set Γ(G.left, U))
    (hK : ∀ i (T : Over (Spec (.of k))) (h : T ⟶ G),
      (∀ f ∈ F i, RightStabilises h U f) ↔ K i ≤ h.left.ker)
    (hcov : ∀ f, ∃ i, f ∈ F i) :
    ⨆ i, K i = (η[G] : 𝟙_ (Over (Spec (.of k))) ⟶ G).left.ker := by
  refine le_antisymm (iSup_le fun i ↦ ?_) ?_
  · refine (hK i _ η[G]).mp fun f _ ↦ ?_
    rw [MonObj.one_eq_one G]
    exact rightStabilises_one U f
  · let I := ⨆ i, K i
    let incl : Over.mk (I.subschemeι ≫ G.hom) ⟶ G := Over.homMk I.subschemeι rfl
    have hι : ∀ f, RightStabilises incl U f := by
      intro f
      obtain ⟨i, hi⟩ := hcov f
      refine (hK i _ incl).mpr ?_ f hi
      change K i ≤ I.subschemeι.ker
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact le_iSup K i
    have h1 := eq_one_of_forall_rightStabilises incl hU hne hι
    have hker : I = incl.left.ker := (Scheme.IdealSheafData.ker_subschemeι I).symm
    change _ ≤ I
    rw [hker, h1]
    change _ ≤ ((toUnit _ ≫ η[G]).left).ker
    rw [Over.comp_left]
    exact Scheme.Hom.le_ker_comp _ _

end Stabilizer

end AlgebraicGeometry

end
