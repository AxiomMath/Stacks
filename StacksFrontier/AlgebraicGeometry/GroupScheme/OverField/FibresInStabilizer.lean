/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.StabilizerGlobal
public import StacksFrontier.AlgebraicGeometry.IdealSheaf.DirectedSupFiniteType
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GenericQuotientFlat

/-!
# Fibres of a rational quotient lie in a stabiliser of finite type

Let `G` be a quasi-compact, geometrically irreducible group scheme over a field `k` and `U` a
nonempty affine open of `G` satisfying Perrin's content hypothesis (every zero divisor of every
`Γ(U) ⊗[k] κ` is nilpotent; automatic when `Γ(U)` is geometrically integral).

## Main definitions

* `AlgebraicGeometry.fibreTwist`: the morphism `(g, t) ↦ (g x(t)⁻¹, z(t))` from `G ×_k T` to
  `G ×_k G`.

## Main results

* `AlgebraicGeometry.exists_finset_rightStabilises_lift`: if `Z ⊆ G` is a closed subscheme,
  locally of finite presentation, through which the unit section factors, then the right
  stabiliser of some finite family of functions on `U` lies in `Z`.
* `AlgebraicGeometry.injective_res_of_forall_exists_mem`: an open of `U ×_k T` meeting every fibre
  over `T` is scheme-theoretically dense.
* `AlgebraicGeometry.RightStabilises.of_le`: right stabilisation of `f|_V` on a nonempty `V ⊆ U`
  implies right stabilisation of `f` on `U`.
* `AlgebraicGeometry.rightStabilises_of_comp_eq`: if `π : V ⟶ X` and a rational map
  `F : G × X ⇢ X` satisfy `F (a, π b) = π (a b)` on an open `D''` of `G × G`, then for `T`-points
  `x, y` of `V ∩ pr₂ D''` with `π x = π y` the point `x⁻¹ y` right-stabilises every coordinate
  function `π^* φ`.
* `AlgebraicGeometry.exists_finset_forall_fibres_lift`: `x⁻¹ y` factors through `Z` once the
  coordinates of `π` include a suitable finite family of functions on `U`.

## References

* D. Perrin, *Schémas en groupes quasi-compacts sur un corps*, thèse, IV §1.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory TensorProduct

namespace AlgebraicGeometry

universe u

section Stabilizer

variable {k : Type u} [Field k] {G : Over (Spec (.of k))} [GrpObj G] {U : G.left.Opens}

/-- The closed subscheme `V(K)` of `G` as a `T`-point of `G`. -/
noncomputable abbrev idealSheafPoint (K : G.left.IdealSheafData) :
    Over.mk (K.subschemeι ≫ G.hom) ⟶ G :=
  Over.homMk K.subschemeι rfl

/-- **A closed subscheme of finite type through the unit contains the stabiliser of a finite
family.** Let `G` be a quasi-compact geometrically irreducible group scheme over a field `k`, `U`
a nonempty affine open satisfying Perrin's content hypothesis `hC`, and `i : Z ⟶ G` a closed
immersion locally of finite presentation through which the unit section factors. Then there is a
finite set `s` of functions on `U` such that every `T`-point of `G` right-stabilising every member
of `s` factors through `Z`. -/
theorem exists_finset_rightStabilises_lift [GeometricallyIrreducible G.hom]
    [CompactSpace G.left] (hU : IsAffineOpen U)
    (hC : letI := sectionsAlgebra G.hom U
      ∀ (κ : Type u) [Field κ] [Algebra k κ] (z : Γ(G.left, U) ⊗[k] κ),
        z ∉ nonZeroDivisors (Γ(G.left, U) ⊗[k] κ) → IsNilpotent z)
    (hne : (U : Set G.left).Nonempty) {Z : Scheme.{u}} (i : Z ⟶ G.left) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i]
    (he : ∃ e : (𝟙_ (Over (Spec (.of k)))).left ⟶ Z,
      e ≫ i = (η[G] : 𝟙_ (Over (Spec (.of k))) ⟶ G).left) :
    ∃ s : Finset Γ(G.left, U), ∀ (T : Over (Spec (.of k))) (h : T ⟶ G),
      (∀ f ∈ s, RightStabilises h U f) → ∃ z : T.left ⟶ Z, z ≫ i = h.left := by
  classical
  choose K _ hK using fun s : Finset Γ(G.left, U) ↦
    exists_idealSheafData_forall_rightStabilises hU hC hne (fun f : s ↦ f.1)
  have hK' : ∀ (s : Finset Γ(G.left, U)) (T : Over (Spec (.of k))) (h : T ⟶ G),
      (∀ f ∈ (s : Set Γ(G.left, U)), RightStabilises h U f) ↔ K s ≤ h.left.ker := by
    intro s T h
    rw [← hK s T h]
    exact ⟨fun H f ↦ H f.1 f.2, fun H f hf ↦ H ⟨f, hf⟩⟩
  have hmono : ∀ s s' : Finset Γ(G.left, U), s ⊆ s' → K s ≤ K s' := by
    intro s s' hss'
    have h1 : ∀ f ∈ (s' : Set Γ(G.left, U)), RightStabilises (idealSheafPoint (K s')) U f :=
      (hK' s' _ _).mpr (Scheme.IdealSheafData.ker_subschemeι _).ge
    have h2 := (hK' s _ (idealSheafPoint (K s'))).mp fun f hf ↦ h1 f (hss' hf)
    exact h2.trans (Scheme.IdealSheafData.ker_subschemeι _).le
  have hdir : Directed (· ≤ ·) fun s ↦ (K s).subschemeι.ker := by
    intro s s'
    simp only [Scheme.IdealSheafData.ker_subschemeι]
    exact ⟨s ∪ s', hmono _ _ Finset.subset_union_left, hmono _ _ Finset.subset_union_right⟩
  have hsup : ⨆ s, K s = (η[G] : 𝟙_ (Over (Spec (.of k))) ⟶ G).left.ker :=
    iSup_eq_ker_one_of_rightStabilises hU hne K (fun s ↦ (s : Set Γ(G.left, U))) hK'
      fun f ↦ ⟨{f}, by simp⟩
  obtain ⟨e, he⟩ := he
  have hle : i.ker ≤ ⨆ s, (K s).subschemeι.ker := by
    simp only [Scheme.IdealSheafData.ker_subschemeι]
    rw [hsup, ← he]
    exact Scheme.Hom.le_ker_comp _ _
  obtain ⟨s, t, ht⟩ := exists_lift_of_ker_le_iSup_of_directed i (fun s ↦ (K s).subschemeι)
    hdir hle
  refine ⟨s, fun T h hst ↦ ?_⟩
  have hker : (K s).subschemeι.ker ≤ h.left.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact (hK' s T h).mp hst
  refine ⟨IsClosedImmersion.lift (K s).subschemeι h.left hker ≫ t, ?_⟩
  rw [Category.assoc, ht, IsClosedImmersion.lift_fac]

/-! ### Opens meeting every fibre are scheme-theoretically dense -/

omit [GrpObj G] in
/-- **A fibrewise non-zero-divisor near every point.** Let `U` be an affine open of `G` satisfying
Perrin's content hypothesis `hC` and `O ⊆ U ×_k T` an open of `G ×_k T` meeting every fibre over
`T`. Every point of `T` has an affine neighbourhood `V'` with a non-zero-divisor `b` of
`Γ(U ×_k V')` such that `D(b) ⊆ O`. -/
theorem exists_basicOpen_le_mem_nonZeroDivisors {T : Over (Spec (.of k))} (hU : IsAffineOpen U)
    (hC : letI := sectionsAlgebra G.hom U
      ∀ (κ : Type u) [Field κ] [Algebra k κ] (z : Γ(G.left, U) ⊗[k] κ),
        z ∉ nonZeroDivisors (Γ(G.left, U) ⊗[k] κ) → IsNilpotent z)
    {O : (G ⊗ T).left.Opens} (hOU : O ≤ (fst G T).left ⁻¹ᵁ U)
    (hO : ∀ t : T.left, ∃ a ∈ O, (snd G T).left a = t) (t : T.left) :
    ∃ (V' : T.left.Opens) (_hV' : IsAffineOpen V'), t ∈ V' ∧
      ∃ b : Γ((G ⊗ T).left, prodOpen U V'), (G ⊗ T).left.basicOpen b ≤ O ∧
        b ∈ nonZeroDivisors Γ((G ⊗ T).left, prodOpen U V') := by
  let X := (G ⊗ T).left
  obtain ⟨w, hwO, hwt⟩ := hO t
  obtain ⟨V₀, hV₀, htV₀, -⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top t)
  have hY₀ := isAffineOpen_prodOpen (T := T) hU hV₀
  have hwY₀ : w ∈ prodOpen U V₀ := ⟨hOU hwO, show (snd G T).left w ∈ V₀ from hwt ▸ htV₀⟩
  obtain ⟨b₀, hb₀, hwb₀⟩ := hY₀.exists_basicOpen_le (V := O ⊓ prodOpen U V₀) ⟨w, hwO, hwY₀⟩ hwY₀
  let O' : T.left.Opens := ⟨(snd G T).left '' (X.basicOpen b₀ : Set X),
    (pullback.snd G.hom T.hom).isOpenMap _ (X.basicOpen b₀).isOpen⟩
  have htO' : t ∈ O' := ⟨w, hwb₀, hwt⟩
  obtain ⟨a₀, ha₀, hta₀⟩ := hV₀.exists_basicOpen_le (V := O' ⊓ V₀) ⟨t, htO', htV₀⟩ htV₀
  let V := T.left.basicOpen a₀
  have hV : IsAffineOpen V := hV₀.basicOpen a₀
  have hVV₀ : V ≤ V₀ := T.left.basicOpen_le a₀
  have hVO' : V ≤ O' := ha₀.trans inf_le_left
  have hY := isAffineOpen_prodOpen (T := T) hU hV
  have hYY₀ : prodOpen U V ≤ prodOpen U V₀ := inf_le_inf_left _ (Scheme.Hom.preimage_mono _ hVV₀)
  let b := X.presheaf.map (homOfLE hYY₀).op b₀
  have hbD : X.basicOpen b = prodOpen U V ⊓ X.basicOpen b₀ := Scheme.basicOpen_res _ _ _
  have hbO : X.basicOpen b ≤ O := hbD ▸ inf_le_right.trans (hb₀.trans inf_le_left)
  refine ⟨V, hV, hta₀, b, hbO, ?_⟩
  let := sectionsAlgebra G.hom U
  let := sectionsAlgebra T.hom V
  have hfib : ∀ p : PrimeSpectrum Γ(T.left, V), ¬ IsNilpotent
      (Algebra.TensorProduct.map (AlgHom.id k Γ(G.left, U))
        (IsScalarTower.toAlgHom k Γ(T.left, V) p.asIdeal.ResidueField)
        ((prodOpenTensorIso hU hV).inv b)) := by
    intro p
    let y : V := hV.isoSpec.inv (show Spec Γ(T.left, V) from p)
    have hyp : hV.primeIdealOf y = p := by
      change (hV.isoSpec.inv ≫ hV.isoSpec.hom) (show Spec Γ(T.left, V) from p) = p
      rw [Iso.inv_hom_id]
      rfl
    obtain ⟨w', hw'b₀, hw'y⟩ := hVO' y.2
    have hw'Y : w' ∈ prodOpen U V :=
      ⟨hOU (hb₀.trans inf_le_left hw'b₀), show (snd G T).left w' ∈ V from hw'y ▸ y.2⟩
    have hw'b : w' ∈ X.basicOpen b := hbD ▸ ⟨hw'Y, hw'b₀⟩
    let Q := hY.primeIdealOf ⟨w', hw'Y⟩
    have hQp : (Q.asIdeal.comap ((snd G T).left.appLE V (prodOpen U V)
        (prodOpen_le_snd U V)).hom) = p.asIdeal := by
      have := IsAffineOpen.comap_primeIdealOf_appLE (f := (snd G T).left) V hV (prodOpen U V) hY
        (prodOpen_le_snd U V) hw'Y
      rw [← hyp]
      refine (congrArg PrimeSpectrum.asIdeal this).trans ?_
      congr 2
      exact Subtype.ext hw'y
    have hbQ : b ∉ Q.asIdeal := by
      have hmem : hY.fromSpec Q ∈ X.basicOpen b := by
        rw [hY.fromSpec_primeIdealOf]
        exact hw'b
      exact (hY.fromSpec_preimage_basicOpen b).le hmem
    refine TensorProduct.not_isNilpotent_map_residueField_of_not_mem
      (prodOpenTensorIso hU hV).commRingCatIsoToRingEquiv
      ((fst G T).left.appLE U (prodOpen U V) (prodOpen_le_fst U V)).hom
      ((snd G T).left.appLE V (prodOpen U V) (prodOpen_le_snd U V)).hom
      (prodOpenTensorIso_tmul hU hV) _ Q.asIdeal p.asIdeal hQp.symm ?_
    change (prodOpenTensorIso hU hV).hom ((prodOpenTensorIso hU hV).inv b) ∉ Q.asIdeal
    rwa [Iso.inv_hom_id_apply]
  have hz := TensorProduct.mem_nonZeroDivisors_of_forall_not_isNilpotent
    ((prodOpenTensorIso hU hV).inv b) (fun p ↦ hC _) hfib
  have hb : b = (prodOpenTensorIso hU hV).hom ((prodOpenTensorIso hU hV).inv b) :=
    (Iso.inv_hom_id_apply _ _).symm
  rw [hb, ← MulEquivClass.map_nonZeroDivisors
    (prodOpenTensorIso hU hV).commRingCatIsoToRingEquiv]
  exact ⟨_, hz, rfl⟩

omit [GrpObj G] in
/-- **An open of `U ×_k T` meeting every fibre over `T` is scheme-theoretically dense.** Let `U` be
an affine open of `G` satisfying Perrin's content hypothesis `hC`, and `O ⊆ W ⊆ U ×_k T` opens of
`G ×_k T` with `O` meeting every fibre over `T`. Then restriction of sections from `W` to `O` is
injective. -/
theorem injective_res_of_forall_exists_mem {T : Over (Spec (.of k))} (hU : IsAffineOpen U)
    (hC : letI := sectionsAlgebra G.hom U
      ∀ (κ : Type u) [Field κ] [Algebra k κ] (z : Γ(G.left, U) ⊗[k] κ),
        z ∉ nonZeroDivisors (Γ(G.left, U) ⊗[k] κ) → IsNilpotent z)
    {O W : (G ⊗ T).left.Opens} (hOW : O ≤ W) (hWU : W ≤ (fst G T).left ⁻¹ᵁ U)
    (hO : ∀ t : T.left, ∃ a ∈ O, (snd G T).left a = t) :
    Function.Injective ((G ⊗ T).left.presheaf.map (homOfLE hOW).op).hom := by
  let X := (G ⊗ T).left
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine TopCat.Presheaf.section_ext X.sheaf W s 0 fun w hw ↦ ?_
  obtain ⟨V', hV', htV', b, hbO, hb⟩ :=
    exists_basicOpen_le_mem_nonZeroDivisors hU hC (hOW.trans hWU) hO ((snd G T).left w)
  have hY := isAffineOpen_prodOpen (T := T) hU hV'
  have hwY : w ∈ prodOpen U V' := ⟨hWU hw, htV'⟩
  have hbWY : X.basicOpen b ≤ W ⊓ prodOpen U V' := le_inf (hbO.trans hOW) (X.basicOpen_le b)
  have hinj := Scheme.injective_res_basicOpen_of_mem_nonZeroDivisors hY hb
    (inf_le_right : W ⊓ prodOpen U V' ≤ prodOpen U V') hbWY
  have hle : W ⊓ prodOpen U V' ≤ W := inf_le_left
  have hs' : X.presheaf.map (homOfLE hle).op s = 0 := by
    refine hinj ?_
    have e1 : X.presheaf.map (homOfLE hbWY).op (X.presheaf.map (homOfLE hle).op s) =
        X.presheaf.map (homOfLE hbO).op (X.presheaf.map (homOfLE hOW).op s) := by
      simp only [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    rw [e1, hs, map_zero, map_zero]
  have hwWY : w ∈ W ⊓ prodOpen U V' := ⟨hw, hwY⟩
  have := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hle) w hwWY s
  rw [map_zero]
  refine this.symm.trans ?_
  change X.presheaf.germ _ w hwWY (X.presheaf.map (homOfLE hle).op s) = 0
  rw [hs', map_zero]

/-- **Right stabilisation on a smaller open.** Let `G` be geometrically irreducible, `V ⊆ U` opens
with `V` nonempty and `U` affine satisfying Perrin's content hypothesis. If `h` right-stabilises
the restriction of `f ∈ Γ(U)` to `V`, then `h` right-stabilises `f` on `U`. -/
theorem RightStabilises.of_le [GeometricallyIrreducible G.hom] {T : Over (Spec (.of k))}
    (hU : IsAffineOpen U)
    (hC : letI := sectionsAlgebra G.hom U
      ∀ (κ : Type u) [Field κ] [Algebra k κ] (z : Γ(G.left, U) ⊗[k] κ),
        z ∉ nonZeroDivisors (Γ(G.left, U) ⊗[k] κ) → IsNilpotent z)
    {V : G.left.Opens} (hVU : V ≤ U) (hVne : (V : Set G.left).Nonempty) {h : T ⟶ G}
    {f : Γ(G.left, U)} (hst : RightStabilises h V (G.left.presheaf.map (homOfLE hVU).op f)) :
    RightStabilises h U f := by
  have hWW : rightStabilizerLocus h V ≤ rightStabilizerLocus h U :=
    inf_le_inf (Scheme.Hom.preimage_mono _ hVU) (Scheme.Hom.preimage_mono _ hVU)
  have hmeet : ∀ t : T.left, ∃ a ∈ rightStabilizerLocus h V, (snd G T).left a = t := by
    intro t
    obtain ⟨a, ha⟩ := (surjective_rightStabilizerLocus h hVne).surj t
    exact ⟨_, a.2, ha⟩
  refine injective_res_of_forall_exists_mem hU hC hWW (rightStabilizerLocus_le_fst h U) hmeet ?_
  simpa only [RightStabilises, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map,
    Scheme.Hom.map_appLE] using hst

/-! ### Fibres of a rational quotient map lie in the stabiliser of its coordinates -/

section Fibres

open GenericQuotientFlat

variable (X : Over (Spec (.of k)))

/-- `(g, t) ↦ (g · x(t)⁻¹, z(t))`, a morphism `G ×_k T ⟶ G ×_k G`. -/
noncomputable abbrev fibreTwist {T : Over (Spec (.of k))} (x z : T ⟶ G) : G ⊗ T ⟶ G ⊗ G :=
  (rightShear x⁻¹).hom ≫ stabilizerBaseChange z

/-- The first component of `AlgebraicGeometry.fibreTwist x z` is `(g, t) ↦ g · x(t)⁻¹`. -/
theorem fibreTwist_fst {T : Over (Spec (.of k))} (x z : T ⟶ G) :
    fibreTwist x z ≫ fst G G = fst G T * (snd G T ≫ x)⁻¹ := by
  simp [fibreTwist, stabilizerBaseChange, rightShear, rightTranslate, GrpObj.comp_inv]

/-- The second component of `AlgebraicGeometry.fibreTwist x z` is `(g, t) ↦ z(t)`. -/
theorem fibreTwist_snd {T : Over (Spec (.of k))} (x z : T ⟶ G) :
    fibreTwist x z ≫ snd G G = snd G T ≫ z := by
  simp [fibreTwist, stabilizerBaseChange, rightShear]

/-- Composed with the multiplication, `AlgebraicGeometry.fibreTwist x z` is right translation by
`x⁻¹ * z`. -/
theorem fibreTwist_mu {T : Over (Spec (.of k))} (x z : T ⟶ G) :
    fibreTwist x z ≫ μ[G] = rightTranslate (x⁻¹ * z) := by
  rw [mu_eq_fst_mul_snd, MonObj.comp_mul, fibreTwist_fst, fibreTwist_snd, rightTranslate,
    MonObj.comp_mul, GrpObj.comp_inv, mul_assoc]

/-- Composed with the multiplication, `AlgebraicGeometry.fibreTwist x x` is the first
projection. -/
theorem fibreTwist_self_mu {T : Over (Spec (.of k))} (x : T ⟶ G) :
    fibreTwist x x ≫ μ[G] = fst G T := by
  rw [fibreTwist_mu, inv_mul_cancel, rightTranslate_one]

/-- The preimage of an open `D''` of `G ×_k G` under `(g, t) ↦ (g x(t)⁻¹, z(t))` meets every
fibre over `T` as soon as `z` lands in the image of `D''` under the second projection. -/
theorem exists_mem_fibreTwist_preimage {T : Over (Spec (.of k))} (x z : T ⟶ G)
    (D'' : (G ⊗ G).left.Opens) (hz : ∀ t, z.left t ∈ (snd G G).left '' (D'' : Set (G ⊗ G).left))
    (t : T.left) : ∃ a, (snd G T).left a = t ∧ (fibreTwist x z).left a ∈ D'' := by
  obtain ⟨d, hd, hdt⟩ := hz t
  obtain ⟨a', ha'd, ha't⟩ := Scheme.exists_preimage_of_isPullback
    (isPullback_stabilizerBaseChange (G := G) z) d t hdt
  refine ⟨(rightShear x⁻¹).inv.left a', ?_, ?_⟩
  · change ((rightShear x⁻¹).inv ≫ snd G T).left a' = t
    rw [rightShear_inv_snd]
    exact ha't
  · change ((rightShear x⁻¹).inv ≫ (rightShear x⁻¹).hom ≫ stabilizerBaseChange z).left a' ∈ D''
    rw [Iso.inv_hom_id_assoc]
    exact ha'd ▸ hd

variable [GeometricallyIrreducible G.hom]

/-- **The fibres of a rational quotient map lie in the stabiliser of its coordinates.** Let
`π : V ⟶ X` be defined on an affine open `V` of a geometrically irreducible group scheme `G` over
`k` satisfying Perrin's content hypothesis, and `F` a rational map `G × X ⇢ X` (defined on `D`)
with `F (a, π b) = π (a b)` on an open `D''` of `G × G`. Let `x, y` be `T`-points of `G` landing
in `V` and in the image of `D''` under the second projection, with `π x = π y`. Then `x⁻¹ y`
right-stabilises `π^* φ` on `V` for every function `φ` on `X`. -/
theorem rightStabilises_of_comp_eq (V : G.left.Opens) (hV : IsAffineOpen V)
    (hC : letI := sectionsAlgebra G.hom V
      ∀ (κ : Type u) [Field κ] [Algebra k κ] (z : Γ(G.left, V) ⊗[k] κ),
        z ∉ nonZeroDivisors (Γ(G.left, V) ⊗[k] κ) → IsNilpotent z)
    (π : V.toScheme ⟶ X.left) (hπ : π ≫ X.hom = V.ι ≫ G.hom) (D : (G ⊗ X).left.Opens)
    (F : D.toScheme ⟶ X.left) (D'' : (G ⊗ G).left.Opens)
    (hD''V : D'' ≤ EV G V) (hD''μ : D'' ≤ μ[G].left ⁻¹ᵁ V)
    (hD''D : Set.range ((G ⊗ G).left.homOfLE hD''V ≫ onePi G X V π hπ) ⊆ Set.range D.ι)
    (hR : IsOpenImmersion.lift D.ι _ hD''D ≫ F =
      IsOpenImmersion.lift V.ι (D''.ι ≫ μ[G].left) (range_ι_comp_subset _ hD''μ) ≫ π)
    {T : Over (Spec (.of k))} (x y : T ⟶ G) (x' y' : T.left ⟶ V.toScheme)
    (hx : x' ≫ V.ι = x.left) (hy : y' ≫ V.ι = y.left) (hxy : x' ≫ π = y' ≫ π)
    (hx₂ : ∀ t, x.left t ∈ (snd G G).left '' (D'' : Set (G ⊗ G).left))
    (hy₂ : ∀ t, y.left t ∈ (snd G G).left '' (D'' : Set (G ⊗ G).left))
    (φ : Γ(X.left, ⊤)) :
    RightStabilises (x⁻¹ * y) V (V.topIso.hom (π.appTop φ)) := by
  set h := x⁻¹ * y
  let α := fibreTwist x y
  let β := fibreTwist x x
  let Ω : (G ⊗ T).left.Opens := α.left ⁻¹ᵁ D'' ⊓ β.left ⁻¹ᵁ D''
  have hαμ : α.left ≫ μ[G].left = (rightTranslate h).left := by
    rw [← Over.comp_left, fibreTwist_mu]
  have hβμ : β.left ≫ μ[G].left = (fst G T).left := by
    rw [← Over.comp_left, fibreTwist_self_mu]
  have hΩ₁ : Ω ≤ (fst G T).left ⁻¹ᵁ V := by
    intro a ha
    change (fst G T).left a ∈ V
    rw [← hβμ, Scheme.Hom.comp_apply]
    exact hD''μ ha.2
  have hΩ₂ : Ω ≤ (rightTranslate h).left ⁻¹ᵁ V := by
    intro a ha
    change (rightTranslate h).left a ∈ V
    rw [← hαμ, Scheme.Hom.comp_apply]
    exact hD''μ ha.1
  have hΩW : Ω ≤ rightStabilizerLocus h V := le_inf hΩ₁ hΩ₂
  have hmeet : ∀ t : T.left, ∃ a ∈ Ω, (snd G T).left a = t := by
    intro t
    obtain ⟨a₁, ha₁t, ha₁⟩ := exists_mem_fibreTwist_preimage x y D'' hy₂ t
    obtain ⟨a₂, ha₂t, ha₂⟩ := exists_mem_fibreTwist_preimage x x D'' hx₂ t
    have hirr := Scheme.Hom.isIrreducible_preimage (pullback.snd G.hom T.hom)
      (pullback.snd G.hom T.hom).isOpenMap (isIrreducible_singleton (x := t))
    obtain ⟨w, hwt, hw₁, hw₂⟩ := hirr.2 _ _ (α.left ⁻¹ᵁ D'').isOpen (β.left ⁻¹ᵁ D'').isOpen
      ⟨a₁, ha₁t, ha₁⟩ ⟨a₂, ha₂t, ha₂⟩
    exact ⟨w, ⟨hw₁, hw₂⟩, hwt⟩
  let q₁ := (fst G T).left.resLE V Ω hΩ₁
  let q₂ := (rightTranslate h).left.resLE V Ω hΩ₂
  let αΩ := α.left.resLE D'' Ω inf_le_left
  let βΩ := β.left.resLE D'' Ω inf_le_right
  let LV := IsOpenImmersion.lift V.ι (D''.ι ≫ μ[G].left) (range_ι_comp_subset _ hD''μ)
  let LD := IsOpenImmersion.lift D.ι _ hD''D
  have hR' : LD ≫ F = LV ≫ π := hR
  have c₁ : αΩ ≫ LV = q₂ := by
    rw [← cancel_mono V.ι, Category.assoc, IsOpenImmersion.lift_fac, Scheme.Hom.resLE_comp_ι,
      ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hαμ]
  have c₂ : βΩ ≫ LV = q₁ := by
    rw [← cancel_mono V.ι, Category.assoc, IsOpenImmersion.lift_fac, Scheme.Hom.resLE_comp_ι,
      ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hβμ]
  have hsnd : ∀ (z : T ⟶ G) (z' : T.left ⟶ V.toScheme), z' ≫ V.ι = z.left →
      ∀ (e : Ω ≤ (fibreTwist x z).left ⁻¹ᵁ D''),
      (fibreTwist x z).left.resLE D'' Ω e ≫
        (G ⊗ G).left.homOfLE hD''V ≫ (snd G G).left.resLE V (EV G V) le_rfl =
      Ω.ι ≫ (snd G T).left ≫ z' := by
    intro z z' hz e
    rw [← cancel_mono V.ι, Category.assoc, Category.assoc, Scheme.Hom.resLE_comp_ι,
      Scheme.homOfLE_ι_assoc, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
      Category.assoc, Category.assoc, hz, ← Over.comp_left, fibreTwist_snd, Over.comp_left]
  have c₃ : αΩ ≫ LD = βΩ ≫ LD := by
    rw [← cancel_mono D.ι, Category.assoc, Category.assoc, IsOpenImmersion.lift_fac]
    apply pullback.hom_ext
    · change (αΩ ≫ _ ≫ onePi G X V π hπ ≫ (fst G X).left) =
        (βΩ ≫ _ ≫ onePi G X V π hπ ≫ (fst G X).left)
      rw [onePi_fst, Scheme.homOfLE_ι_assoc,
        ← Category.assoc αΩ, Scheme.Hom.resLE_comp_ι, ← Category.assoc βΩ,
        Scheme.Hom.resLE_comp_ι, Category.assoc, Category.assoc, ← Over.comp_left,
        ← Over.comp_left, fibreTwist_fst, fibreTwist_fst]
    · change (αΩ ≫ _ ≫ onePi G X V π hπ ≫ (snd G X).left) =
        (βΩ ≫ _ ≫ onePi G X V π hπ ≫ (snd G X).left)
      have h₁ : αΩ ≫ (G ⊗ G).left.homOfLE hD''V ≫ (snd G G).left.resLE V (EV G V) le_rfl =
          Ω.ι ≫ (snd G T).left ≫ y' := hsnd y y' hy inf_le_left
      have h₂ : βΩ ≫ (G ⊗ G).left.homOfLE hD''V ≫ (snd G G).left.resLE V (EV G V) le_rfl =
          Ω.ι ≫ (snd G T).left ≫ x' := hsnd x x' hx inf_le_right
      rw [onePi_snd]
      simp only [← Category.assoc] at h₁ h₂ ⊢
      rw [h₁, h₂]
      simp only [Category.assoc, hxy]
  have key : q₁ ≫ π = q₂ ≫ π := by
    rw [← c₁, ← c₂, Category.assoc, Category.assoc, ← hR', ← Category.assoc,
      ← Category.assoc, c₃]
  refine injective_res_of_forall_exists_mem hV hC hΩW (rightStabilizerLocus_le_fst h V) hmeet ?_
  have e : ∀ (g : (G ⊗ T).left ⟶ G.left) (e₁ : rightStabilizerLocus h V ≤ g ⁻¹ᵁ V)
      (e₂ : Ω ≤ g ⁻¹ᵁ V) (c : Γ(V.toScheme, ⊤)),
      (G ⊗ T).left.presheaf.map (homOfLE hΩW).op (g.appLE V _ e₁ (V.topIso.hom c)) =
        Ω.topIso.hom ((g.resLE V Ω e₂).appTop c) := by
    intro g e₁ e₂ c
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.appTop,
      Scheme.Hom.resLE_app_top]
    simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  have key' : q₁.appTop (π.appTop φ) = q₂.appTop (π.appTop φ) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      ← Scheme.Hom.comp_appTop, key]
  rw [e _ _ hΩ₁, e _ _ hΩ₂]
  exact congrArg Ω.topIso.hom key'

/-- **The fibres of a rational quotient map of `G` lie in a given closed subscheme of finite
presentation through the unit.** Let `G` be a quasi-compact, geometrically irreducible group
scheme over `k`, `U₀` a nonempty affine open satisfying Perrin's content hypothesis and
`i : Z ⟶ G` a closed immersion locally of finite presentation through which the unit section
factors. There is a finite set `s` of functions on `U₀` such that: for every rational quotient
datum (`π : V ⟶ X` on an affine open `V ⊆ U₀` satisfying the content hypothesis, `F` with
`F (a, π b) = π (a b)` on `D''`) whose coordinate functions include the restrictions of the
members of `s`, any two `T`-points `x, y` of `V ∩ pr₂ D''` with `π x = π y` satisfy
`x⁻¹ y ∈ Z`. -/
theorem exists_finset_forall_fibres_lift [CompactSpace G.left] {U₀ : G.left.Opens}
    (hU₀ : IsAffineOpen U₀)
    (hC₀ : letI := sectionsAlgebra G.hom U₀
      ∀ (κ : Type u) [Field κ] [Algebra k κ] (z : Γ(G.left, U₀) ⊗[k] κ),
        z ∉ nonZeroDivisors (Γ(G.left, U₀) ⊗[k] κ) → IsNilpotent z)
    (hne₀ : (U₀ : Set G.left).Nonempty) {Z : Scheme.{u}} (i : Z ⟶ G.left) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i]
    (he : ∃ e : (𝟙_ (Over (Spec (.of k)))).left ⟶ Z,
      e ≫ i = (η[G] : 𝟙_ (Over (Spec (.of k))) ⟶ G).left) :
    ∃ s : Finset Γ(G.left, U₀), ∀ (V : G.left.Opens) (hVU₀ : V ≤ U₀) (_hV : IsAffineOpen V)
      (_hVne : (V : Set G.left).Nonempty)
      (_hC : letI := sectionsAlgebra G.hom V
        ∀ (κ : Type u) [Field κ] [Algebra k κ] (z : Γ(G.left, V) ⊗[k] κ),
          z ∉ nonZeroDivisors (Γ(G.left, V) ⊗[k] κ) → IsNilpotent z)
      (π : V.toScheme ⟶ X.left) (hπ : π ≫ X.hom = V.ι ≫ G.hom) (D : (G ⊗ X).left.Opens)
      (F : D.toScheme ⟶ X.left) (D'' : (G ⊗ G).left.Opens)
      (hD''V : D'' ≤ EV G V) (hD''μ : D'' ≤ μ[G].left ⁻¹ᵁ V)
      (hD''D : Set.range ((G ⊗ G).left.homOfLE hD''V ≫ onePi G X V π hπ) ⊆ Set.range D.ι)
      (_hR : IsOpenImmersion.lift D.ι _ hD''D ≫ F =
        IsOpenImmersion.lift V.ι (D''.ι ≫ μ[G].left) (range_ι_comp_subset _ hD''μ) ≫ π)
      (_hs : ∀ f ∈ s, ∃ φ : Γ(X.left, ⊤),
        V.topIso.hom (π.appTop φ) = G.left.presheaf.map (homOfLE hVU₀).op f)
      (O : G.left.Opens) (_hO : (O : Set G.left) = (snd G G).left '' (D'' : Set (G ⊗ G).left))
      (T : Over (Spec (.of k))) (x y : T ⟶ G) (x' y' : T.left ⟶ (V ⊓ O).toScheme),
      x' ≫ (V ⊓ O).ι = x.left → y' ≫ (V ⊓ O).ι = y.left →
      x' ≫ G.left.homOfLE inf_le_left ≫ π = y' ≫ G.left.homOfLE inf_le_left ≫ π →
      ∃ z : T.left ⟶ Z, z ≫ i = (x⁻¹ * y).left := by
  obtain ⟨s, hs⟩ := exists_finset_rightStabilises_lift hU₀ hC₀ hne₀ i he
  refine ⟨s, fun V hVU₀ hV hVne hC π hπ D F D'' hD''V hD''μ hD''D hR hsφ O hO T x y x' y' hx hy
    hxy ↦ hs T (x⁻¹ * y) fun f hf ↦ ?_⟩
  obtain ⟨φ, hφ⟩ := hsφ f hf
  have hmem : ∀ (z : T ⟶ G) (z' : T.left ⟶ (V ⊓ O).toScheme), z' ≫ (V ⊓ O).ι = z.left →
      ∀ t, z.left t ∈ (snd G G).left '' (D'' : Set (G ⊗ G).left) := by
    intro z z' hz t
    have h1 : z.left t ∈ ((V ⊓ O : G.left.Opens) : Set G.left) := by
      rw [← hz, Scheme.Hom.comp_apply, ← Scheme.Opens.range_ι]
      exact ⟨_, rfl⟩
    rw [← hO]
    exact h1.2
  have hlift : ∀ (z : T ⟶ G) (z' : T.left ⟶ (V ⊓ O).toScheme), z' ≫ (V ⊓ O).ι = z.left →
      (z' ≫ G.left.homOfLE inf_le_left) ≫ V.ι = z.left := by
    intro z z' hz
    rw [Category.assoc, Scheme.homOfLE_ι, hz]
  refine RightStabilises.of_le hU₀ hC₀ hVU₀ hVne ?_
  rw [← hφ]
  exact rightStabilises_of_comp_eq X V hV hC π hπ D F D'' hD''V hD''μ hD''D hR x y
    (x' ≫ G.left.homOfLE inf_le_left) (y' ≫ G.left.homOfLE inf_le_left) (hlift x x' hx)
    (hlift y y' hy) (by simpa only [Category.assoc] using hxy) (hmem x x' hx) (hmem y y' hy) φ

end Fibres

end Stabilizer

end AlgebraicGeometry

end
