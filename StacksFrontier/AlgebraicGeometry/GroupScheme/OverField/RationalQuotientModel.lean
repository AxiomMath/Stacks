/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.FibresInStabilizer
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.LeftInvariantModel
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.TranslatedSmoothModel
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AffineQuotientModel
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AffineStabilizer
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.LeftInvariantQuotientModel
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.RationalGroup

/-!
# A flat rational quotient map whose fibres lie in the stabiliser of given functions

Let `Γ` be an integral group scheme over an algebraically closed field `k`, `U₀` a nonempty affine
open of `Γ` and `s` a finite set of functions on `U₀`. Given a rational quotient datum —
`π : V ⟶ X` on an affine open `V ⊆ U₀` with `X` integral and separated, the members of `s`
restricted to `V` among the coordinate functions `π^* φ`, and a rational map `F : Γ × X ⇢ X`
with `F (a, π b) = π (a b)` on a dense open of the canonical domain — there is a nonempty open
`W ⊆ V` on which `π` is flat and such that any two `T`-points `x, y` of `W` with `π x = π y`
satisfy: `x⁻¹ y` right-stabilises every member of `s` on `U₀`.

## Main results

* `AlgebraicGeometry.exists_open_flatAt_forall_rightStabilises`: the flat open `W ⊆ V` whose
  fibres under `π` lie in the stabiliser of `s`.
* `AlgebraicGeometry.exists_smooth_model_forall_rightStabilises`: the same with `π` replaced by a
  flat quasi-compact morphism to a smooth affine `k`-scheme.
* `AlgebraicGeometry.exists_flat_smooth_model_rightStabilises`: in characteristic zero, for a
  geometrically irreducible `Γ`, such a smooth affine quotient exists for every finite set `s`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry

universe u

open GenericQuotientFlat

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] (X : Over (Spec (.of k)))

/-- For an open `U` of the canonical domain, the image of the composite of the inclusion of `U`
with `onePi` is contained in the open `D` of `G × X`. -/
theorem range_onePi_subset_of_le_canonicalDomain (V : G.left.Opens) (π : V.toScheme ⟶ X.left)
    (hπ : π ≫ X.hom = V.ι ≫ G.hom) (D : (G ⊗ X).left.Opens) (U : (G ⊗ G).left.Opens)
    (hU : U ≤ canonicalDomain G X V π hπ D) :
    Set.range ((G ⊗ G).left.homOfLE (hU.trans (canonicalDomain_le_EV G X V π hπ D)) ≫
      onePi G X V π hπ) ⊆ Set.range D.ι := by
  rintro _ ⟨z, rfl⟩
  refine canonicalDomain_range G X V π hπ D ⟨(G ⊗ G).left.homOfLE hU z, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Category.assoc, Scheme.homOfLE_homOfLE]

/-- If `F (a, π b) = π (a b)` holds on an open `U` of the canonical domain, written through the
inclusion of `U` into the canonical domain, then it holds as an identity of morphisms out of `U`,
with `F` precomposed with the lift of `onePi` to `D` and `π` precomposed with the lift of the
multiplication to `V`. -/
theorem rationalAction_of_le_canonicalDomain (V : G.left.Opens) (π : V.toScheme ⟶ X.left)
    (hπ : π ≫ X.hom = V.ι ≫ G.hom) (D : (G ⊗ X).left.Opens) (F : D.toScheme ⟶ X.left)
    (U : (G ⊗ G).left.Opens) (hU : U ≤ canonicalDomain G X V π hπ D)
    (hRU : (G ⊗ G).left.homOfLE hU ≫ IsOpenImmersion.lift D.ι _
        (canonicalDomain_range G X V π hπ D) ≫ F =
      (G ⊗ G).left.homOfLE hU ≫ IsOpenImmersion.lift V.ι
        ((canonicalDomain G X V π hπ D).ι ≫ μ[G].left)
        (range_ι_comp_subset _ (canonicalDomain_le_mu G X V π hπ D)) ≫ π) :
    IsOpenImmersion.lift D.ι _ (range_onePi_subset_of_le_canonicalDomain G X V π hπ D U hU) ≫ F =
      IsOpenImmersion.lift V.ι (U.ι ≫ μ[G].left)
        (range_ι_comp_subset _ (hU.trans (canonicalDomain_le_mu G X V π hπ D))) ≫ π := by
  have e₁ : IsOpenImmersion.lift D.ι _
        (range_onePi_subset_of_le_canonicalDomain G X V π hπ D U hU) =
      (G ⊗ G).left.homOfLE hU ≫ IsOpenImmersion.lift D.ι _
        (canonicalDomain_range G X V π hπ D) := by
    rw [← cancel_mono D.ι, Category.assoc, IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac,
      ← Category.assoc, Scheme.homOfLE_homOfLE]
  have e₂ : IsOpenImmersion.lift V.ι (U.ι ≫ μ[G].left)
        (range_ι_comp_subset _ (hU.trans (canonicalDomain_le_mu G X V π hπ D))) =
      (G ⊗ G).left.homOfLE hU ≫ IsOpenImmersion.lift V.ι
        ((canonicalDomain G X V π hπ D).ι ≫ μ[G].left)
        (range_ι_comp_subset _ (canonicalDomain_le_mu G X V π hπ D)) := by
    rw [← cancel_mono V.ι, Category.assoc, IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac,
      Scheme.homOfLE_ι_assoc]
  rw [e₁, e₂, Category.assoc, Category.assoc]
  exact hRU

/-- Restricting a map into an open `A` along `A ≤ B` and including into the scheme recovers the
original map. -/
private theorem comp_homOfLE_comp_ι {Y : Scheme} {A B : Y.Opens} (h : A ≤ B) {T : Scheme}
    {z' : T ⟶ A.toScheme} {z : T ⟶ Y} (hz : z' ≫ A.ι = z) : (z' ≫ Y.homOfLE h) ≫ B.ι = z := by
  rw [Category.assoc, Scheme.homOfLE_ι, hz]

/-- **A flat rational quotient map whose fibres lie in the stabiliser of `s`.** Let `G` be an
integral group scheme over an algebraically closed field `k` such that, for every affine open `U`
and every field extension `κ` of `k`, every zero divisor of `Γ(G, U) ⊗[k] κ` is nilpotent (the
hypothesis `hC`), `U₀` an affine open and `s` a finite set of functions on `U₀`. Let `π : V ⟶ X` be
a dominant morphism from a nonempty affine open `V ⊆ U₀` to an integral separated `k`-scheme, such
that the restriction to `V` of every member of `s` is a coordinate function `π^* φ`, and let
`F : G × X ⇢ X` satisfy `F (a, π b) = π (a b)` on a dense open `U` of the canonical domain. Then
there is a nonempty open `W ⊆ V` on which `π` is flat, such that for any two `T`-points `x, y` of
`G` lying in `W` with `π x = π y`, `x⁻¹ y` right-stabilises every member of `s` on `U₀`. -/
theorem exists_open_flatAt_forall_rightStabilises [IsAlgClosed k] [IsIntegral G.left]
    [GeometricallyIrreducible G.hom] [IsIntegral X.left] [IsSeparated X.hom]
    (hC : ∀ U : G.left.Opens, IsAffineOpen U → letI := sectionsAlgebra G.hom U
      ∀ (κ : Type u) [Field κ] [Algebra k κ] (z : Γ(G.left, U) ⊗[k] κ),
        z ∉ nonZeroDivisors (Γ(G.left, U) ⊗[k] κ) → IsNilpotent z)
    {U₀ : G.left.Opens} (hU₀ : IsAffineOpen U₀) (s : Finset Γ(G.left, U₀))
    (V : G.left.Opens) (hVU₀ : V ≤ U₀) (hV : IsAffineOpen V) (hVne : (V : Set G.left).Nonempty)
    (π : V.toScheme ⟶ X.left) (hπ : π ≫ X.hom = V.ι ≫ G.hom) [IsDominant π]
    (hs : ∀ f ∈ s, ∃ φ : Γ(X.left, ⊤),
      V.topIso.hom (π.appTop φ) = G.left.presheaf.map (homOfLE hVU₀).op f)
    (D : (G ⊗ X).left.Opens) (F : D.toScheme ⟶ X.left) (hF : F ≫ X.hom = D.ι ≫ (G ⊗ X).hom)
    (U : (G ⊗ G).left.Opens) (hU : U ≤ canonicalDomain G X V π hπ D)
    (hUd : Dense (U : Set (G ⊗ G).left))
    (hRU : (G ⊗ G).left.homOfLE hU ≫ IsOpenImmersion.lift D.ι _
        (canonicalDomain_range G X V π hπ D) ≫ F =
      (G ⊗ G).left.homOfLE hU ≫ IsOpenImmersion.lift V.ι
        ((canonicalDomain G X V π hπ D).ι ≫ μ[G].left)
        (range_ι_comp_subset _ (canonicalDomain_le_mu G X V π hπ D)) ≫ π) :
    ∃ (W : G.left.Opens) (hWV : W ≤ V), (W : Set G.left).Nonempty ∧
      (∀ w (hw : w ∈ W), FlatAt π ⟨w, hWV hw⟩) ∧
      ∀ (T : Over (Spec (.of k))) (x y : T ⟶ G) (x' y' : T.left ⟶ W.toScheme),
        x' ≫ W.ι = x.left → y' ≫ W.ι = y.left →
        x' ≫ G.left.homOfLE hWV ≫ π = y' ≫ G.left.homOfLE hWV ≫ π →
        ∀ f ∈ s, RightStabilises (x⁻¹ * y) U₀ f := by
  obtain ⟨v, hv⟩ := hVne
  obtain ⟨p, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := G.hom) v v
    (Subsingleton.elim _ _)
  have : Nonempty (G ⊗ G).left := ⟨p⟩
  have hUne : (U : Set (G ⊗ G).left).Nonempty := hUd.nonempty
  obtain ⟨V', hV'V, hV'ne, hflat⟩ :=
    exists_open_flatAt_of_localRationalAction G X V π hπ D F hF U hU hUne hRU
  let O : G.left.Opens := ⟨(snd G G).left '' (U : Set (G ⊗ G).left),
    (pullback.snd G.hom G.hom).isOpenMap _ U.isOpen⟩
  have hOne : (O : Set G.left).Nonempty := hUne.image _
  let W := V' ⊓ O
  have hWV : W ≤ V := inf_le_left.trans hV'V
  have hWne : (W : Set G.left).Nonempty :=
    nonempty_preirreducible_inter V'.isOpen O.isOpen hV'ne hOne
  refine ⟨W, hWV, hWne, fun w hw ↦ hflat w hw.1, fun T x y x' y' hx hy hxy f hf ↦ ?_⟩
  obtain ⟨φ, hφ⟩ := hs f hf
  have hmem : ∀ (z : T ⟶ G) (z' : T.left ⟶ W.toScheme), z' ≫ W.ι = z.left →
      ∀ t, z.left t ∈ (snd G G).left '' (U : Set (G ⊗ G).left) := by
    intro z z' hz t
    have h1 : z.left t ∈ (W : Set G.left) := by
      rw [← hz, Scheme.Hom.comp_apply, ← Scheme.Opens.range_ι]
      exact ⟨_, rfl⟩
    exact h1.2
  refine RightStabilises.of_le hU₀ (hC U₀ hU₀) hVU₀ ⟨v, hv⟩ ?_
  rw [← hφ]
  exact rightStabilises_of_comp_eq X V hV (hC V hV) π hπ D F U
    (hU.trans (canonicalDomain_le_EV G X V π hπ D)) (hU.trans (canonicalDomain_le_mu G X V π hπ D))
    (range_onePi_subset_of_le_canonicalDomain G X V π hπ D U hU)
    (rationalAction_of_le_canonicalDomain G X V π hπ D F U hU hRU) x y
    (x' ≫ G.left.homOfLE hWV) (y' ≫ G.left.homOfLE hWV) (comp_homOfLE_comp_ι hWV hx)
    (comp_homOfLE_comp_ι hWV hy)
    (by simpa only [Category.assoc] using hxy) (hmem x x' hx) (hmem y y' hy) φ

/-- **A flat smooth affine rational quotient whose fibres lie in the stabiliser of `s`.**  In the
situation of `AlgebraicGeometry.exists_open_flatAt_forall_rightStabilises`, with `X` moreover
locally of finite type over `k`, there are a nonempty open `W ⊆ V`, a smooth affine `k`-scheme
`X₀` and a flat quasi-compact `k`-morphism `π₀ : W ⟶ X₀` (an open piece of `π`) such that any two
`T`-points `x, y` of `W` with `π₀ x = π₀ y` satisfy: `x⁻¹ y` right-stabilises every member of `s`
on `U₀`. -/
theorem exists_smooth_model_forall_rightStabilises [IsAlgClosed k] [IsIntegral G.left]
    [GeometricallyIrreducible G.hom] [IsIntegral X.left] [IsSeparated X.hom]
    [LocallyOfFiniteType X.hom]
    (hC : ∀ U : G.left.Opens, IsAffineOpen U → letI := sectionsAlgebra G.hom U
      ∀ (κ : Type u) [Field κ] [Algebra k κ] (z : Γ(G.left, U) ⊗[k] κ),
        z ∉ nonZeroDivisors (Γ(G.left, U) ⊗[k] κ) → IsNilpotent z)
    {U₀ : G.left.Opens} (hU₀ : IsAffineOpen U₀) (s : Finset Γ(G.left, U₀))
    (V : G.left.Opens) (hVU₀ : V ≤ U₀) (hV : IsAffineOpen V) (hVne : (V : Set G.left).Nonempty)
    (π : V.toScheme ⟶ X.left) (hπ : π ≫ X.hom = V.ι ≫ G.hom) [IsDominant π]
    (hs : ∀ f ∈ s, ∃ φ : Γ(X.left, ⊤),
      V.topIso.hom (π.appTop φ) = G.left.presheaf.map (homOfLE hVU₀).op f)
    (D : (G ⊗ X).left.Opens) (F : D.toScheme ⟶ X.left) (hF : F ≫ X.hom = D.ι ≫ (G ⊗ X).hom)
    (U : (G ⊗ G).left.Opens) (hU : U ≤ canonicalDomain G X V π hπ D)
    (hUd : Dense (U : Set (G ⊗ G).left))
    (hRU : (G ⊗ G).left.homOfLE hU ≫ IsOpenImmersion.lift D.ι _
        (canonicalDomain_range G X V π hπ D) ≫ F =
      (G ⊗ G).left.homOfLE hU ≫ IsOpenImmersion.lift V.ι
        ((canonicalDomain G X V π hπ D).ι ≫ μ[G].left)
        (range_ι_comp_subset _ (canonicalDomain_le_mu G X V π hπ D)) ≫ π) :
    ∃ (W : G.left.Opens) (X₀ : Over (Spec (.of k))) (_ : IsAffine X₀.left) (_ : Smooth X₀.hom)
      (π₀ : W.toScheme ⟶ X₀.left) (_ : π₀ ≫ X₀.hom = W.ι ≫ G.hom) (_ : QuasiCompact π₀)
      (_ : Flat π₀), (W : Set G.left).Nonempty ∧
      ∀ (T : Over (Spec (.of k))) (x y : T ⟶ G) (x' y' : T.left ⟶ W.toScheme),
        x' ≫ W.ι = x.left → y' ≫ W.ι = y.left → x' ≫ π₀ = y' ≫ π₀ →
        ∀ f ∈ s, RightStabilises (x⁻¹ * y) U₀ f := by
  obtain ⟨W, hWV, hWne, hflat, hfib⟩ := exists_open_flatAt_forall_rightStabilises G X hC hU₀ s V
    hVU₀ hV hVne π hπ hs D F hF U hU hUd hRU
  obtain ⟨X₀, hX₀a, hX₀s, j, -, -, W₀, hW₀, hW₀ne, -, π₀, hπ₀, hπ₀j, hflat₀, hqc₀⟩ :=
    exists_smooth_affine_model G.hom V X π hπ W hWV hWne hflat
  refine ⟨W₀, X₀, hX₀a, hX₀s, π₀, hπ₀, hqc₀, hflat₀, hW₀ne, fun T x y x' y' hx hy hxy ↦ ?_⟩
  have hcomp : ∀ z' : T.left ⟶ W₀.toScheme,
      (z' ≫ G.left.homOfLE hW₀) ≫ G.left.homOfLE hWV ≫ π = (z' ≫ π₀) ≫ j := by
    intro z'
    rw [Category.assoc, Scheme.homOfLE_homOfLE_assoc, Category.assoc, hπ₀j]
  refine hfib T x y (x' ≫ G.left.homOfLE hW₀) (y' ≫ G.left.homOfLE hW₀)
    (comp_homOfLE_comp_ι hW₀ hx) (comp_homOfLE_comp_ι hW₀ hy) ?_
  rw [hcomp, hcomp, hxy]

/-- **A flat smooth affine rational quotient of `Γ` whose fibres lie in the stabiliser of a given
finite family.**  Let `Γ` be an integral, geometrically irreducible group scheme over an
algebraically closed field `k` of characteristic zero, `U₀` a nonempty affine open of `Γ` and `s` a
finite set of functions on `U₀`.  There are a nonempty open `W` of `Γ`, a smooth affine `k`-scheme
`X₀` and a flat quasi-compact `k`-morphism `π₀ : W ⟶ X₀` such that any two `T`-points `x, y` of
`W` with `π₀ x = π₀ y` satisfy: `x⁻¹ y` right-stabilises every member of `s` on `U₀`. -/
theorem exists_flat_smooth_model_rightStabilises [IsAlgClosed k] [CharZero k]
    (Γ : Over (Spec (.of k))) [GrpObj Γ] [IsIntegral Γ.left] [GeometricallyIrreducible Γ.hom]
    {U₀ : Γ.left.Opens} (hU₀ : IsAffineOpen U₀) (hne₀ : (U₀ : Set Γ.left).Nonempty)
    (s : Finset Γ(Γ.left, U₀)) :
    ∃ (W : Γ.left.Opens) (X₀ : Over (Spec (.of k))) (_ : IsAffine X₀.left) (_ : Smooth X₀.hom)
      (π₀ : W.toScheme ⟶ X₀.left) (_ : π₀ ≫ X₀.hom = W.ι ≫ Γ.hom) (_ : QuasiCompact π₀)
      (_ : Flat π₀), (W : Set Γ.left).Nonempty ∧
      ∀ (T : Over (Spec (.of k))) (x y : T ⟶ Γ) (x' y' : T.left ⟶ W.toScheme),
        x' ≫ W.ι = x.left → y' ≫ W.ι = y.left → x' ≫ π₀ = y' ≫ π₀ →
        ∀ f ∈ s, RightStabilises (x⁻¹ * y) U₀ f := by
  classical
  let : Algebra k Γ.left.functionField := functionFieldAlgebra Γ
  have : Nonempty U₀ := ⟨⟨_, hne₀.some_mem⟩⟩
  obtain ⟨K₁, ⟨t, ht⟩, hsK₁, hK₁⟩ :=
    exists_fg_leftInvariant_functionField Γ (s.image (Γ.left.germToFunctionField U₀))
  obtain ⟨X, V, hVU₀, hV, hgV, π, hπ, hXa, hXi, hXl, hπd, hs, hadj, htπ⟩ :=
    exists_affineQuotientModel Γ U₀ hU₀ s t
  have := hXa
  have := hXi
  have := hXl
  have := hπd
  have hπK₁ : ∀ φ : Γ(X.left, ⊤), Γ.left.presheaf.germ V (genericPoint Γ.left) hgV
      (V.topIso.hom (π.appTop φ)) ∈ K₁ := by
    intro φ
    refine (IntermediateField.adjoin_le_iff.mpr ?_) (hadj φ)
    rintro _ (hx | ⟨f, hf, rfl⟩)
    · rw [← ht]
      exact IntermediateField.subset_adjoin k _ hx
    · exact hsK₁ (by simpa using ⟨f, hf, rfl⟩)
  obtain ⟨D, F, hF, U, hU, hUd, hRU⟩ := exists_localRationalAction_of_leftInvariant Γ X V hgV π hπ
    K₁ hK₁ t ht.ge htπ hπK₁
  exact exists_smooth_model_forall_rightStabilises Γ X
    (zeroDivisors_isNilpotent_tensor_of_charZero k (Grp.mk Γ)) hU₀ s V hVU₀ hV ⟨_, hgV⟩ π hπ hs
    D F hF U hU hUd hRU

end AlgebraicGeometry

end
