module

public import StacksFrontier.Algebra.Homology.DoubleQuasiIso
public import StacksFrontier.RingTheory.NaiveCotangent.Defs

/-!
# Two-term complexes and their doubles: comparison of quasi-isomorphy

A `NaiveCotangent.TwoTerm S` is a two-term chain complex of `S`-modules `X₁ --d--> X₀`, and a
`NaiveCotangent.ChainMap` between two of them is a commuting pair `(f₁, f₀)` of `S`-linear maps;
such a chain map is a `NaiveCotangent.IsQuasiIso` when it is bijective on `H₁ = ker d` and on
`H₀ = coker d`. The same mathematical object is carried by the cochain complex
`HomologicalComplex.double (ModuleCat.ofHom d)`, which is `d` placed in degrees `-1` and `0` and
zero elsewhere, and there quasi-isomorphy is the categorical `QuasiIso`. This file shows that a
quasi-isomorphism of two-term complexes induces a quasi-isomorphism of the associated doubles.

## Main definitions

* `Stacks.TwoTermDoubleQuasiIso.mapDouble`: the morphism of cochain complexes induced by a chain
  map of two-term complexes, with components `f₁` in degree `-1` and `f₀` in degree `0`.

## Main results

* `Stacks.TwoTermDoubleQuasiIso.eq_zero_of_injective_onH₁`,
  `Stacks.TwoTermDoubleQuasiIso.exists_eq_of_surjective_onH₁`,
  `Stacks.TwoTermDoubleQuasiIso.exists_d_eq_of_injective_onH₀` and
  `Stacks.TwoTermDoubleQuasiIso.exists_add_d_eq_of_surjective_onH₀`: bijectivity of the maps
  induced on `H₁ = ker d` and on `H₀ = coker d`, read elementwise.
* `Stacks.TwoTermDoubleQuasiIso.quasiIso_mapDouble`: a quasi-isomorphism of two-term complexes
  induces a quasi-isomorphism of the associated doubles.

## References

* [The Stacks Project, Lemma 00S1](https://stacks.math.columbia.edu/tag/00S1)
* [The Stacks Project, Lemma 0D0K](https://stacks.math.columbia.edu/tag/0D0K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits NaiveCotangent

universe u v

namespace Stacks.TwoTermDoubleQuasiIso

variable {S : Type u} [CommRing S]

/-- The degree-`(-1)` term of the cochain complex attached to a two-term complex
`X₁ --d--> X₀` is `X₁`, as an identification of additive groups. -/
noncomputable def equivNegOne (A : TwoTerm.{u, v, v} S)
    (hd : (ComplexShape.up ℤ).Rel (-1 : ℤ) 0) :
    (HomologicalComplex.double (ModuleCat.ofHom A.d) hd).X (-1) ≃+ A.X₁ :=
  (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom A.d) hd).toLinearEquiv.toAddEquiv

/-- The degree-`0` term of the cochain complex attached to a two-term complex
`X₁ --d--> X₀` is `X₀`, as an identification of additive groups. -/
noncomputable def equivZero (A : TwoTerm.{u, v, v} S)
    (hd : (ComplexShape.up ℤ).Rel (-1 : ℤ) 0) :
    (HomologicalComplex.double (ModuleCat.ofHom A.d) hd).X 0 ≃+ A.X₀ :=
  (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom A.d) hd
    TwoTerm.negOne_ne_zero).toLinearEquiv.toAddEquiv

/-- The identification of the degree-`(-1)` term with `X₁` is the structural isomorphism
`HomologicalComplex.doubleXIso₀`. -/
@[simp]
theorem equivNegOne_apply (A : TwoTerm.{u, v, v} S)
    (hd : (ComplexShape.up ℤ).Rel (-1 : ℤ) 0)
    (x : (HomologicalComplex.double (ModuleCat.ofHom A.d) hd).X (-1)) :
    equivNegOne A hd x = (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom A.d) hd).hom x :=
  rfl

/-- The identification of the degree-`0` term with `X₀` is the structural isomorphism
`HomologicalComplex.doubleXIso₁`. -/
@[simp]
theorem equivZero_apply (A : TwoTerm.{u, v, v} S) (hd : (ComplexShape.up ℤ).Rel (-1 : ℤ) 0)
    (x : (HomologicalComplex.double (ModuleCat.ofHom A.d) hd).X 0) :
    equivZero A hd x =
      (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom A.d) hd TwoTerm.negOne_ne_zero).hom x :=
  rfl

/-- The only nonzero differential of the cochain complex attached to a two-term complex
`X₁ --d--> X₀` is `d` itself, read through the identifications of the two nonzero terms. -/
theorem equivZero_d (A : TwoTerm.{u, v, v} S) (hd : (ComplexShape.up ℤ).Rel (-1 : ℤ) 0)
    (x : (HomologicalComplex.double (ModuleCat.ofHom A.d) hd).X (-1)) :
    equivZero A hd ((HomologicalComplex.double (ModuleCat.ofHom A.d) hd).d (-1) 0 x) =
      A.d (equivNegOne A hd x) := by
  simp [HomologicalComplex.double_d (ModuleCat.ofHom A.d) hd TwoTerm.negOne_ne_zero]

/-- The commuting square `d_B ∘ f₁ = f₀ ∘ d_A` of a chain map of two-term complexes, read as a
square in the category of `S`-modules. -/
theorem ofHom_comm {A B : TwoTerm.{u, v, v} S} (f : ChainMap A B) :
    ModuleCat.ofHom f.f₁ ≫ ModuleCat.ofHom B.d =
      ModuleCat.ofHom A.d ≫ ModuleCat.ofHom f.f₀ := by
  rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp, f.comm]

/-- The morphism of doubles induced by a chain map of two-term complexes: a chain map
`(f₁, f₀) : (X₁ --d_A--> X₀) → (Y₁ --d_B--> Y₀)` induces a morphism of the cochain complexes
concentrated in degrees `-1` and `0` attached to `d_A` and `d_B`, acting by `f₁` in degree `-1` and
by `f₀` in degree `0`. -/
noncomputable def mapDouble {A B : TwoTerm.{u, v, v} S} (f : ChainMap A B)
    (hd : (ComplexShape.up ℤ).Rel (-1 : ℤ) 0) :
    HomologicalComplex.double (ModuleCat.ofHom A.d) hd ⟶
      HomologicalComplex.double (ModuleCat.ofHom B.d) hd :=
  HomologicalComplex.mkHomFromDouble hd TwoTerm.negOne_ne_zero
    (ModuleCat.ofHom f.f₁ ≫ (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom B.d) hd).inv)
    (ModuleCat.ofHom f.f₀ ≫
      (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom B.d) hd TwoTerm.negOne_ne_zero).inv)
    (by
      rw [HomologicalComplex.double_d (ModuleCat.ofHom B.d) hd TwoTerm.negOne_ne_zero,
        Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc, ofHom_comm f, Category.assoc])
    (fun k _ => by
      rw [HomologicalComplex.double_d_eq_zero₀ (ModuleCat.ofHom B.d) hd 0 k (by decide),
        comp_zero])

/-- In degree `-1` the induced morphism of doubles is `f₁`, conjugated by the identifications of
the degree-`(-1)` terms. -/
@[simp]
theorem mapDouble_f_negOne {A B : TwoTerm.{u, v, v} S} (f : ChainMap A B)
    (hd : (ComplexShape.up ℤ).Rel (-1 : ℤ) 0) :
    (mapDouble f hd).f (-1) =
      (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom A.d) hd).hom ≫ ModuleCat.ofHom f.f₁ ≫
        (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom B.d) hd).inv := by
  simp only [mapDouble, HomologicalComplex.mkHomFromDouble_f₀]

/-- In degree `0` the induced morphism of doubles is `f₀`, conjugated by the identifications of
the degree-`0` terms. -/
@[simp]
theorem mapDouble_f_zero {A B : TwoTerm.{u, v, v} S} (f : ChainMap A B)
    (hd : (ComplexShape.up ℤ).Rel (-1 : ℤ) 0) :
    (mapDouble f hd).f 0 =
      (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom A.d) hd TwoTerm.negOne_ne_zero).hom ≫
        ModuleCat.ofHom f.f₀ ≫
          (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom B.d) hd TwoTerm.negOne_ne_zero).inv := by
  simp only [mapDouble, HomologicalComplex.mkHomFromDouble_f₁]

/-- The degree-`(-1)` component of the induced morphism of doubles is `f₁`, read through the
identifications of the degree-`(-1)` terms. -/
theorem equivNegOne_mapDouble {A B : TwoTerm.{u, v, v} S} (f : ChainMap A B)
    (hd : (ComplexShape.up ℤ).Rel (-1 : ℤ) 0)
    (x : (HomologicalComplex.double (ModuleCat.ofHom A.d) hd).X (-1)) :
    equivNegOne B hd ((mapDouble f hd).f (-1) x) = f.f₁ (equivNegOne A hd x) := by
  simp

/-- The degree-`0` component of the induced morphism of doubles is `f₀`, read through the
identifications of the degree-`0` terms. -/
theorem equivZero_mapDouble {A B : TwoTerm.{u, v, v} S} (f : ChainMap A B)
    (hd : (ComplexShape.up ℤ).Rel (-1 : ℤ) 0)
    (x : (HomologicalComplex.double (ModuleCat.ofHom A.d) hd).X 0) :
    equivZero B hd ((mapDouble f hd).f 0 x) = f.f₀ (equivZero A hd x) := by
  simp

/-! ### The two bijectivity conditions, read elementwise -/

/-- If the map induced on `H₁ = ker d` by a chain map is injective, then an element of `X₁` killed
both by `d_A` and by `f₁` is zero. -/
theorem eq_zero_of_injective_onH₁ {A B : TwoTerm.{u, v, v} S} {f : ChainMap A B}
    (hf : Function.Injective f.onH₁) (x : A.X₁) (hx : A.d x = 0) (hfx : f.f₁ x = 0) : x = 0 := by
  have h0 : f.onH₁ ⟨x, LinearMap.mem_ker.mpr hx⟩ = f.onH₁ 0 := by
    rw [map_zero]
    exact Subtype.ext (by
      simpa only [ChainMap.onH₁, LinearMap.coe_restrict_apply, ZeroMemClass.coe_zero] using hfx)
  simpa using congrArg Subtype.val (hf h0)

/-- If the map induced on `H₁ = ker d` by a chain map is surjective, then every element of `Y₁`
killed by `d_B` is `f₁` of an element of `X₁` killed by `d_A`. -/
theorem exists_eq_of_surjective_onH₁ {A B : TwoTerm.{u, v, v} S} {f : ChainMap A B}
    (hf : Function.Surjective f.onH₁) (y : B.X₁) (hy : B.d y = 0) :
    ∃ x : A.X₁, A.d x = 0 ∧ f.f₁ x = y := by
  obtain ⟨a, ha⟩ := hf ⟨y, LinearMap.mem_ker.mpr hy⟩
  exact ⟨a, LinearMap.mem_ker.mp a.2, by
    simpa only [ChainMap.onH₁, LinearMap.coe_restrict_apply] using congrArg Subtype.val ha⟩

/-- If the map induced on `H₀ = coker d` by a chain map is injective and `f₀ x` is in the image of
`d_B`, then `x` is in the image of `d_A`. -/
theorem exists_d_eq_of_injective_onH₀ {A B : TwoTerm.{u, v, v} S} {f : ChainMap A B}
    (hf : Function.Injective f.onH₀) (x : A.X₀) (hx : ∃ y : B.X₁, B.d y = f.f₀ x) :
    ∃ z : A.X₁, A.d z = x := by
  obtain ⟨y, hy⟩ := hx
  have h0 : f.onH₀ (Submodule.Quotient.mk x) = f.onH₀ 0 := by
    rw [map_zero, ChainMap.onH₀, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨y, hy⟩
  exact LinearMap.mem_range.mp ((Submodule.Quotient.mk_eq_zero _).mp (hf h0))

/-- If the map induced on `H₀ = coker d` by a chain map is surjective, then every element of `Y₀`
is the sum of a value of `f₀` and an element of the image of `d_B`. -/
theorem exists_add_d_eq_of_surjective_onH₀ {A B : TwoTerm.{u, v, v} S} {f : ChainMap A B}
    (hf : Function.Surjective f.onH₀) (y : B.X₀) :
    ∃ (x : A.X₀) (z : B.X₁), f.f₀ x + B.d z = y := by
  obtain ⟨c, hc⟩ := hf (Submodule.Quotient.mk y)
  obtain ⟨x, rfl⟩ := (LinearMap.range A.d).mkQ_surjective c
  rw [Submodule.mkQ_apply, ChainMap.onH₀, Submodule.mapQ_apply, Submodule.Quotient.eq] at hc
  obtain ⟨w, hw⟩ := hc
  exact ⟨x, -w, by rw [map_neg, hw]; abel⟩

/-! ### Quasi-isomorphism of the doubles -/

/-- If a chain map `(f₁, f₀)` of two-term complexes of `S`-modules is bijective on `H₁ = ker d` and
on `H₀ = coker d`, then the morphism it induces between the cochain complexes concentrated in
degrees `-1` and `0` attached to the two differentials is a quasi-isomorphism. -/
theorem quasiIso_mapDouble {A B : TwoTerm.{u, v, v} S} {f : ChainMap A B}
    (hd : (ComplexShape.up ℤ).Rel (-1 : ℤ) 0) (hf : IsQuasiIso f) :
    QuasiIso (mapDouble f hd) := by
  refine CochainComplex.quasiIso_of_isZero_X_of_bijective (mapDouble f hd)
    (fun i h₁ h₀ => HomologicalComplex.isZero_double_X _ hd i h₁ h₀)
    (fun i h₁ h₀ => HomologicalComplex.isZero_double_X _ hd i h₁ h₀) ?_ ?_ ?_ ?_
  · exact CochainComplex.eq_zero_of_d_eq_zero_of_addEquiv (u₀ := equivZero A hd)
      (equivZero_d A hd) (equivNegOne_mapDouble f hd)
      (fun m hm hfm => eq_zero_of_injective_onH₁ hf.1.1 m hm hfm)
  · exact CochainComplex.exists_of_d_eq_zero_of_addEquiv (u₀ := equivZero A hd)
      (v₀ := equivZero B hd) (equivZero_d A hd) (equivZero_d B hd) (equivNegOne_mapDouble f hd)
      (fun m hm => exists_eq_of_surjective_onH₁ hf.1.2 m hm)
  · exact CochainComplex.exists_d_eq_of_addEquiv (u₁ := equivNegOne A hd)
      (v₁ := equivNegOne B hd) (equivZero_d A hd) (equivZero_d B hd) (equivZero_mapDouble f hd)
      (fun n hn => exists_d_eq_of_injective_onH₀ hf.2.1 n hn)
  · exact CochainComplex.exists_add_d_eq_of_addEquiv (v₁ := equivNegOne B hd)
      (u₀ := equivZero A hd) (equivZero_d B hd) (equivZero_mapDouble f hd)
      (fun n => exists_add_d_eq_of_surjective_onH₀ hf.2.2 n)

end Stacks.TwoTermDoubleQuasiIso

end
