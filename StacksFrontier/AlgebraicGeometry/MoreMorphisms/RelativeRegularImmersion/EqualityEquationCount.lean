module

public import StacksFrontier.AlgebraicGeometry.FiberCotangentAssembly.Transport
public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.KoszulRegularSmoothCover
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.Containing
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.FibreEquationCount
public import StacksFrontier.RingTheory.Ideal.InvertibleGeneratorChange
public import StacksCore.Tactic.StacksAttribute

/-!
# The equation count of Stacks tag 063W, item (3)

Stacks tag 063W is a four-part lemma about a closed subscheme `T` of a scheme `X` flat and
locally of finite presentation over a base `S`, at a point `x` of `T` whose fibre `T_s ⊆ X_s` is
a quasi-regular immersion near `x`.  Its third item assumes in addition that `T` is cut out near
`x` by `c` equations with `c = dim_x(X_s) - dim_x(T_s)`, and concludes that the relative
quasi-regular immersion `Z` of the first item can be taken to be `T` itself:  there is an open
`U ∋ x` with `T ∩ U = Z`.

This file proves that item.  As for item (2), taking `Z = T ∩ U` makes the remaining assertions
of item (1) hold by construction, so the content is that `T ∩ U ⊆ U` is a relative quasi-regular
immersion over `S`;  the closing sentence of the lemma, that `Z → U` is a regular immersion, is
carried along as the second conjunct and comes from Stacks tag 063U.

## Main results

* `Stacks.AlgebraicGeometry.germ_app_fiberι`: the germ of a section in the local ring of the
  fibre is the class of its germ on `X`.
* `Stacks.AlgebraicGeometry.flat_quotient_away_of_flat_quotient` and
  `Stacks.AlgebraicGeometry.flat_quotient_res_basicOpen`: a flat quotient stays flat after
  localizing away from an element, on rings and on an affine chart.
* `Stacks.AlgebraicGeometry.exists_mem_isRelativeQuasiRegularImmersion_of_dim_eq`: item (3) of
  Stacks tag 063W.

## Implementation notes

The proof compares two families of generators in the local ring `𝒪_{X_s, x}` of the fibre.  The
chart of item (1)
(`Stacks.AlgebraicGeometry.exists_affineOpen_isWeaklyRegular_flat_quotient_ideal_fibre`)
supplies a family `a` of `r` sections cutting out `Z`, regular in that local ring;  the
hypothesis of item (3) supplies a family `g` of `c` sections cutting out `T`, regular in that
local ring by the equation count
(`Stacks.AlgebraicGeometry.isRegular_of_span_eq_stalkIdeal_fiber_of_dim_eq`).  Both generate the
same ideal there, so both lengths are its minimal number of generators
(`Koszul.spanFinrank_eq_length_of_isRegular`) and `r = c`.

With the two families of equal length, `T ∩ V ⊆ Z` gives a *square* matrix `b` over `Γ(X, V)`
with `a = b ⬝ g`, and regularity of `a` makes `det b` invertible in `𝒪_{X_s, x}`
(`Stacks.RingTheory.exists_matrix_isUnit_det_map`), hence in `𝒪_{X, x}`.  On the basic open
`U = D(det b)` the two families then generate the same ideal
(`Stacks.RingTheory.span_range_mulVec_eq_of_isUnit_det`), so `T ∩ U = Z ∩ U`, and the chart data
restricted to `U` exhibits `T ∩ U` as a relative quasi-regular immersion.

The passage between the local ring of the fibre and the quotient of `𝒪_{X, x}` by the extended
maximal ideal of `𝒪_{S, s}` is `AlgebraicGeometry.quotientStalkEquivFiberStalk`, read on germs by
`Stacks.AlgebraicGeometry.germ_app_fiberι`.

## References

* [Stacks Project, Lemma 31.22.8 (Tag 063W)](https://stacks.math.columbia.edu/tag/063W)
* [Stacks Project, Lemma 31.22.4 (Tag 063U)](https://stacks.math.columbia.edu/tag/063U)
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry RingTheory.Sequence
open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace Stacks.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}}

/-- **The germ of a section in the local ring of the fibre.**  It is the class of the germ on `X`
modulo the extended maximal ideal of the local ring of the base. -/
theorem germ_app_fiberι (f : X ⟶ S) (x : X) {V : X.Opens} (hxV : x ∈ V)
    (hmem : f.asFiber x ∈ f.fiberι (f x) ⁻¹ᵁ V) (s : Γ(X, V)) :
    ((f.fiber (f x)).presheaf.germ (f.fiberι (f x) ⁻¹ᵁ V) (f.asFiber x) hmem).hom
        (((f.fiberι (f x)).app V).hom s)
      = quotientStalkEquivFiberStalk f x
          (Ideal.Quotient.mk (Ideal.map (f.stalkMap x).hom
            (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))))
            ((X.presheaf.germ V x hxV).hom s)) := by
  have hy : f.fiberι (f x) (f.asFiber x) ∈ V := hmem
  have hcongr := congrArg
    (fun θ : Γ(X, V) ⟶ X.presheaf.stalk (f.fiberι (f x) (f.asFiber x)) => θ.hom s)
    (Stacks.FiberCotangentAssembly.germ_stalkCongr X.presheaf hxV
      (Inseparable.of_eq (f.fiberι_asFiber x).symm) hy)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hcongr
  rw [quotientStalkEquivFiberStalk_mk, hcongr, Scheme.Hom.germ_stalkMap_apply]

/-- **A flat quotient stays flat after localizing away from an element.**  The localization of
`B / I` away from the image of `g` is flat over `B / I`, which is flat over `A`. -/
theorem flat_quotient_away_of_flat_quotient {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (I : Ideal B) (g : B) (hflat : Module.Flat A (B ⧸ I)) :
    Module.Flat A (Localization.Away g ⧸ I.map (algebraMap B (Localization.Away g))) := by
  have _ : IsLocalization (Submonoid.powers (algebraMap B (B ⧸ I) g))
      (Localization.Away g ⧸ I.map (algebraMap B (Localization.Away g))) := by
    rw [← Algebra.algebraMapSubmonoid_powers (S := B ⧸ I) g]
    infer_instance
  have _ : Module.Flat (B ⧸ I)
      (Localization.Away g ⧸ I.map (algebraMap B (Localization.Away g))) :=
    IsLocalization.flat _ (Submonoid.powers (algebraMap B (B ⧸ I) g))
  have _ : IsScalarTower A (B ⧸ I)
      (Localization.Away g ⧸ I.map (algebraMap B (Localization.Away g))) :=
    .of_algebraMap_eq fun _ => rfl
  have _ := hflat
  exact Module.Flat.trans A (B ⧸ I) _

/-- **The flat quotient of an affine chart restricted to a basic open.**  The sections over a
basic open of an affine open are a localization, and the quotient by the extended ideal stays
flat over the base. -/
theorem flat_quotient_res_basicOpen (f : X ⟶ S) {W : S.Opens} {V : X.Opens}
    (hV : IsAffineOpen V) (hVW : V ≤ f ⁻¹ᵁ W) {r : ℕ} (a : Fin r → Γ(X, V)) (t : Γ(X, V))
    (hflat : ((Ideal.Quotient.mk (Ideal.span (Set.range a))).comp (f.appLE W V hVW).hom).Flat)
    (hUW : X.basicOpen t ≤ f ⁻¹ᵁ W) :
    ((Ideal.Quotient.mk (Ideal.span (Set.range fun i =>
          (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom (a i)))).comp
        (f.appLE W (X.basicOpen t) hUW).hom).Flat := by
  letI : Algebra Γ(S, W) Γ(X, V) := (f.appLE W V hVW).hom.toAlgebra
  letI : Algebra Γ(S, W) Γ(X, X.basicOpen t) :=
    (f.appLE W (X.basicOpen t) hUW).hom.toAlgebra
  have _ : IsLocalization.Away t Γ(X, X.basicOpen t) := hV.isLocalization_basicOpen t
  have halgV : algebraMap Γ(X, V) Γ(X, X.basicOpen t)
      = (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom := RingHom.algebraMap_toAlgebra _
  have _ : IsScalarTower Γ(S, W) Γ(X, V) Γ(X, X.basicOpen t) := by
    refine .of_algebraMap_eq fun z => ?_
    have h := congrArg (fun ψ : Γ(S, W) ⟶ Γ(X, X.basicOpen t) => ψ.hom z)
      (Scheme.Hom.appLE_map f hVW (homOfLE (X.basicOpen_le t)).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
    rw [halgV]
    exact h.symm
  have hflatB : Module.Flat Γ(S, W) (Γ(X, V) ⧸ Ideal.span (Set.range a)) :=
    RingHom.flat_algebraMap_iff.mp hflat
  have hflatAway := flat_quotient_away_of_flat_quotient (A := Γ(S, W))
    (Ideal.span (Set.range a)) t hflatB
  have hflatV := flat_quotient_map_away_of_abstract (A := Γ(S, W))
    (O := Γ(X, X.basicOpen t)) t (Ideal.span (Set.range a)) hflatAway
  rw [halgV, Ideal.map_span, ← Set.range_comp, Function.comp_def] at hflatV
  exact RingHom.flat_algebraMap_iff.mpr hflatV

/-- **A point of the support of a closed subscheme lies in the support of its fibre.** -/
theorem asFiber_mem_support_comap (f : X ⟶ S) (T : X.IdealSheafData) (x : X)
    (hx : x ∈ T.support) : f.asFiber x ∈ (T.comap (f.fiberι (f x))).support := by
  rw [Scheme.IdealSheafData.support_comap]
  show f.fiberι (f x) (f.asFiber x) ∈ T.support
  rw [f.fiberι_asFiber x]
  exact hx

/-- **Stacks tag 063W, item (3).**  Let `f : X ⟶ S` be flat and locally of finite presentation,
let `T` be a closed subscheme of `X` and let `x` be a point of `T` such that the fibre of `T`
over `f x` is a quasi-regular immersion on a neighbourhood of `x`.  Assume that `T` is cut out on
an affine open neighbourhood of `x` by `n` equations, and that `n` is the drop in local dimension
from the fibre `X_s` to the fibre `T_s` at `x`.  Then there is an open `U ∋ x` on which `T`
itself is a relative quasi-regular immersion over `S`, and a regular immersion. -/
@[stacks 063W "item (3): equation count"]
theorem exists_mem_isRelativeQuasiRegularImmersion_of_dim_eq (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] (T : X.IdealSheafData) (x : X) (hx : x ∈ T.support)
    (hfib : ∃ V : (f.fiber (f x)).Opens, f.asFiber x ∈ V ∧ IsQuasiRegularImmersion
      (((T.comap (f.fiberι (f x))).comap V.ι).subschemeι))
    {n : ℕ} {U₀ : X.Opens} (hU₀ : IsAffineOpen U₀) (hxU₀ : x ∈ U₀) (g : Fin n → Γ(X, U₀))
    (hg : T.ideal ⟨U₀, hU₀⟩ = Ideal.span (Set.range g))
    (hdim : topologicalKrullDimAt (T.comap (f.fiberι (f x))).subscheme
          ⟨f.asFiber x, asFiber_mem_support_comap f T x hx⟩ + (n : WithBot ℕ∞)
        = topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x)) :
    ∃ U : X.Opens, x ∈ U ∧
      IsRelativeQuasiRegularImmersion (U.ι ≫ f) (T.comap U.ι).subschemeι ∧
        IsRegularImmersion (T.comap U.ι).subschemeι := by
  classical
  obtain ⟨W, hW, V, hV, hVW, hxV, hVU₀, r, a, haI, hwr, hflatq, hfibeq, hQreg⟩ :=
    exists_affineOpen_isWeaklyRegular_flat_quotient_ideal_fibre f T x hx hfib U₀ hxU₀
  have _ : IsLocallyNoetherian (f.fiber (f x)) := isLocallyNoetherian_fiber f (f x)
  have hxs : f.asFiber x ∈ (T.comap (f.fiberι (f x))).support :=
    asFiber_mem_support_comap f T x hx
  have hmemV : f.asFiber x ∈ f.fiberι (f x) ⁻¹ᵁ V := by
    show f.fiberι (f x) (f.asFiber x) ∈ V
    rw [f.fiberι_asFiber x]
    exact hxV
  rw [Scheme.Hom.appLE_eq_app] at hfibeq
  set φ : Γ(X, V) →+* (f.fiber (f x)).presheaf.stalk (f.asFiber x) :=
    ((f.fiber (f x)).presheaf.germ (f.fiberι (f x) ⁻¹ᵁ V) (f.asFiber x) hmemV).hom.comp
      ((f.fiberι (f x)).app V).hom with hφdef
  -- the generators of `T` restricted to the chart
  set gV : Fin n → Γ(X, V) := fun j => (X.presheaf.map (homOfLE hVU₀).op).hom (g j) with hgVdef
  have hTV : T.ideal ⟨V, hV⟩ = Ideal.span (Set.range gV) := by
    rw [← T.map_ideal (U := ⟨V, hV⟩) (V := ⟨U₀, hU₀⟩) hVU₀, hg, Ideal.map_span, ← Set.range_comp]
    rfl
  -- the ideal cut out in the local ring of the fibre, read off each family
  have hIa : stalkIdeal (T.comap (f.fiberι (f x))) (f.asFiber x) hxs
      = Ideal.span (Set.range fun i => φ (a i)) := by
    rw [stalkIdeal_eq_map_germ _ _ hxs (hV.preimage (f.fiberι (f x))) hmemV, hfibeq,
      Ideal.map_span, ← Set.range_comp]
    rfl
  have hIg : stalkIdeal (T.comap (f.fiberι (f x))) (f.asFiber x) hxs
      = Ideal.span (Set.range fun j => φ (gV j)) := by
    rw [stalkIdeal_eq_map_germ _ _ hxs (hV.preimage (f.fiberι (f x))) hmemV,
      Stacks.IdealSheaf.ideal_comap_of_isAffineHom T (f.fiberι (f x)) ⟨V, hV⟩, hTV,
      Ideal.map_map, Ideal.map_span, ← Set.range_comp]
    rfl
  -- the equation count makes the generators of `T` a regular sequence on the fibre
  have hgreg : IsRegular ((f.fiber (f x)).presheaf.stalk (f.asFiber x))
      (List.ofFn fun j => φ (gV j)) :=
    isRegular_of_span_eq_stalkIdeal_fiber_of_dim_eq f T x hfib hxs hdim _ hIg
  -- the chart family is a regular sequence on the fibre
  have hareg : IsRegular ((f.fiber (f x)).presheaf.stalk (f.asFiber x))
      (List.ofFn fun i => φ (a i)) := by
    have hψ := isRegular_map_ringEquiv (quotientStalkEquivFiberStalk f x) hQreg
    have hbridge : ∀ i, (quotientStalkEquivFiberStalk f x) (Ideal.Quotient.mk
        (Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))))
        ((X.presheaf.germ V x hxV).hom (a i))) = φ (a i) :=
      fun i => (germ_app_fiberι f x hxV hmemV (a i)).symm
    simpa only [hbridge] using hψ
  -- the two families have the same length
  have hnr : n = r := by
    have h1 := Koszul.spanFinrank_eq_length_of_isRegular _ hgreg
    have h2 := Koszul.spanFinrank_eq_length_of_isRegular _ hareg
    rw [Ideal.ofList_ofFn, ← hIg] at h1
    rw [Ideal.ofList_ofFn, ← hIa] at h2
    simpa using h1.symm.trans h2
  subst hnr
  -- the change of generators, and the invertibility of its determinant
  have hmaxR : ∀ i, φ (a i)
      ∈ IsLocalRing.maximalIdeal ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) := by
    intro i
    refine IsLocalRing.le_maximalIdeal (stalkIdeal_ne_top _ _ hxs) ?_
    rw [hIa]
    exact Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨b, hab, hdetu⟩ := Stacks.RingTheory.exists_matrix_isUnit_det_map φ a gV
    (fun i => hTV ▸ haI i) hareg.1 hmaxR (hIa.symm.trans hIg)
  have hPle : Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))
      ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    refine IsLocalRing.le_maximalIdeal fun htop => ?_
    have _ : Nontrivial (X.presheaf.stalk x ⧸ Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))) :=
      (quotientStalkEquivFiberStalk f x).toEquiv.nontrivial
    exact not_subsingleton _ (Ideal.Quotient.subsingleton_iff.mpr htop)
  have hdetX : IsUnit ((X.presheaf.germ V x hxV).hom b.det) := by
    have hQ : IsUnit (Ideal.Quotient.mk (Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))))
        ((X.presheaf.germ V x hxV).hom b.det)) := by
      have hdetu' := hdetu
      rw [hφdef, RingHom.comp_apply, germ_app_fiberι f x hxV hmemV b.det] at hdetu'
      simpa using hdetu'.map (quotientStalkEquivFiberStalk f x).symm.toRingHom
    by_contra hcon
    obtain ⟨v, hv⟩ := hQ.exists_right_inv
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective v
    have hsub : (X.presheaf.germ V x hxV).hom b.det * u - 1
        ∈ Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hv, map_one, sub_self]
    have hmax : (X.presheaf.germ V x hxV).hom b.det
        ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
      (IsLocalRing.mem_maximalIdeal _).mpr hcon
    have hone : (1 : X.presheaf.stalk x) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
      have h1 : (1 : X.presheaf.stalk x) = (X.presheaf.germ V x hxV).hom b.det * u
          - ((X.presheaf.germ V x hxV).hom b.det * u - 1) := by ring
      rw [h1]
      exact sub_mem (Ideal.mul_mem_right _ _ hmax) (hPle hsub)
    exact (IsLocalRing.mem_maximalIdeal 1).mp hone isUnit_one
  -- the chart shrunk to where the determinant is invertible
  have hxU : x ∈ X.basicOpen b.det := (X.mem_basicOpen b.det x hxV).mpr hdetX
  have hUa : IsAffineOpen (X.basicOpen b.det) := hV.basicOpen _
  have hUV : X.basicOpen b.det ≤ V := X.basicOpen_le _
  have hUW : X.basicOpen b.det ≤ f ⁻¹ᵁ W := hUV.trans hVW
  set ρ : Γ(X, V) →+* Γ(X, X.basicOpen b.det) :=
    (X.presheaf.map (homOfLE hUV).op).hom with hρdef
  have _ : IsLocalization.Away b.det Γ(X, X.basicOpen b.det) := hV.isLocalization_basicOpen _
  have hρalg : algebraMap Γ(X, V) Γ(X, X.basicOpen b.det) = ρ := RingHom.algebraMap_toAlgebra _
  have hdetU : IsUnit (ρ b.det) := hρalg ▸ IsLocalization.Away.algebraMap_isUnit b.det
  have hmul : (fun i => ρ (a i)) = (ρ.mapMatrix b).mulVec fun j => ρ (gV j) := by
    funext i
    show ρ (a i) = ∑ j, ρ (b i j) * ρ (gV j)
    rw [congrFun hab i]
    show ρ (∑ j, b i j * gV j) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => map_mul ρ _ _
  have hspanU : Ideal.span (Set.range fun i => ρ (a i))
      = Ideal.span (Set.range fun j => ρ (gV j)) := by
    rw [hmul]
    exact Stacks.RingTheory.span_range_mulVec_eq_of_isUnit_det _
      (by rw [← RingHom.map_det]; exact hdetU) _
  have hTU : T.ideal ⟨X.basicOpen b.det, hUa⟩ = Ideal.span (Set.range fun i => ρ (a i)) := by
    rw [hspanU, ← T.map_ideal (U := ⟨X.basicOpen b.det, hUa⟩) (V := ⟨V, hV⟩) hUV, hTV,
      Ideal.map_span, ← Set.range_comp]
    rfl
  -- the chart data on the shrunken chart, and the two halves of the conclusion
  have hwrU : IsWeaklyRegular Γ(X, X.basicOpen b.det) (List.ofFn fun i => ρ (a i)) :=
    isWeaklyRegular_res_basicOpen hV b.det rfl hUV a hwr
  have hflatU : ((Ideal.Quotient.mk (Ideal.span (Set.range fun i => ρ (a i)))).comp
      (f.appLE W (X.basicOpen b.det) hUW).hom).Flat :=
    flat_quotient_res_basicOpen f hV hVW a b.det hflatq hUW
  have _ : IsAffine (X.basicOpen b.det).toScheme := hUa
  have hUtop : IsAffineOpen (⊤ : (X.basicOpen b.det).toScheme.Opens) := isAffineOpen_top _
  have hZtop : (T.comap (X.basicOpen b.det).ι).ideal ⟨⊤, hUtop⟩
      = Ideal.span (Set.range fun i => (X.basicOpen b.det).topIso.inv.hom (ρ (a i))) := by
    rw [Stacks.IdealSheaf.ideal_comap_ι_top T hUa hUtop, hTU, Ideal.map_span, ← Set.range_comp]
    rfl
  have hrel := isRelativeQuasiRegularImmersion_subschemeι_of_chart f hW hUa hUW hUtop
    (T.comap (X.basicOpen b.det).ι) (fun i => ρ (a i)) hZtop hwrU hflatU
  have _ : Flat ((X.basicOpen b.det).ι ≫ f) := inferInstance
  have _ : LocallyOfFinitePresentation ((X.basicOpen b.det).ι ≫ f) := inferInstance
  exact ⟨X.basicOpen b.det, hxU, hrel,
    isRegularImmersion_of_isRelativeQuasiRegularImmersion _ _ hrel⟩

end Stacks.AlgebraicGeometry

end
