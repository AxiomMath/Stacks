module

public import StacksFrontier.AlgebraicGeometry.Quot.EtaleLocallyProjectiveCurvesFibreEquation
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.CartierAffineLocalConverse.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.Chart

/-!
# A divisor on an étale chart from an equation on its fibre

Let `g : X ⟶ S` be locally of finite type with `X` affine, `w ∈ X`, and suppose the fibre
`X_s` over `s = g(w)` has, on an affine open `N` through the point `y` of the fibre over `w`, a
nonzerodivisor `b` of `Γ(X_s, N)` vanishing at `y` whose zero locus in `N` is `{y}` near `y`.
Then a global function `c` of `X` whose germ at `w` maps to the germ of `b` up to a unit cuts out
a closed subscheme `Z = V(c)` of `X` through `w`, principal, whose fibre over `s` is an effective
Cartier divisor near `y` (it is cut out there by `b` times a unit), and which is quasi-finite over
`S` at its point over `w` (that point is isolated in its fibre).

These are the hypotheses on the chart divisor of
`AlgebraicGeometry.Space.exists_etale_isEffectiveCartierDivisor_range_of_chart`, the step of the
proof that families of curves are étale locally schemes (Stacks 0E6F) which moves a local divisor
from an étale chart to the family.

## Main results

* `AlgebraicGeometry.exists_idealSheafData_quasiFiniteAt_of_fibre_equation`.

## References

* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- An element whose image under an injective ring homomorphism is regular is regular. -/
theorem isRegular_of_isRegular_map {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R')
    (hφ : Function.Injective φ) {a : R} (ha : IsRegular (φ a)) : IsRegular a := by
  refine (Commute.isRegular_iff (Commute.all _)).2 fun b c hbc => hφ ?_
  exact ha.1 (by simpa only [map_mul] using congrArg φ hbc)

open Stacks.Divisors in
/-- **A divisor on an affine chart from an isolated equation on its fibre.** Let `g : X ⟶ S` be
locally of finite type with `X` affine, `w ∈ X`, `y` the point of the fibre `X_s` over `w`
(`s = g(w)`), `N ∋ y` an affine open of `X_s` and `b` a nonzerodivisor of `Γ(X_s, N)` vanishing at
`y` whose zero locus in `N` is `{y}` near `y`. Then there is a closed subscheme `Z` of `X` through
`w`, principal near `w`, whose fibre over `s` is an effective Cartier divisor near `y`, and which
is quasi-finite over `S` at a point over `w`. -/
theorem exists_idealSheafData_quasiFiniteAt_of_fibre_equation {X S : Scheme.{u}} [IsAffine X]
    (g : X ⟶ S) [LocallyOfFiniteType g] (w : X) {N : (g.fiber (g w)).Opens} (hN : IsAffineOpen N)
    (b : Γ(g.fiber (g w), N)) (hyN : g.asFiber w ∈ N) (hb : IsRegular b)
    (hyb : g.asFiber w ∉ (g.fiber (g w)).basicOpen b) (O : (g.fiber (g w)).Opens)
    (hyO : g.asFiber w ∈ O)
    (hiso : ∀ y' ∈ O, y' ∈ N → y' ∉ (g.fiber (g w)).basicOpen b → y' = g.asFiber w) :
    ∃ Z : X.IdealSheafData, w ∈ Z.support ∧
      (∃ V : X.affineOpens, w ∈ (V : X.Opens) ∧ (Z.ideal V).IsPrincipal) ∧
      (∃ V : (g.fiber (g w)).Opens, g.asFiber w ∈ V ∧
        IsEffectiveCartierDivisor ((Z.comap (g.fiberι (g w))).comap V.ι)) ∧
      ∃ z : Z.subscheme, Z.subschemeι z = w ∧ (Z.subschemeι ≫ g).QuasiFiniteAt z := by
  classical
  set ι : g.fiber (g w) ⟶ X := g.fiberι (g w) with hιdef
  set y : g.fiber (g w) := g.asFiber w
  have hιy : ι y = w := g.fiberι_asFiber w
  have hιyT : ι y ∈ (⊤ : X.Opens) := trivial
  -- the germ of `b` lifts, up to a unit, to a global function `c` of `X`
  obtain ⟨γ, hγ⟩ := ι.stalkMap_surjective y (((g.fiber (g w)).presheaf.germ N y hyN).hom b)
  let _ : Algebra Γ(X, ⊤) (X.presheaf.stalk (ι y)) :=
    X.presheaf.algebra_section_stalk (⟨ι y, hιyT⟩ : (⊤ : X.Opens))
  set q : Ideal Γ(X, ⊤) := ((isAffineOpen_top X).primeIdealOf ⟨ι y, hιyT⟩).asIdeal
  have _ : q.IsPrime := ((isAffineOpen_top X).primeIdealOf ⟨ι y, hιyT⟩).isPrime
  have _ : IsLocalization.AtPrime (X.presheaf.stalk (ι y)) q :=
    (isAffineOpen_top X).isLocalization_stalk ⟨ι y, hιyT⟩
  obtain ⟨⟨c, ⟨s, hsq⟩⟩, hcs⟩ := IsLocalization.mk'_surjective q.primeCompl γ
  have hcγ : algebraMap Γ(X, ⊤) (X.presheaf.stalk (ι y)) c =
      γ * algebraMap Γ(X, ⊤) (X.presheaf.stalk (ι y)) s := by
    rw [← hcs, IsLocalization.mk'_spec]
  have hsunit : IsUnit (algebraMap Γ(X, ⊤) (X.presheaf.stalk (ι y)) s) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk (ι y)) q s).mpr hsq
  have hNT : N ≤ ι ⁻¹ᵁ (⊤ : X.Opens) := le_top
  have hgerm : ∀ t : Γ(X, ⊤), (ι.stalkMap y).hom (algebraMap Γ(X, ⊤) (X.presheaf.stalk (ι y)) t)
      = ((g.fiber (g w)).presheaf.germ N y hyN).hom ((ι.appLE ⊤ N hNT).hom t) := fun t =>
    RingHom.congr_fun (Stacks.AlgebraicGeometry.stalkMap_hom_comp_germ ι hNT hyN hιyT) t
  set cb : Γ(g.fiber (g w), N) := (ι.appLE ⊤ N hNT).hom c
  set sb : Γ(g.fiber (g w), N) := (ι.appLE ⊤ N hNT).hom s
  have hcbgerm : ((g.fiber (g w)).presheaf.germ N y hyN).hom cb =
      ((g.fiber (g w)).presheaf.germ N y hyN).hom (b * sb) := by
    rw [map_mul, ← hgerm, ← hgerm, hcγ, map_mul, hγ]
  have hysb : y ∈ (g.fiber (g w)).basicOpen sb := by
    rw [(g.fiber (g w)).mem_basicOpen sb y hyN, ← hgerm]; exact hsunit.map _
  -- on a basic open `N'` of `N` through `y`, `cb = b * sb` with `sb` a unit
  obtain ⟨W, hyW, iU, iV, hWeq⟩ :=
    TopCat.Presheaf.germ_eq (g.fiber (g w)).presheaf y hyN hyN cb (b * sb) hcbgerm
  obtain ⟨h', hh'le, hyh'⟩ := hN.exists_basicOpen_le
    (⟨y, ⟨hyW, hysb⟩⟩ : (W ⊓ (g.fiber (g w)).basicOpen sb : (g.fiber (g w)).Opens)) hyN
  set N' : (g.fiber (g w)).Opens := (g.fiber (g w)).basicOpen h'
  have hN' : IsAffineOpen N' := hN.basicOpen h'
  have hN'N : N' ≤ N := (g.fiber (g w)).basicOpen_le h'
  have hN'W : N' ≤ W := hh'le.trans inf_le_left
  have hN'sb : N' ≤ (g.fiber (g w)).basicOpen sb := hh'le.trans inf_le_right
  let res : Γ(g.fiber (g w), N) →+* Γ(g.fiber (g w), N') :=
    ((g.fiber (g w)).presheaf.map (homOfLE hN'N).op).hom
  have key5 : ∀ {U₁ U₂ U₃ : (g.fiber (g w)).Opens} (i : U₁ ⟶ U₂) (j : U₂ ⟶ U₃) (k : U₁ ⟶ U₃)
      (t : Γ(g.fiber (g w), U₃)), ((g.fiber (g w)).presheaf.map i.op).hom
        (((g.fiber (g w)).presheaf.map j.op).hom t) =
          ((g.fiber (g w)).presheaf.map k.op).hom t := by
    intro U₁ U₂ U₃ i j k t
    rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, Subsingleton.elim (i ≫ j) k]
  have hrescb : res cb = res b * res sb := by
    have h1 := congrArg ((g.fiber (g w)).presheaf.map (homOfLE hN'W).op).hom hWeq
    rwa [key5 _ _ (homOfLE hN'N), map_mul ((g.fiber (g w)).presheaf.map iV.op).hom, map_mul,
      key5 _ _ (homOfLE hN'N), key5 _ _ (homOfLE hN'N)] at h1
  have hressb : IsUnit (res sb) := by
    have h1 := (g.fiber (g w)).toRingedSpace.isUnit_res_basicOpen sb
    have h2 := h1.map ((g.fiber (g w)).presheaf.map (homOfLE hN'sb).op).hom
    convert h2 using 1
    exact (key5 _ _ (homOfLE hN'N) sb).symm
  have hresb : IsRegular (res b) := by
    let : Algebra Γ(g.fiber (g w), N) Γ(g.fiber (g w), N') := res.toAlgebra
    have : IsLocalization.Away h' Γ(g.fiber (g w), N') := hN.isLocalization_basicOpen h'
    have : Module.Flat Γ(g.fiber (g w), N) Γ(g.fiber (g w), N') :=
      IsLocalization.flat _ (Submonoid.powers h')
    exact Stacks.Fitting.isRegular_algebraMap_of_flat hb
  have hrescbreg : IsRegular (res cb) := by
    rw [hrescb]; exact hresb.mul hressb.isRegular
  -- vanishing of `cb` and of `b` agree on `N'`
  have hvan : ∀ y' ∈ N', y' ∈ (g.fiber (g w)).basicOpen cb ↔ y' ∈ (g.fiber (g w)).basicOpen b := by
    intro y' hy'
    have e1 : (g.fiber (g w)).basicOpen (res cb) = N' ⊓ (g.fiber (g w)).basicOpen cb :=
      (g.fiber (g w)).basicOpen_res _ _
    have e2 : (g.fiber (g w)).basicOpen (res b) = N' ⊓ (g.fiber (g w)).basicOpen b :=
      (g.fiber (g w)).basicOpen_res _ _
    have e3 : (g.fiber (g w)).basicOpen (res sb) = N' := by
      simpa using (g.fiber (g w)).basicOpen_of_isUnit hressb
    have e4 : (g.fiber (g w)).basicOpen (res cb) = (g.fiber (g w)).basicOpen (res b) := by
      rw [hrescb, (g.fiber (g w)).basicOpen_mul, e3]
      exact inf_of_le_left ((g.fiber (g w)).basicOpen_le _)
    constructor
    · intro h
      have : y' ∈ (g.fiber (g w)).basicOpen (res cb) := by rw [e1]; exact ⟨hy', h⟩
      rw [e4, e2] at this; exact this.2
    · intro h
      have : y' ∈ (g.fiber (g w)).basicOpen (res b) := by rw [e2]; exact ⟨hy', h⟩
      rw [← e4, e1] at this; exact this.2
  have hbasiccb : (g.fiber (g w)).basicOpen cb = N ⊓ ι ⁻¹ᵁ X.basicOpen c :=
    Scheme.basicOpen_appLE ι N ⊤ hNT c
  have hyN' : y ∈ N' := hyh'
  have hwc : w ∉ X.basicOpen c := by
    intro hw
    have : y ∈ (g.fiber (g w)).basicOpen cb := by
      rw [hbasiccb]; exact ⟨hyN, by rwa [← hιy] at hw⟩
    exact hyb ((hvan y hyN').1 this)
  -- the closed subscheme
  let Z : X.IdealSheafData := Scheme.IdealSheafData.ofIdealTop (Ideal.span {c})
  have hsuppZ : (Z.support : Set X) = (X.basicOpen c : Set X)ᶜ := by
    ext x
    change x ∈ Z.support ↔ _
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨⊤, isAffineOpen_top X⟩) trivial,
      Stacks.Divisors.ideal_ofIdealTop_top, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton]
  have hwZ : w ∈ Z.support := by
    change w ∈ (Z.support : Set X); rw [hsuppZ]; exact hwc
  obtain ⟨z, hz⟩ : w ∈ Set.range Z.subschemeι := by
    rwa [Scheme.IdealSheafData.range_subschemeι]
  refine ⟨Z, hwZ, ⟨⟨⊤, isAffineOpen_top X⟩, trivial, ?_⟩, ⟨N', hyN', ?_⟩, z, hz, ?_⟩
  · rw [Stacks.Divisors.ideal_ofIdealTop_top]; exact ⟨c, rfl⟩
  · -- the fibre of `Z` on `N'` is cut out by `cb` restricted, a nonzerodivisor
    have hN'aff : IsAffine N'.toScheme := hN'
    rw [← Scheme.IdealSheafData.comap_comp]
    refine (Stacks.CartierAffineLocalConverse.isEffectiveCartierDivisor_iff_isRegular _).2
      fun x _ => ⟨⟨⊤, isAffineOpen_top _⟩, trivial, _, ?_,
        Stacks.Divisors.ideal_comap_ofIdealTop_span (N'.ι ≫ ι) c ⊤ (isAffineOpen_top _)⟩
    have hk : N'.ι ''ᵁ (⊤ : N'.toScheme.Opens) ≤ ι ⁻¹ᵁ ⊤ := fun _ _ => trivial
    change IsRegular (((g.fiber (g w)).presheaf.map
      (homOfLE (le_refl (N'.ι ''ᵁ (⊤ : N'.toScheme.Opens)))).op).hom
        (((g.fiber (g w)).presheaf.map (homOfLE hk).op).hom ((ι.app ⊤).hom c)))
    rw [key5 _ _ (homOfLE hk)]
    have hk' : N' ≤ ι ⁻¹ᵁ ⊤ := fun _ _ => trivial
    have hreg :
        IsRegular (((g.fiber (g w)).presheaf.map (homOfLE hk').op).hom ((ι.app ⊤).hom c)) := by
      convert hrescbreg using 1
      change _ = ((g.fiber (g w)).presheaf.map (homOfLE hN'N).op).hom
        (((g.fiber (g w)).presheaf.map (homOfLE hNT).op).hom ((ι.app ⊤).hom c))
      exact (key5 _ _ _ _).symm
    have hNN : N'.ι ''ᵁ (⊤ : N'.toScheme.Opens) = N' := N'.ι_image_top
    refine isRegular_of_isRegular_map ((g.fiber (g w)).presheaf.map (eqToHom hNN.symm).op).hom
      (ConcreteCategory.bijective_of_isIso _).1 ?_
    rwa [key5]
  · -- the point over `w` is isolated in its fibre
    have : LocallyOfFiniteType (Z.subschemeι ≫ g) := inferInstance
    rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
    set G := (Z.subschemeι ≫ g).fiber ((Z.subschemeι ≫ g) z)
    set ιG := (Z.subschemeι ≫ g).fiberι ((Z.subschemeι ≫ g) z)
    obtain ⟨U₀, hU₀, hU₀eq⟩ := (isOpen_induced_iff.1 (by
      rw [← ι.isEmbedding.isInducing.eq_induced]
      exact (O ⊓ N').isOpen) :
        ∃ t, IsOpen t ∧ ι ⁻¹' t = ((O ⊓ N' : (g.fiber (g w)).Opens) : Set (g.fiber (g w))))
    have hE : {(Z.subschemeι ≫ g).asFiber z} = ιG ⁻¹' (Z.subschemeι ⁻¹' U₀) := by
      ext e
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl
        rw [Scheme.Hom.fiberι_asFiber, hz]
        have : y ∈ ι ⁻¹' U₀ := by rw [hU₀eq]; exact ⟨hyO, hyN'⟩
        rwa [Set.mem_preimage, hιy] at this
      · intro he
        set z' := ιG e
        have hz's : (Z.subschemeι ≫ g) z' = (Z.subschemeι ≫ g) z := by
          have := Set.mem_range_self (f := ιG) e
          rwa [Scheme.Hom.range_fiberι] at this
        have hw'Z : Z.subschemeι z' ∈ (Z.support : Set X) := by
          rw [← Scheme.IdealSheafData.range_subschemeι]; exact Set.mem_range_self _
        have hw's : g (Z.subschemeι z') = g w := by
          rwa [← hz]
        obtain ⟨y', hy'⟩ : Z.subschemeι z' ∈ Set.range ι := by
          rwa [hιdef, Scheme.Hom.range_fiberι]
        have hy'U : y' ∈ ι ⁻¹' U₀ := by rwa [Set.mem_preimage, hy']
        rw [hU₀eq] at hy'U
        obtain ⟨hy'O, hy'N'⟩ := hy'U
        have hy'c : y' ∉ (g.fiber (g w)).basicOpen cb := by
          rw [hbasiccb]; rintro ⟨-, h⟩
          have : Z.subschemeι z' ∈ (Z.support : Set X) := hw'Z
          rw [hsuppZ] at this
          exact this (by rw [← hy']; exact h)
        have hy'b : y' ∉ (g.fiber (g w)).basicOpen b := fun h => hy'c ((hvan y' hy'N').2 h)
        have hy'y : y' = y := hiso y' hy'O (hN'N hy'N') hy'b
        have hzz : z' = z := by
          apply Z.subschemeι.isEmbedding.injective
          rw [hz, ← hy', hy'y, hιy]
        apply ιG.isEmbedding.injective
        rwa [Scheme.Hom.fiberι_asFiber]
    rw [hE]
    exact (hU₀.preimage Z.subschemeι.continuous).preimage ιG.continuous

end AlgebraicGeometry
