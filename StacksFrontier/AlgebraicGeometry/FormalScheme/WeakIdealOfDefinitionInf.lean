module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionPoints

/-!
# The intersection of two weak ideals of definition

The intersection `ℐ ∩ 𝒥` of two ideal sheaves on a locally topologically ringed space is an ideal
sheaf, and it is a weak ideal of definition over a class of opens as soon as both are: an
intersection of two open ideals is open, and its elements are topologically nilpotent.

The substance of this file is that the intersection of two weak ideals of definition of a formal
scheme in the sense of McQuillan, both cut out by their sections over the weak affine formal opens
(`AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.IsCutOutOn`), is again cut out by
its sections. Over a weak affine formal open `𝔘 ≅ Spfw A`, with `𝔞` and `𝔟` the weak ideals of
definition of `A` corresponding to `ℐ(𝔘)` and `𝒥(𝔘)`, a point killing `ℐ(𝔘) ∩ 𝒥(𝔘)` factors
through the quotient point `Spec (A/(𝔞 ∩ 𝔟)) → 𝔘`, so it suffices that this quotient point kills a
section `s` of `ℐ ∩ 𝒥`. Its two closed subschemes `Spec (A/𝔞)` and `Spec (A/𝔟)` kill `s`, `ℐ` and
`𝒥` being cut out by their sections, and a section of the structure sheaf of `Spec R` vanishing
on two closed subschemes `Spec (R/𝔞')` and `Spec (R/𝔟')` with `𝔞' ∩ 𝔟' = 0` vanishes.

## Main definitions

* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.inf`: the intersection of two
  ideal sheaves.

## Main results

* `AlgebraicGeometry.eq_zero_of_app_eq_zero_of_isAffine` and
  `AlgebraicGeometry.eq_zero_of_spec_map_app_eq_zero`: a section of the structure sheaf of an
  affine scheme which vanishes along two morphisms from affine schemes whose maps on global
  sections have trivially intersecting kernels is zero.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.isWeakIdealOfDefinitionOn_inf`:
  the intersection of two weak ideals of definition is one.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.isCutOutOn_inf`: the intersection
  of two weak ideals of definition cut out by their sections over the weak affine formal opens is
  cut out by its sections.

## Implementation notes

The vanishing of a section of `𝒪_{Spec R}` along two closed subschemes with trivially intersecting
ideals is proved for arbitrary morphisms `f₁ : Y₁ → X`, `f₂ : Y₂ → X` of affine schemes such that
no nonzero global section of `X` is killed by both `f₁` and `f₂`. It is checked on the basic opens
`D(g) ⊆ W` of `X`: there the sections are the localisation `Γ(X, ⊤)_g`, the preimage of `D(g)` in
`Y_i` is the basic open of the image of `g`, and an element `x/gⁿ` killed in both localisations
`Γ(Y_i, ⊤)_g` has `g^N x` killed by both `f_i`, so `g^N x = 0`.

## References

* [Stacks Project, Tag 0AIV](https://stacks.math.columbia.edu/tag/0AIV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-! ### Sections vanishing along two morphisms of affine schemes -/

/-- A global section of an affine scheme `X` whose restriction to a basic open `D(g)` is killed by
a morphism `f : Y → X` out of an affine scheme becomes killed by `f` after multiplication by a
power of `g`: the sections of `Y` over the preimage of `D(g)` are the localisation of `Γ(Y, ⊤)` at
the image of `g`. -/
theorem exists_pow_mul_appTop_eq_zero {X Y : Scheme.{u}} [IsAffine Y] (f : Y ⟶ X) (g x : Γ(X, ⊤))
    (h : f.app (X.basicOpen g) (X.presheaf.map (homOfLE le_top : X.basicOpen g ⟶ ⊤).op x) = 0) :
    ∃ k : ℕ, f.appTop (g ^ k * x) = 0 := by
  have hnat : f.app (X.basicOpen g) (X.presheaf.map (homOfLE le_top : X.basicOpen g ⟶ ⊤).op x) =
      Y.presheaf.map (homOfLE le_top : f ⁻¹ᵁ X.basicOpen g ⟶ ⊤).op (f.appTop x) :=
    congrArg (fun φ => φ.hom x) (f.naturality (homOfLE le_top : X.basicOpen g ⟶ ⊤).op)
  let : Algebra Γ(Y, ⊤) Γ(Y, f ⁻¹ᵁ X.basicOpen g) :=
    (Y.presheaf.map (homOfLE le_top : f ⁻¹ᵁ X.basicOpen g ⟶ ⊤).op).hom.toAlgebra
  have : IsLocalization.Away (f.appTop g) Γ(Y, f ⁻¹ᵁ X.basicOpen g) :=
    (isAffineOpen_top Y).isLocalization_of_eq_basicOpen (f.appTop g) (homOfLE le_top)
      (Scheme.preimage_basicOpen_top f g)
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (f.appTop g))
    Γ(Y, f ⁻¹ᵁ X.basicOpen g) (f.appTop x)).mp (hnat.symm.trans h)
  exact ⟨k, by rw [map_mul, map_pow]; exact hk⟩

/-- **A section of an affine scheme vanishing along two morphisms with jointly injective maps on
global sections is zero.** Let `f₁ : Y₁ → X` and `f₂ : Y₂ → X` be morphisms of affine schemes such
that no nonzero global section of `X` is killed by both. Then a section of `𝒪_X` over any open `W`
killed by both `f₁` and `f₂` is zero. -/
theorem eq_zero_of_app_eq_zero_of_isAffine {X Y₁ Y₂ : Scheme.{u}} [IsAffine X] [IsAffine Y₁]
    [IsAffine Y₂] (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X)
    (h : ∀ x : Γ(X, ⊤), f₁.appTop x = 0 → f₂.appTop x = 0 → x = 0)
    {W : X.Opens} {σ : Γ(X, W)} (h₁ : f₁.app W σ = 0) (h₂ : f₂.app W σ = 0) : σ = 0 := by
  have hloc : ∀ g : Γ(X, ⊤), ∀ hg : X.basicOpen g ≤ W,
      X.presheaf.map (homOfLE hg).op σ = 0 := by
    intro g hg
    have hres : ∀ {Y : Scheme.{u}} (f : Y ⟶ X), f.app W σ = 0 →
        f.app (X.basicOpen g) (X.presheaf.map (homOfLE hg).op σ) = 0 := by
      intro Y f hf
      refine (congrArg (fun φ => φ.hom σ) (f.naturality (homOfLE hg).op)).trans ?_
      change Y.presheaf.map _ (f.app W σ) = 0
      rw [hf, map_zero]
    let : Algebra Γ(X, ⊤) Γ(X, X.basicOpen g) :=
      (X.presheaf.map (homOfLE le_top : X.basicOpen g ⟶ ⊤).op).hom.toAlgebra
    have : IsLocalization.Away g Γ(X, X.basicOpen g) :=
      (isAffineOpen_top X).isLocalization_of_eq_basicOpen g (homOfLE le_top) rfl
    obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, hx⟩ := IsLocalization.surj (Submonoid.powers g)
      (X.presheaf.map (homOfLE hg).op σ)
    have hx' : ∀ {Y : Scheme.{u}} (f : Y ⟶ X), f.app W σ = 0 →
        f.app (X.basicOpen g) (X.presheaf.map (homOfLE le_top : X.basicOpen g ⟶ ⊤).op x) = 0 := by
      intro Y f hf
      change f.app (X.basicOpen g) (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen g) x) = 0
      rw [← hx, map_mul, hres f hf, zero_mul]
    obtain ⟨k₁, hk₁⟩ := exists_pow_mul_appTop_eq_zero f₁ g x (hx' f₁ h₁)
    obtain ⟨k₂, hk₂⟩ := exists_pow_mul_appTop_eq_zero f₂ g x (hx' f₂ h₂)
    have hz : g ^ (k₁ + k₂) * x = 0 := by
      refine h _ ?_ ?_
      · rw [show g ^ (k₁ + k₂) * x = g ^ k₂ * (g ^ k₁ * x) by ring, map_mul, hk₁, mul_zero]
      · rw [show g ^ (k₁ + k₂) * x = g ^ k₁ * (g ^ k₂ * x) by ring, map_mul, hk₂, mul_zero]
    have h0 : algebraMap Γ(X, ⊤) Γ(X, X.basicOpen g) x = 0 :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ x).mpr
        ⟨⟨g ^ (k₁ + k₂), k₁ + k₂, rfl⟩, hz⟩
    exact (IsUnit.mul_left_eq_zero (IsLocalization.map_units Γ(X, X.basicOpen g)
      (⟨g ^ n, n, rfl⟩ : Submonoid.powers g))).mp (hx.trans h0)
  refine TopCat.Presheaf.section_ext X.sheaf W σ 0 fun p hp => ?_
  obtain ⟨g, hgW, hpg⟩ := (isAffineOpen_top X).exists_basicOpen_le ⟨p, hp⟩ trivial
  refine (X.presheaf.germ_res_apply (homOfLE hgW) p hpg σ).symm.trans ?_
  rw [hloc g hgW, map_zero, map_zero]
  rfl

/-- **A section of `Spec R` vanishing along two closed subschemes with trivially intersecting
ideals is zero**, in the generality of two ring homomorphisms `R → S₁`, `R → S₂` whose kernels
intersect trivially. -/
theorem eq_zero_of_spec_map_app_eq_zero {R S₁ S₂ : CommRingCat.{u}} (φ₁ : R ⟶ S₁) (φ₂ : R ⟶ S₂)
    (h : RingHom.ker φ₁.hom ⊓ RingHom.ker φ₂.hom = ⊥) {W : (Spec R).Opens} {σ : Γ(Spec R, W)}
    (h₁ : (Spec.map φ₁).app W σ = 0) (h₂ : (Spec.map φ₂).app W σ = 0) : σ = 0 := by
  refine eq_zero_of_app_eq_zero_of_isAffine _ _ (fun x hx₁ hx₂ => ?_) h₁ h₂
  have hker : ∀ {S : CommRingCat.{u}} (φ : R ⟶ S), (Spec.map φ).appTop x = 0 →
      (Scheme.ΓSpecIso R).hom x ∈ RingHom.ker φ.hom := by
    intro S φ hx
    have hnat := congrArg (fun ψ => ψ.hom x) (Scheme.ΓSpecIso_naturality φ)
    change (Scheme.ΓSpecIso S).hom ((Spec.map φ).appTop x) = φ ((Scheme.ΓSpecIso R).hom x)
      at hnat
    rw [hx, map_zero] at hnat
    exact RingHom.mem_ker.mpr hnat.symm
  have hmem : (Scheme.ΓSpecIso R).hom x ∈ RingHom.ker φ₁.hom ⊓ RingHom.ker φ₂.hom :=
    ⟨hker φ₁ hx₁, hker φ₂ hx₂⟩
  rw [h] at hmem
  exact (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.injective
    (((Submodule.mem_bot _).mp hmem).trans (map_zero _).symm)

namespace LocallyTopologicallyRingedSpace.IdealSheaf

variable {X : LTRS.{u}}

/-! ### The intersection of two ideal sheaves -/

/-- The intersection `ℐ ∩ 𝒥` of two ideal sheaves: its ideal of sections over an open is the
intersection of the ideals of sections of `ℐ` and of `𝒥`. -/
def inf (I J : IdealSheaf X) : IdealSheaf X where
  ideal V := I.ideal V ⊓ J.ideal V
  map_mem h _ hs := ⟨I.map_mem h hs.1, J.map_mem h hs.2⟩
  mem_of_locally_mem {U s} hloc := by
    refine ⟨I.mem_of_locally_mem fun x hx => ?_, J.mem_of_locally_mem fun x hx => ?_⟩
    · obtain ⟨V, hVU, hxV, hs⟩ := hloc x hx
      exact ⟨V, hVU, hxV, hs.1⟩
    · obtain ⟨V, hVU, hxV, hs⟩ := hloc x hx
      exact ⟨V, hVU, hxV, hs.2⟩

/-- The ideal of sections of `ℐ ∩ 𝒥` over an open `V` is `ℐ(V) ∩ 𝒥(V)`. -/
@[simp]
theorem inf_ideal (I J : IdealSheaf X) (V : Opens X) :
    (I.inf J).ideal V = I.ideal V ⊓ J.ideal V :=
  rfl

/-- A morphism killing `ℐ` kills `ℐ ∩ 𝒥`. -/
theorem kills_inf_of_kills_left {I : IdealSheaf X} (J : IdealSheaf X) {Y : LTRS.{u}} {f : Y ⟶ X}
    (h : I.Kills f) : (I.inf J).Kills f :=
  fun V _ hs => h V hs.1

/-- A morphism killing `𝒥` kills `ℐ ∩ 𝒥`. -/
theorem kills_inf_of_kills_right (I : IdealSheaf X) {J : IdealSheaf X} {Y : LTRS.{u}} {f : Y ⟶ X}
    (h : J.Kills f) : (I.inf J).Kills f :=
  fun V _ hs => h V hs.2

/-- **The intersection of two weak ideals of definition is a weak ideal of definition**: over every
open of the class, an intersection of two open ideals is open, and an element of it is
topologically nilpotent. -/
theorem isWeakIdealOfDefinitionOn_inf {I J : IdealSheaf X} {𝒜 : Opens X → Prop}
    (hI : I.IsWeakIdealOfDefinitionOn 𝒜) (hJ : J.IsWeakIdealOfDefinitionOn 𝒜) :
    (I.inf J).IsWeakIdealOfDefinitionOn 𝒜 :=
  fun U hU => ⟨(hI U hU).1.inter (hJ U hU).1, fun x hx => (hI U hU).2 x hx.1⟩

/-- **The intersection of two weak ideals of definition cut out by their sections over the weak
affine formal opens is cut out by its sections.** A section of `ℐ ∩ 𝒥` over `V ≤ U`, `U` a weak
affine formal open with chart `Spfw A`, is killed by the quotient points of `A` at the weak ideals
of definition `𝔞` and `𝔟` corresponding to `ℐ(U)` and `𝒥(U)`, hence by the quotient point at
`𝔞 ∩ 𝔟`, through which every point killing `(ℐ ∩ 𝒥)(U)` factors. Conversely a section killed by
every point killing `(ℐ ∩ 𝒥)(U)` is killed by every point killing `ℐ(U)`, and by every point
killing `𝒥(U)`. -/
theorem isCutOutOn_inf {I J : IdealSheaf X}
    (hI : I.IsWeakIdealOfDefinitionOn (IsWeakAffineFormalOpen X))
    (hJ : J.IsWeakIdealOfDefinitionOn (IsWeakAffineFormalOpen X))
    (hCI : I.IsCutOutOn (IsWeakAffineFormalOpen X))
    (hCJ : J.IsCutOutOn (IsWeakAffineFormalOpen X)) :
    (I.inf J).IsCutOutOn (IsWeakAffineFormalOpen X) := by
  intro U hU V hVU s
  refine ⟨fun hs T f hf hkill => ?_, fun hs =>
    ⟨(hCI U hU V hVU s).mpr fun T f hf hkill => hs T f hf fun t ht => hkill t ht.1,
      (hCJ U hU V hVU s).mpr fun T f hf hkill => hs T f hf fun t ht => hkill t ht.2⟩⟩
  set L : WeakIdealsOfDefinition hU.chart.ring.α :=
    spfIndexMeet _ (I.chartIdeal hI hU) (J.chartIdeal hJ hU)
  have hLa : L.1 ≤ (I.chartIdeal hI hU).1 := inf_le_left
  have hLb : L.1 ≤ (J.chartIdeal hJ hU).1 := inf_le_right
  set qL := weakChartPoint _ hU.chart.admissible hU.chart.iso L
  obtain ⟨g, hg, -⟩ := existsUnique_weakChartPoint_factor _ hU.chart.admissible hU.chart.iso L f
    hf fun x hx => hkill _ ⟨hx.1, hx.2⟩
  suffices hq : (qL.toHom.c.app (op V)).1 s = 0 by
    subst hg
    exact mem_ker_iff.mp (ker_le_ker_comp (schemeToLTRS.map g) qL V (mem_ker_iff.mpr hq))
  have key : ∀ (K : IdealSheaf X) (hK : K.IsWeakIdealOfDefinitionOn (IsWeakAffineFormalOpen X))
      (hCK : K.IsCutOutOn (IsWeakAffineFormalOpen X)) (hsK : s ∈ K.ideal V)
      (hL : L.1 ≤ (K.chartIdeal hK hU).1),
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hL))).app
        ((Opens.map qL.toHom.base).obj V) ((qL.toHom.c.app (op V)).1 s) = 0 := by
    intro K hK hCK hsK hL
    have hq : ((weakChartPoint _ hU.chart.admissible hU.chart.iso
        (K.chartIdeal hK hU)).toHom.c.app (op V)).1 s = 0 :=
      (hCK U hU V hVU s).mp hsK _ _ (K.range_chartPoint_subset hK hU)
        fun _ ht => K.chartPoint_c_app_eq_zero hK hU ht
    rwa [← schemeToLTRS_map_comp_weakChartPoint _ hU.chart.admissible hU.chart.iso hL] at hq
  have mem : ∀ {a : Ideal hU.chart.ring.α} (hL : L.1 ≤ a) (w : hU.chart.ring.α),
      Ideal.Quotient.factor hL (Ideal.Quotient.mk L.1 w) = 0 → w ∈ a := fun hL w hw =>
    Ideal.Quotient.eq_zero_iff_mem.mp ((Ideal.Quotient.factor_mk hL w).symm.trans hw)
  refine eq_zero_of_spec_map_app_eq_zero _ _ (eq_bot_iff.mpr fun z hz => ?_)
      (key I hI hCI hs.1 hLa) (key J hJ hCJ hs.2 hLb)
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact (Submodule.mem_bot _).mpr
    (Ideal.Quotient.eq_zero_iff_mem.mpr ⟨mem hLa w hz.1, mem hLb w hz.2⟩)

end LocallyTopologicallyRingedSpace.IdealSheaf

end AlgebraicGeometry

end
