module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleExtension
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.FiniteTypeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FittingIdealEtale
public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul

/-!
# Descending a family of étale-local centres to one centre on the base

Let `S` be a quasi-compact and quasi-separated scheme, let `U ⊆ S` be a quasi-compact open and
let `e_i : S_i ⟶ S` be finitely many quasi-compact étale morphisms. Given on each `S_i` a
quasi-coherent centre `J_i` which is finitely presented as a closed subscheme and supported away
from `e_i^{-1}(U)`, there is a single such centre `I` on `S` whose inverse image on each `S_i` is
*locally divisible* by `J_i`: every point of `S_i` has a neighbourhood `W` on which
`I·𝒪_W = J_i·𝒪_W · K` for some quasi-coherent `K` on `W`.

This is the content of steps 3 and 4 of the proof of [Stacks, Tag 0814] that concerns ideals
only. The local input is [Stacks, Tag 0813], which for an étale ring map `A → B`, an element
`a ∈ A` and a finitely generated `J ⊆ B` with `a ∈ √J` produces a finitely generated `I ⊆ A`
with `a ∈ √I` and `I·B_g = J·B_g · J'` near any given prime of `B`.

## Main definitions

* `Stacks.EtaleCentre.IdealSheafLocallyDvd`: the local divisibility relation above.

## Main results

* `Stacks.EtaleCentre.exists_affine_etale_locallyDvd_center`: the affine case, from
  [Stacks, Tag 0813].
* `Stacks.EtaleCentre.exists_etale_family_locallyDvd_center_of_isAffine_base`: an affine base and
  a finite family of quasi-compact étale coverings of it.
* `Stacks.EtaleCentre.exists_global_center_locallyDvd`: the global statement, the centre of
  step 4 of the proof of [Stacks, Tag 0814].

## Implementation notes

The source of [Stacks, Tag 0814] reduces first, by the observations of [Stacks, Tag 080Y], to an
affine base carrying an effective Cartier divisor cut out by a nonzerodivisor, so as to have an
element `a` with `S ∖ U = V(a)` for [Stacks, Tag 0813]. That reduction is **not used here**: the
library's form of [Stacks, Tag 0813], `exists_ideal_map_eq_mul_after_localization`, carries no
nonzerodivisor hypothesis, and the radical membership it wants is available directly from
disjointness of a basic open from the support of the centre
(`Stacks.EtaleCentre.mem_radical_of_disjoint_basicOpen_support`). So the argument runs over a
cover of `U` by basic opens of affine opens of `S`, with no divisor in sight, and the centres
produced for the individual basic opens are combined by `⊔`.

Local divisibility, rather than divisibility, is what the local construction delivers and what
the blowup argument consumes: [Stacks, Tag 080A] is applied after restricting to a neighbourhood
of the point being tested. It is stable under multiplying the divisible side by anything
(`Stacks.EtaleCentre.idealSheafLocallyDvd_mul_right`), which is what makes the products over a
finite cover work.

The passage from a local centre on an affine open of `S` to a centre on all of `S` is
`Stacks.Blowup.exists_idealSheafData_comap_eq`, the ideal half of [Stacks, Tag 080M].

## References

* [Stacks Project, Tag 0813](https://stacks.math.columbia.edu/tag/0813)
* [Stacks Project, Tag 0814](https://stacks.math.columbia.edu/tag/0814)
* [Stacks Project, Tag 080M](https://stacks.math.columbia.edu/tag/080M)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.EtaleCentre

/-! ### Finite presentation of the centres that occur -/

/-- A finitely generated ideal of the global sections of an affine scheme cuts out a closed
subscheme of finite presentation. -/
theorem finitePresentation_ofIdealTop_of_fg {X : Scheme.{u}} [IsAffine X] (I : Ideal Γ(X, ⊤))
    (hI : I.FG) : FinitePresentation (Scheme.IdealSheafData.ofIdealTop I).subschemeι := by
  refine (Stacks.Flatness.finitePresentation_subschemeι_iff _).mpr fun U ↦ ?_
  rw [Scheme.IdealSheafData.ofIdealTop_ideal]
  exact hI.map _

/-- A supremum of two centres of finite presentation is of finite presentation. -/
theorem finitePresentation_sup_subschemeι {X : Scheme.{u}} (I J : X.IdealSheafData)
    (hI : FinitePresentation I.subschemeι) (hJ : FinitePresentation J.subschemeι) :
    FinitePresentation (I ⊔ J).subschemeι := by
  refine (Stacks.Flatness.finitePresentation_subschemeι_iff _).mpr fun V ↦ ?_
  exact Submodule.FG.sup ((Stacks.Flatness.finitePresentation_subschemeι_iff I).mp hI V)
    ((Stacks.Flatness.finitePresentation_subschemeι_iff J).mp hJ V)

/-- A finite product of centres of finite presentation is of finite presentation. -/
theorem finitePresentation_prod_subschemeι {X : Scheme.{u}} {ι : Type*} (s : Finset ι)
    (I : ι → X.IdealSheafData) (hI : ∀ i, FinitePresentation (I i).subschemeι) :
    FinitePresentation (s.prod I).subschemeι :=
  (finitePresentation_subschemeι_iff_isFiniteType _).mpr
    (Stacks.Blowup.isFiniteType_prod s I fun i ↦
      (finitePresentation_subschemeι_iff_isFiniteType (I i)).mp (hI i))

/-! ### Radical membership and basic opens -/

/-- If `a` lies in the radical of `I`, the basic open of `a` misses the closed subscheme cut out
by `I`. -/
theorem disjoint_basicOpen_support_of_mem_radical {X : Scheme.{u}} (a : Γ(X, ⊤))
    (I : Ideal Γ(X, ⊤)) (ha : a ∈ I.radical) :
    Disjoint (X.basicOpen a : Set X)
      ((Scheme.IdealSheafData.ofIdealTop I).support : Set X) := by
  rw [Scheme.IdealSheafData.coe_support_ofIdealTop]
  refine Set.disjoint_left.mpr fun x hx hz ↦ ?_
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp ha
  have hnot := (Scheme.mem_zeroLocus_iff X (U := ⊤) (I : Set Γ(X, ⊤)) x).mp hz (a ^ n) hn
  have hunit := (X.mem_basicOpen_top a x).mp hx
  refine hnot ((X.mem_basicOpen_top (a ^ n) x).mpr ?_)
  show IsUnit ((X.presheaf.germ ⊤ x (by trivial)).hom (a ^ n))
  simpa only [map_pow] using hunit.pow n

/-- Conversely, on an affine scheme, if the basic open of `a` misses the closed subscheme cut out
by a quasi-coherent centre, then `a` lies in the radical of that centre's global ideal. -/
theorem mem_radical_of_disjoint_basicOpen_support {X : Scheme.{u}} [IsAffine X] (a : Γ(X, ⊤))
    (I : X.IdealSheafData) (ha : Disjoint (X.basicOpen a : Set X) (I.support : Set X)) :
    a ∈ (I.ideal ⟨⊤, isAffineOpen_top X⟩).radical := by
  have hle : I.support ≤ (Scheme.IdealSheafData.ofIdealTop (Ideal.span {a})).support := by
    intro x hx
    show x ∈ ((Scheme.IdealSheafData.ofIdealTop (Ideal.span {a})).support : Set X)
    rw [Scheme.IdealSheafData.coe_support_ofIdealTop, Scheme.zeroLocus_span]
    refine (Scheme.mem_zeroLocus_iff X _ x).mpr fun b hb ↦ ?_
    rcases hb with rfl
    exact fun h ↦ Set.disjoint_left.mp ha h hx
  rw [Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal,
    Scheme.IdealSheafData.vanishingIdeal_support] at hle
  have htop := hle ⟨⊤, isAffineOpen_top X⟩
  simpa using htop (by simp)

/-! ### Inverse images of centres given by a global ideal -/

/-- The inverse image along a morphism of affine schemes of the centre cut out by a global ideal
is cut out by the extension of that ideal. -/
theorem idealSheaf_comap_ofIdealTop {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (I : Ideal Γ(Y, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop I).comap f =
      Scheme.IdealSheafData.ofIdealTop (I.map f.appTop.hom) := by
  refine Scheme.IdealSheafData.ext_of_isAffine ?_
  rw [Stacks.IdealSheaf.ideal_comap_top_of_isAffine]
  simp

/-- On a basic open of an affine scheme, a factorization of extended ideals coming from
[Stacks, Tag 0813] becomes a factorization of the inverse images of the corresponding centres. -/
theorem idealSheaf_factorization_on_basicOpen {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (I : Ideal Γ(Y, ⊤)) (J : Ideal Γ(X, ⊤)) (g : Γ(X, ⊤))
    (K : Ideal (Localization.Away g)) (hK : K.FG)
    (h : I.map ((algebraMap Γ(X, ⊤) (Localization.Away g)).comp f.appTop.hom) =
      J.map (algebraMap Γ(X, ⊤) (Localization.Away g)) * K) :
    ∃ K' : Ideal Γ(X.basicOpen g, ⊤), K'.FG ∧
      (Scheme.IdealSheafData.ofIdealTop I).comap ((X.basicOpen g).ι ≫ f) =
        (Scheme.IdealSheafData.ofIdealTop J).comap (X.basicOpen g).ι *
          Scheme.IdealSheafData.ofIdealTop K' := by
  let W := X.basicOpen g
  let ε := IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) Γ(W, ⊤)
  refine ⟨K.map ε.toRingHom, hK.map _, ?_⟩
  rw [idealSheaf_comap_ofIdealTop, idealSheaf_comap_ofIdealTop]
  show (Scheme.IdealSheafData.equivOfIsAffine (X := W)).symm _ =
    (Scheme.IdealSheafData.equivOfIsAffine (X := W)).symm _ *
      (Scheme.IdealSheafData.equivOfIsAffine (X := W)).symm _
  rw [← map_mul]
  congr 1
  have hε : ε.toRingHom.comp (algebraMap Γ(X, ⊤) (Localization.Away g)) = W.ι.appTop.hom := by
    ext b
    exact ε.commutes b
  have hh := congrArg (Ideal.map ε.toRingHom) h
  simp only [Ideal.map_mul, Ideal.map_map] at hh
  rw [← RingHom.comp_assoc, hε] at hh
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using hh

/-! ### Local divisibility of centres -/

/-- `I` is **locally divisible** by `J` when every point has a neighbourhood `V` on which the
inverse image of `J` is the inverse image of `I` times some quasi-coherent centre on `V`. This is
the relation that [Stacks, Tag 080A] consumes: after restricting to such a `V` the blowup in `J`
factors through the blowup in `I`. -/
def IdealSheafLocallyDvd {X : Scheme.{u}} (I J : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ K : V.toScheme.IdealSheafData,
    J.comap V.ι = I.comap V.ι * K

/-- Divisibility implies local divisibility. -/
theorem idealSheafLocallyDvd_of_dvd {X : Scheme.{u}} (I J : X.IdealSheafData) (h : I ∣ J) :
    IdealSheafLocallyDvd I J := by
  obtain ⟨K, rfl⟩ := h
  exact fun x ↦ ⟨⊤, trivial, K.comap (⊤ : X.Opens).ι,
    Stacks.IdealSheaf.comap_mul _ _ _⟩

/-- Local divisibility by a fixed centre is stable under suprema. -/
theorem idealSheafLocallyDvd_sup {X : Scheme.{u}} {I J K : X.IdealSheafData}
    (hJ : IdealSheafLocallyDvd I J) (hK : IdealSheafLocallyDvd I K) :
    IdealSheafLocallyDvd I (J ⊔ K) := by
  intro x
  obtain ⟨V, hxV, A, hA⟩ := hJ x
  obtain ⟨W, hxW, B, hB⟩ := hK x
  refine ⟨V ⊓ W, ⟨hxV, hxW⟩,
    A.comap (X.homOfLE (inf_le_left : V ⊓ W ≤ V)) ⊔
      B.comap (X.homOfLE (inf_le_right : V ⊓ W ≤ W)), ?_⟩
  have hA' := congrArg
    (fun L ↦ Scheme.IdealSheafData.comap L (X.homOfLE (inf_le_left : V ⊓ W ≤ V))) hA
  have hB' := congrArg
    (fun L ↦ Scheme.IdealSheafData.comap L (X.homOfLE (inf_le_right : V ⊓ W ≤ W))) hB
  simp only [Stacks.IdealSheaf.comap_mul,
    ← Scheme.IdealSheafData.comap_comp] at hA' hB'
  rw [show X.homOfLE (inf_le_left : V ⊓ W ≤ V) ≫ V.ι = (V ⊓ W).ι from by simp] at hA'
  rw [show X.homOfLE (inf_le_right : V ⊓ W ≤ W) ≫ W.ι = (V ⊓ W).ι from by simp] at hB'
  rw [Scheme.IdealSheafData.comap_sup, hA', hB']
  exact (mul_add _ _ _).symm

/-- Local divisibility by a fixed centre is stable under multiplying by a further centre. -/
theorem idealSheafLocallyDvd_mul_right {X : Scheme.{u}} {I J : X.IdealSheafData}
    (h : IdealSheafLocallyDvd I J) (K : X.IdealSheafData) :
    IdealSheafLocallyDvd I (J * K) := by
  intro x
  obtain ⟨V, hx, L, hL⟩ := h x
  refine ⟨V, hx, L * K.comap V.ι, ?_⟩
  rw [Stacks.IdealSheaf.comap_mul, hL, mul_assoc]

/-- Local divisibility can be checked on an open cover. -/
theorem idealSheafLocallyDvd_of_openImmersion_at {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (I J : X.IdealSheafData)
    (h : IdealSheafLocallyDvd (I.comap j) (J.comap j)) (y : Y) :
    ∃ W : X.Opens, j y ∈ W ∧ ∃ K : W.toScheme.IdealSheafData,
      J.comap W.ι = I.comap W.ι * K := by
  obtain ⟨V, hyV, K, hK⟩ := h y
  set d := V.ι ≫ j with hd
  refine ⟨d.opensRange, Scheme.Hom.mem_opensRange.mpr ⟨⟨y, hyV⟩, rfl⟩,
    K.comap d.isoOpensRange.inv, ?_⟩
  have hc : d.isoOpensRange.inv ≫ d = d.opensRange.ι := d.isoOpensRange_inv_comp
  have hK' := congrArg (fun L ↦ Scheme.IdealSheafData.comap L d.isoOpensRange.inv) hK
  rw [Stacks.IdealSheaf.comap_mul] at hK'
  simp only [← Scheme.IdealSheafData.comap_comp] at hK'
  have hc' : d.isoOpensRange.inv ≫ V.ι ≫ j = d.opensRange.ι := hc
  simpa only [Category.assoc, hc'] using hK'

/-- Local divisibility is local on the ambient scheme. -/
theorem idealSheafLocallyDvd_of_openCover {X : Scheme.{u}} {ι : Type*} (V : ι → X.Opens)
    (hcover : ∀ x : X, ∃ i, x ∈ V i) (I J : X.IdealSheafData)
    (h : ∀ i, IdealSheafLocallyDvd (I.comap (V i).ι) (J.comap (V i).ι)) :
    IdealSheafLocallyDvd I J := fun x ↦ by
  obtain ⟨i, hxi⟩ := hcover x
  exact idealSheafLocallyDvd_of_openImmersion_at (V i).ι I J (h i) ⟨x, hxi⟩

/-- Local divisibility of the inverse image of a centre on an affine base survives multiplying
that centre by a further one. -/
theorem idealSheafLocallyDvd_comap_mul_right {S T : Scheme.{u}} [IsAffine S] (e : T ⟶ S)
    {I : S.IdealSheafData} {J : T.IdealSheafData} (h : IdealSheafLocallyDvd J (I.comap e))
    (K : S.IdealSheafData) : IdealSheafLocallyDvd J ((I * K).comap e) := by
  intro t
  obtain ⟨V, htV, L, hL⟩ := h t
  obtain ⟨_, ⟨W₀, hW, rfl⟩, htW, hWV⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open htV V.isOpen
  let W : T.Opens := W₀
  have : IsAffine W.toScheme := hW
  set p : W.toScheme ⟶ V.toScheme := T.homOfLE (show W ≤ V from hWV)
  have hp : p ≫ V.ι = W.ι := by simp [p]
  have hL' := congrArg (fun A ↦ Scheme.IdealSheafData.comap A p) hL
  rw [Stacks.IdealSheaf.comap_mul] at hL'
  simp only [← Scheme.IdealSheafData.comap_comp] at hL'
  rw [show p ≫ V.ι ≫ e = W.ι ≫ e from by rw [← Category.assoc, hp], hp] at hL'
  refine ⟨W, htW, L.comap p * K.comap (W.ι ≫ e), ?_⟩
  rw [← Scheme.IdealSheafData.comap_comp, Stacks.IdealSheaf.comap_mul, hL', mul_assoc]

/-! ### The affine case: Tag 0813 globalized over the source -/

/-- **[Stacks, Tag 0813] globalized over the source.** For an étale morphism of affine schemes
`e : T ⟶ S`, an `a ∈ Γ(S, ⊤)` and a finitely generated `J ⊆ Γ(T, ⊤)` whose vanishing locus
contains that of `a`, there is one finitely generated `I ⊆ Γ(S, ⊤)` with `a ∈ √I` such that near
every prime of `Γ(T, ⊤)` the extension of `I` factors as `J` times a finitely generated ideal.

Quasi-compactness of the spectrum of `Γ(T, ⊤)` turns the pointwise statement of
[Stacks, Tag 0813] into this one: take the product of the finitely many ideals obtained from a
finite subcover, and absorb the extra factors into the second ideal. -/
theorem exists_affine_etale_ideal_center_global {S T : Scheme.{u}} [IsAffine S] [IsAffine T]
    (e : T ⟶ S) [Etale e] (a : Γ(S, ⊤)) (J : Ideal Γ(T, ⊤)) (hJ : J.FG)
    (hV : e.appTop.hom a ∈ J.radical) :
    ∃ I : Ideal Γ(S, ⊤), I.FG ∧ a ∈ I.radical ∧
      ∀ q : PrimeSpectrum Γ(T, ⊤), ∃ g : Γ(T, ⊤), g ∉ q.asIdeal ∧
        ∃ J' : Ideal (Localization.Away g), J'.FG ∧
          Ideal.map ((algebraMap Γ(T, ⊤) (Localization.Away g)).comp e.appTop.hom) I =
            Ideal.map (algebraMap Γ(T, ⊤) (Localization.Away g)) J * J' := by
  classical
  set φ : Γ(S, ⊤) →+* Γ(T, ⊤) := e.appTop.hom with hφ
  have he : φ.Etale := by
    simpa [hφ, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using
      e.etale_appLE (isAffineOpen_top S) (isAffineOpen_top T) (by simp)
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := φ.toAlgebra
  let _ : Algebra.Etale Γ(S, ⊤) Γ(T, ⊤) := he.toAlgebra
  have hlocal (q : PrimeSpectrum Γ(T, ⊤)) :
      ∃ I : Ideal Γ(S, ⊤), I.FG ∧ a ∈ I.radical ∧
        ∃ g : Γ(T, ⊤), g ∉ q.asIdeal ∧
          ∃ J' : Ideal (Localization.Away g), J'.FG ∧
            Ideal.map ((algebraMap Γ(T, ⊤) (Localization.Away g)).comp φ) I =
              Ideal.map (algebraMap Γ(T, ⊤) (Localization.Away g)) J * J' := by
    have _ : q.asIdeal.IsPrime := q.isPrime
    exact exists_ideal_map_eq_mul_after_localization Γ(S, ⊤) Γ(T, ⊤) a J hJ hV q.asIdeal
  choose I hIfg haI g hg J' hJ' hEq using hlocal
  obtain ⟨s, hs⟩ := (isCompact_univ (X := PrimeSpectrum Γ(T, ⊤))).elim_finite_subcover
    (fun q ↦ (PrimeSpectrum.basicOpen (g q) : Set (PrimeSpectrum Γ(T, ⊤))))
    (fun q ↦ PrimeSpectrum.isOpen_basicOpen)
    (fun q _ ↦ Set.mem_iUnion.mpr ⟨q, (PrimeSpectrum.mem_basicOpen (g q) q).mpr (hg q)⟩)
  have hprod (t : Finset (PrimeSpectrum Γ(T, ⊤))) : (∏ q ∈ t, I q).FG := by
    induction t using Finset.induction_on with
    | empty => simpa using Ideal.fg_top Γ(S, ⊤)
    | @insert q t hqt ih => simpa [Finset.prod_insert, hqt] using Ideal.FG.mul (hIfg q) ih
  have hrad (t : Finset (PrimeSpectrum Γ(T, ⊤))) : a ∈ (∏ q ∈ t, I q).radical := by
    induction t using Finset.induction_on with
    | empty => simp [Ideal.radical_top]
    | @insert q t hqt ih =>
      rw [Finset.prod_insert hqt, Ideal.radical_mul]
      exact ⟨haI q, ih⟩
  refine ⟨∏ q ∈ s, I q, hprod s, hrad s, fun p ↦ ?_⟩
  obtain ⟨q, hqs, hp⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ p))
  set ψ : Γ(T, ⊤) →+* Localization.Away (g q) := algebraMap Γ(T, ⊤) (Localization.Away (g q))
    with hψ
  refine ⟨g q, (PrimeSpectrum.mem_basicOpen (g q) p).mp hp,
    J' q * ∏ r ∈ s.erase q, Ideal.map (ψ.comp φ) (I r), ?_, ?_⟩
  · refine Ideal.FG.mul (hJ' q) ?_
    induction s.erase q using Finset.induction_on with
    | empty => simpa using Ideal.fg_top (Localization.Away (g q))
    | @insert r t hrt ih =>
      simpa [Finset.prod_insert, hrt] using Ideal.FG.mul ((hIfg r).map _) ih
  · have hmap (t : Finset (PrimeSpectrum Γ(T, ⊤))) :
        Ideal.map (ψ.comp φ) (∏ r ∈ t, I r) = ∏ r ∈ t, Ideal.map (ψ.comp φ) (I r) := by
      induction t using Finset.induction_on with
      | empty =>
        simpa only [Finset.prod_empty, Ideal.one_eq_top] using Ideal.map_top (ψ.comp φ)
      | @insert r t hrt ih => simp [Finset.prod_insert, hrt, ih, Ideal.map_mul]
    rw [hmap s, ← Finset.mul_prod_erase s (fun r ↦ Ideal.map (ψ.comp φ) (I r)) hqs, hEq q]
    ac_rfl

/-- The affine case over a single basic open: for an étale morphism of affine schemes and a
centre `J` on the source supported away from the inverse image of the basic open of `a`, there is
a centre `I` on the target, of finite presentation and supported away from that basic open, whose
inverse image is locally divisible by `J`. -/
theorem exists_affine_etale_locallyDvd_center_basicOpen {S T : Scheme.{u}} [IsAffine S]
    [IsAffine T] (e : T ⟶ S) [Etale e] (a : Γ(S, ⊤)) (J : T.IdealSheafData)
    (hJ : FinitePresentation J.subschemeι)
    (hdisj : Disjoint (e ⁻¹ᵁ S.basicOpen a : Set T) (J.support : Set T)) :
    ∃ I : S.IdealSheafData, FinitePresentation I.subschemeι ∧
      Disjoint (S.basicOpen a : Set S) (I.support : Set S) ∧
      IdealSheafLocallyDvd J (I.comap e) := by
  set J₀ := J.ideal ⟨⊤, isAffineOpen_top T⟩ with hJ₀
  have hJ₀fg : J₀.FG := (Stacks.Flatness.finitePresentation_subschemeι_iff J).mp hJ _
  have hV : e.appTop.hom a ∈ J₀.radical := by
    refine mem_radical_of_disjoint_basicOpen_support _ J ?_
    simpa only [Scheme.Hom.preimage_basicOpen_top] using hdisj
  obtain ⟨I, hI, haI, hlocal⟩ := exists_affine_etale_ideal_center_global e a J₀ hJ₀fg hV
  refine ⟨Scheme.IdealSheafData.ofIdealTop I, finitePresentation_ofIdealTop_of_fg I hI,
    disjoint_basicOpen_support_of_mem_radical a I haI, fun t ↦ ?_⟩
  obtain ⟨g, hg, K, hK, hfac⟩ := hlocal (T.isoSpec.hom t)
  obtain ⟨K', hK', hfac'⟩ := idealSheaf_factorization_on_basicOpen e I J₀ g K hK hfac
  refine ⟨T.basicOpen g, ?_, Scheme.IdealSheafData.ofIdealTop K', ?_⟩
  · have ht : t ∈ T.isoSpec.hom ⁻¹ᵁ PrimeSpectrum.basicOpen g := hg
    simpa only [Scheme.isoSpec_hom, Scheme.toSpecΓ_preimage_basicOpen] using ht
  · have hJid : Scheme.IdealSheafData.ofIdealTop J₀ = J :=
      Scheme.IdealSheafData.equivOfIsAffine.symm_apply_apply J
    simpa only [hJid, Scheme.IdealSheafData.comap_comp] using hfac'

/-- The affine case over a finite family of basic opens. -/
theorem exists_affine_etale_locallyDvd_center_finite_basicOpens {S T : Scheme.{u}} [IsAffine S]
    [IsAffine T] (e : T ⟶ S) [Etale e] (s : Finset Γ(S, ⊤)) (J : T.IdealSheafData)
    (hJ : FinitePresentation J.subschemeι)
    (hdisj : ∀ a ∈ s, Disjoint (e ⁻¹ᵁ S.basicOpen a : Set T) (J.support : Set T)) :
    ∃ I : S.IdealSheafData, FinitePresentation I.subschemeι ∧
      (∀ a ∈ s, Disjoint (S.basicOpen a : Set S) (I.support : Set S)) ∧
      IdealSheafLocallyDvd J (I.comap e) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨⊥, (Stacks.Flatness.finitePresentation_subschemeι_iff _).mpr
      fun _ ↦ Submodule.fg_bot, by simp, ?_⟩
    rw [Scheme.IdealSheafData.comap_bot]
    exact idealSheafLocallyDvd_of_dvd J ⊥ ⟨⊥, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨I, hI, hIs, hIL⟩ := ih fun b hb ↦ hdisj b (Finset.mem_insert_of_mem hb)
    obtain ⟨K, hK, hKa, hKL⟩ := exists_affine_etale_locallyDvd_center_basicOpen e a J hJ
      (hdisj a (Finset.mem_insert_self ..))
    refine ⟨I ⊔ K, finitePresentation_sup_subschemeι I K hI hK, ?_, ?_⟩
    · intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hKa.mono_right (Scheme.IdealSheafData.support_antitone le_sup_right)
      · exact (hIs b hb).mono_right (Scheme.IdealSheafData.support_antitone le_sup_left)
    · rw [Scheme.IdealSheafData.comap_sup]
      exact idealSheafLocallyDvd_sup hIL hKL

/-- The affine case over a quasi-compact open: cover the open by finitely many basic opens. -/
theorem exists_affine_etale_locallyDvd_center {S T : Scheme.{u}} [IsAffine S] [IsAffine T]
    (e : T ⟶ S) [Etale e] (U : S.Opens) (hU : IsCompact (U : Set S)) (J : T.IdealSheafData)
    (hJ : FinitePresentation J.subschemeι)
    (hdisj : Disjoint (e ⁻¹ᵁ U : Set T) (J.support : Set T)) :
    ∃ I : S.IdealSheafData, FinitePresentation I.subschemeι ∧
      Disjoint (U : Set S) (I.support : Set S) ∧ IdealSheafLocallyDvd J (I.comap e) := by
  classical
  obtain ⟨s, hs, hUs⟩ :=
    isCompact_and_isOpen_iff_finite_and_eq_biUnion_basicOpen.mp ⟨hU, U.isOpen⟩
  have hle (a : Γ(S, ⊤)) (ha : a ∈ hs.toFinset) : S.basicOpen a ≤ U := by
    intro x hx
    show x ∈ (U : Set S)
    rw [hUs]
    exact Set.mem_iUnion₂.mpr ⟨a, hs.mem_toFinset.mp ha, hx⟩
  obtain ⟨I, hI, hIdisj, hIL⟩ := exists_affine_etale_locallyDvd_center_finite_basicOpens e
    hs.toFinset J hJ fun a ha ↦ hdisj.mono_left fun x hx ↦ hle a ha hx
  refine ⟨I, hI, Set.disjoint_left.mpr fun x hx hxI ↦ ?_, hIL⟩
  rw [hUs] at hx
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp hx
  exact Set.disjoint_left.mp (hIdisj a (hs.mem_toFinset.mpr ha)) hxa hxI

/-- Centres on an affine base, one for each member of a finite family of morphisms to it, combine
into a single centre by taking their product. -/
private theorem exists_prod_center_locallyDvd {S : Scheme.{u}} [IsAffine S] {ι : Type*}
    [Finite ι] {T : ι → Scheme.{u}} (e : ∀ i, T i ⟶ S) (U : S.Opens)
    (J : ∀ i, (T i).IdealSheafData)
    (hlocal : ∀ i, ∃ I : S.IdealSheafData, FinitePresentation I.subschemeι ∧
      Disjoint (U : Set S) (I.support : Set S) ∧ IdealSheafLocallyDvd (J i) (I.comap (e i))) :
    ∃ I : S.IdealSheafData, FinitePresentation I.subschemeι ∧
      Disjoint (U : Set S) (I.support : Set S) ∧
      ∀ i, IdealSheafLocallyDvd (J i) (I.comap (e i)) := by
  classical
  have _ := Fintype.ofFinite ι
  choose I hI hIU hIL using hlocal
  refine ⟨∏ i, I i, finitePresentation_prod_subschemeι Finset.univ I hI,
    Stacks.Blowup.disjoint_support_prod U Finset.univ I (fun i _ ↦ hIU i), fun i ↦ ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ I (Finset.mem_univ i)]
  exact idealSheafLocallyDvd_comap_mul_right (e i) (hIL i) _

/-- The affine case for a finite family of étale affine coverings: take the product of the
centres obtained one family member at a time. -/
theorem exists_affine_etale_family_locallyDvd_center {S : Scheme.{u}} [IsAffine S] {ι : Type*}
    [Finite ι] (T : ι → Scheme.{u}) [∀ i, IsAffine (T i)] (e : ∀ i, T i ⟶ S)
    (he : ∀ i, Etale (e i)) (U : S.Opens) (hU : IsCompact (U : Set S))
    (J : ∀ i, (T i).IdealSheafData) (hJ : ∀ i, FinitePresentation (J i).subschemeι)
    (hdisj : ∀ i, Disjoint (e i ⁻¹ᵁ U : Set (T i)) ((J i).support : Set (T i))) :
    ∃ I : S.IdealSheafData, FinitePresentation I.subschemeι ∧
      Disjoint (U : Set S) (I.support : Set S) ∧
      ∀ i, IdealSheafLocallyDvd (J i) (I.comap (e i)) := by
  exact exists_prod_center_locallyDvd e U J fun i ↦ by
    have _ : Etale (e i) := he i
    exact exists_affine_etale_locallyDvd_center (e i) U hU (J i) (hJ i) (hdisj i)

/-! ### An affine base with quasi-compact étale coverings -/

/-- Every point lies in one of the affine opens of a cover of the whole scheme. -/
private theorem exists_mem_of_top_eq_biSup {X : Scheme.{u}} {s : Set X.affineOpens}
    (hcover : (⊤ : X.Opens) = ⨆ i ∈ s, (i : X.Opens)) (x : X) :
    ∃ k : s, x ∈ (k.val.val : X.Opens) := by
  have hx : x ∈ (⊤ : X.Opens) := trivial
  rw [hcover] at hx
  obtain ⟨V, hxV⟩ := Opens.mem_iSup.mp hx
  obtain ⟨hVs, hxV⟩ := Opens.mem_iSup.mp hxV
  exact ⟨⟨V, hVs⟩, hxV⟩

/-- An affine base and one quasi-compact étale morphism onto it: cover the source by finitely
many affine opens and apply the affine case to each. -/
theorem exists_etale_locallyDvd_center_of_isAffine_base {S T : Scheme.{u}} [IsAffine S]
    [CompactSpace T] (e : T ⟶ S) [Etale e] (U : S.Opens) (hU : IsCompact (U : Set S))
    (J : T.IdealSheafData) (hJ : FinitePresentation J.subschemeι)
    (hdisj : Disjoint (e ⁻¹ᵁ U : Set T) (J.support : Set T)) :
    ∃ I : S.IdealSheafData, FinitePresentation I.subschemeι ∧
      Disjoint (U : Set S) (I.support : Set S) ∧ IdealSheafLocallyDvd J (I.comap e) := by
  classical
  obtain ⟨s, hs, hcover⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (X := T) (U := ⊤)).mp isCompact_univ
  have _ := hs.fintype
  let V : s → T.Opens := fun i ↦ i.val.val
  have hIA (i : s) : IsAffine (V i).toScheme := i.val.property
  obtain ⟨I, hI, hIU, hIL⟩ := exists_affine_etale_family_locallyDvd_center
    (fun i : s ↦ (V i).toScheme)
    (fun i ↦ (V i).ι ≫ e) (fun i ↦ inferInstance) U hU
    (fun i ↦ J.comap (V i).ι)
    (fun i ↦ finitePresentation_comap_subschemeι J _ hJ)
    (fun i ↦ by
      rw [Scheme.IdealSheafData.support_comap]
      exact hdisj.preimage _)
  refine ⟨I, hI, hIU, idealSheafLocallyDvd_of_openCover V (fun x ↦ ?_) J (I.comap e) fun i ↦ ?_⟩
  · exact exists_mem_of_top_eq_biSup hcover x
  · simpa only [Scheme.IdealSheafData.comap_comp] using hIL i

/-- An affine base and a finite family of quasi-compact étale morphisms onto it. -/
theorem exists_etale_family_locallyDvd_center_of_isAffine_base {S : Scheme.{u}} [IsAffine S]
    {ι : Type*} [Finite ι] (T : ι → Scheme.{u}) [∀ i, CompactSpace (T i)] (e : ∀ i, T i ⟶ S)
    (he : ∀ i, Etale (e i)) (U : S.Opens) (hU : IsCompact (U : Set S))
    (J : ∀ i, (T i).IdealSheafData) (hJ : ∀ i, FinitePresentation (J i).subschemeι)
    (hdisj : ∀ i, Disjoint (e i ⁻¹ᵁ U : Set (T i)) ((J i).support : Set (T i))) :
    ∃ I : S.IdealSheafData, FinitePresentation I.subschemeι ∧
      Disjoint (U : Set S) (I.support : Set S) ∧
      ∀ i, IdealSheafLocallyDvd (J i) (I.comap (e i)) := by
  exact exists_prod_center_locallyDvd e U J fun i ↦ by
    have _ : Etale (e i) := he i
    exact exists_etale_locallyDvd_center_of_isAffine_base (e i) U hU (J i) (hJ i) (hdisj i)

/-! ### The global statement -/

/-- The centre on an affine open of the base, for a finite family of quasi-compact étale
morphisms onto the base. -/
theorem exists_center_on_affine_open {S : Scheme.{u}} [QuasiSeparatedSpace S] (V : S.Opens)
    [IsAffine V.toScheme] (U : S.Opens) (hU : IsCompact (U : Set S)) {ι : Type*} [Finite ι]
    (Sᵢ : ι → Scheme.{u}) (e : ∀ i, Sᵢ i ⟶ S) (Iᵢ : ∀ i, (Sᵢ i).IdealSheafData)
    (he : ∀ i, Etale (e i) ∧ QuasiCompact (e i))
    (hadm : ∀ i, FinitePresentation (Iᵢ i).subschemeι ∧
      Disjoint (e i ⁻¹ᵁ U : Set (Sᵢ i)) ((Iᵢ i).support : Set (Sᵢ i))) :
    ∃ I : V.toScheme.IdealSheafData, FinitePresentation I.subschemeι ∧
      Disjoint (V.ι ⁻¹ᵁ U : Set V.toScheme) (I.support : Set V.toScheme) ∧
      ∀ i, IdealSheafLocallyDvd ((Iᵢ i).comap (e i ⁻¹ᵁ V).ι) (I.comap (e i ∣_ V)) := by
  have hT (i : ι) : CompactSpace (e i ⁻¹ᵁ V).toScheme := by
    have _ : QuasiCompact (e i) := (he i).2
    exact isCompact_iff_compactSpace.mp
      ((e i).isCompact_preimage (show IsAffineOpen V from ‹IsAffine V.toScheme›).isCompact)
  have heV (i : ι) : Etale (e i ∣_ V) := by
    have _ : Etale (e i) := (he i).1
    infer_instance
  have hUV : IsCompact (V.ι ⁻¹ᵁ U : Set V.toScheme) := V.ι.isCompact_preimage hU
  refine exists_etale_family_locallyDvd_center_of_isAffine_base
    (fun i ↦ (e i ⁻¹ᵁ V).toScheme) (fun i ↦ e i ∣_ V) heV (V.ι ⁻¹ᵁ U) hUV
    (fun i ↦ (Iᵢ i).comap (e i ⁻¹ᵁ V).ι)
    (fun i ↦ finitePresentation_comap_subschemeι (Iᵢ i) _ (hadm i).1) fun i ↦ ?_
  rw [Scheme.IdealSheafData.support_comap]
  refine Set.disjoint_left.mpr fun t htU htI ↦ ?_
  refine Set.disjoint_left.mp (hadm i).2 ?_ htI
  show (((e i ⁻¹ᵁ V).ι ≫ e i).base t) ∈ (U : Set S)
  rw [← morphismRestrict_ι]
  exact htU

/-- **The centre of step 4 of the proof of [Stacks, Tag 0814].** Let `S` be quasi-compact and
quasi-separated, `U ⊆ S` a quasi-compact open, and `e_i : S_i ⟶ S` finitely many quasi-compact
étale morphisms carrying centres `I_i` of finite presentation supported away from `e_i^{-1}(U)`.
There is a centre `I` on `S` of finite presentation, supported away from `U`, whose inverse image
on each `S_i` is locally divisible by `I_i`.

Cover `S` by finitely many affine opens; on each, `Stacks.EtaleCentre.exists_center_on_affine_open`
gives a centre, which extends to `S` by `Stacks.Blowup.exists_idealSheafData_comap_eq`; take the
product of the extensions. -/
theorem exists_global_center_locallyDvd {S : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] (U : S.Opens) (hU : IsCompact (U : Set S)) {ι : Type*} [Finite ι]
    (Sᵢ : ι → Scheme.{u}) (e : ∀ i, Sᵢ i ⟶ S) (Iᵢ : ∀ i, (Sᵢ i).IdealSheafData)
    (he : ∀ i, Etale (e i) ∧ QuasiCompact (e i))
    (hadm : ∀ i, FinitePresentation (Iᵢ i).subschemeι ∧
      Disjoint (e i ⁻¹ᵁ U : Set (Sᵢ i)) ((Iᵢ i).support : Set (Sᵢ i))) :
    ∃ I : S.IdealSheafData, FinitePresentation I.subschemeι ∧
      Disjoint (U : Set S) (I.support : Set S) ∧
      ∀ i, IdealSheafLocallyDvd (Iᵢ i) (I.comap (e i)) := by
  classical
  obtain ⟨s, hs, hcover⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (X := S) (U := ⊤)).mp isCompact_univ
  have _ := hs.fintype
  let V : s → S.Opens := fun k ↦ k.val.val
  have hVA (k : s) : IsAffine (V k).toScheme := k.val.property
  have hlocal (k : s) := exists_center_on_affine_open (V k) U hU Sᵢ e Iᵢ he hadm
  choose A hAfp hAdisj hAdiv using hlocal
  have hExt (k : s) := Stacks.Blowup.exists_idealSheafData_comap_eq U (V k) hU
    (show IsAffineOpen (V k) from k.val.property).isCompact (A k) (hAfp k) (hAdisj k)
  choose G hGfp hGdisj hGrestrict using hExt
  refine ⟨∏ k : s, G k, finitePresentation_prod_subschemeι Finset.univ G hGfp,
    Stacks.Blowup.disjoint_support_prod U Finset.univ G (fun k _ ↦ hGdisj k), fun i ↦ ?_⟩
  refine idealSheafLocallyDvd_of_openCover (fun k : s ↦ e i ⁻¹ᵁ V k)
    (fun t ↦ ?_) (Iᵢ i) ((∏ k : s, G k).comap (e i)) fun k ↦ ?_
  · exact exists_mem_of_top_eq_biSup hcover ((e i).base t)
  · have hRestrict : ((∏ k : s, G k).comap (e i)).comap (e i ⁻¹ᵁ V k).ι =
        ((∏ l : s, G l).comap (V k).ι).comap (e i ∣_ V k) := by
      rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
      exact congrArg (Scheme.IdealSheafData.comap (∏ l : s, G l))
        (morphismRestrict_ι (e i) (V k)).symm
    have hprod : (∏ l : s, G l).comap (V k).ι =
        A k * ((∏ l ∈ Finset.univ.erase k, G l).comap (V k).ι) := by
      rw [← Finset.mul_prod_erase Finset.univ G (Finset.mem_univ k),
        Stacks.IdealSheaf.comap_mul, hGrestrict k]
    rw [hRestrict, hprod]
    exact idealSheafLocallyDvd_comap_mul_right (e i ∣_ V k) (hAdiv k i) _

end Stacks.EtaleCentre

end
