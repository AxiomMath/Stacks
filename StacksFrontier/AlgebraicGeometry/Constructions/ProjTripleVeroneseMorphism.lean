module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleClassifyingMorphism

/-!
# A Veronese restriction classifies the same morphism, and clause (3) implies clause (4)

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `X = Proj(A)` and `Y` a scheme. A triple
`(d, L, ψ)` over `Y` — an integer `d ≥ 1`, an invertible `𝒪_Y`-module `L` and a graded ring map
`ψ : A^{(d)} ⟶ Γ_*(Y, L)` whose degree-`d` values generate `L` — classifies a morphism
`Y ⟶ X` by [Stacks, Tag 01N8]. For a weight `k ≥ 1` the *Veronese restriction*
`(kd, L^{⊗ k}, ψ|_{A^{(kd)}})` is again such a triple.

The result proved here is that the Veronese restriction classifies **the same morphism**, and the
consequence drawn from it is the implication (3) ⇒ (4) of [Stacks, Tag 01NB]: two triples whose
Veronese restrictions at weights `a` and `a'` with `ad = a'd'` are carried into one another by an
isomorphism `β : L^{⊗ a} ≅ (L')^{⊗ a'}` classify the same morphism `Y ⟶ X`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTripleVeroneseMorphism.classifyingMorphism_veroneseRestrict`:
  **the Veronese restriction of a triple classifies the same morphism `Y ⟶ Proj(A)`.**
* `Stacks.AlgebraicGeometry.ProjTripleVeroneseMorphism.sameMorphism_of_agreeAtSome`:
  **clause (3) implies clause (4) of [Stacks, Tag 01NB].**
* `Stacks.AlgebraicGeometry.ProjTripleVeroneseMorphism.sameMorphism_of_agree` and
  `sameMorphism_of_agreeAtLcm`: the same for clause (2) — the agreement condition at `dd'` — and
  for clause (1) — the agreement condition at `lcm(d, d')`, which are the two instances
  `(a, a') = (d', d)` and `(a, a') = (lcm/d, lcm/d')` of clause (3).

The converse implication (4) ⇒ (1), which closes the cycle of the tag, is
`Stacks.AlgebraicGeometry.ProjTripleMorphismConverse.agreeAtLcm_of_sameMorphism`; it consumes
`classifyingMorphism_veroneseRestrict` below for the same reduction to a common weight.

## Implementation notes

**Why the comparison of the two classified morphisms is made directly and not through a
compatible pair.** The morphism classified by a triple is the first component of the unique pair
`(φ, α)` of [Stacks, Tag 01N8], so the natural route to
`classifyingMorphism_veroneseRestrict` is to exhibit a pair for the restricted triple whose first
component is the one of the original. That route needs `α^{⊗ k}` and the degree-one clause of
`Stacks.AlgebraicGeometry.MorphismToProjUniversal.IsCompatible` for it, which is the tensor-power
square `α^{⊗ k}(ψ^d_φ(x)) = ψ(x)` in degree `k` — not available, see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Constructions/ProjTripleClassifyingMorphism.lean`. The route taken
instead uses only the *morphism* half of the uniqueness assertion,
`Stacks.AlgebraicGeometry.ProjSectionsUnique.eq_of_smul_restrict_eq`, which mentions no tensor
power of `α`: the two morphisms are compared over the cover of `Y` by the nonvanishing opens
`Y_{ψ(f)}`, `f ∈ A_d`, and on `Y_{ψ(f)}` both factor through the affine open `D₊(f)`, where they
are determined by their ring maps on the fractions `a/f^n`.

**The degree mismatch, and how `f ^ k` closes it.** The local identity
`ψ(a)|_V = φ^♯(a/f^n) · ψ(f)^n|_V` of [Stacks, Tag 01N8] is available for the restricted triple
only at the homogeneous elements of degree `kd`, and for the original triple only at those of
degree `d`. The two meet at `f ^ k` for `f` of degree `d`: the standard opens `D₊(f ^ k)` and
`D₊(f)` coincide (`AlgebraicGeometry.Proj.basicOpen_pow`), the fraction `a/f^n` of `A_{(f)}` is
the fraction `a f^{(k-1)n} / (f^k)^n` of `A_{(f^k)}`
(`AlgebraicGeometry.Proj.awayMap_awayToSection`), and the local identity of the original triple at
`a` becomes the local identity at `a f^{(k-1)n}` after multiplying through by `ψ(f)^{(k-1)n}`.
Since `ψ(f)^{kn}` is nonvanishing on `Y_{ψ(f)}`, the two ring maps agree there.

## References

* [Stacks Project, Tag 01NB](https://stacks.math.columbia.edu/tag/01NB)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry
open HomogeneousLocalization
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.MorphismToProjUniversal
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.AlgebraicGeometry.ProjSectionsUnique (Pair eq_of_smul_restrict_eq)
open Stacks.AlgebraicGeometry.ProjTripleClassifying
open Stacks.AmplePullbackPart1 (natTensorPowCongr)
open Stacks.MorphismToProj.HomogeneousRatios (pow_mem)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowers (natTensorPow)
open Stacks.TensorPowerTrivialize (resTop)

universe u w

namespace Stacks.AlgebraicGeometry.ProjTripleVeroneseMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y : Scheme.{u}} {d : ℕ}

/-! ### Two morphisms into `Proj A` that agree on a cover by standard opens -/

/-- **Two morphisms `Y ⟶ Proj A` are equal as soon as they agree on a cover by preimages of
standard opens `D₊(f)` with `f` homogeneous of one positive degree `d`.** This is the morphism
half of the uniqueness assertion of [Stacks, Tag 01N8] with neither morphism required to factor
through `U_d` and with the preimages required only to *contain* the covering opens: both
morphisms restrict to morphisms `W f ⟶ D₊(f)`, the target is affine
(`AlgebraicGeometry.Proj.isAffineOpen_basicOpen`), so the restrictions are determined by the ring
maps, and the `W f` cover `Y`. -/
theorem eq_of_appLE_eq_of_cover {ξ ξ' : Y ⟶ AlgebraicGeometry.Proj 𝒜} (hd : 0 < d)
    {W : 𝒜 d → Y.Opens} (hcover : ⨆ f : 𝒜 d, W f = ⊤)
    (hW : ∀ f : 𝒜 d, W f ≤ ξ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))
    (hW' : ∀ f : 𝒜 d, W f ≤ ξ' ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))
    (happ : ∀ f : 𝒜 d,
      ξ.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) (W f) (hW f)
        = ξ'.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) (W f) (hW' f)) :
    ξ = ξ' := by
  refine Scheme.hom_ext_of_forall _ _ fun p => ?_
  obtain ⟨f, hf⟩ := Opens.mem_iSup.mp (hcover ▸ (Opens.mem_top p : p ∈ (⊤ : Y.Opens)))
  refine ⟨W f, hf, ?_⟩
  have haff : IsAffine (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)).toScheme :=
    AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒜 (f : A) f.2 hd
  rw [← Scheme.Hom.resLE_comp_ι ξ (hW f), ← Scheme.Hom.resLE_comp_ι ξ' (hW' f)]
  refine congrArg (· ≫ _) (AlgebraicGeometry.ext_of_isAffine ?_)
  simp only [Scheme.Hom.resLE_app_top, happ f]

/-- **`eq_of_appLE_eq_of_cover` with the ring maps compared on the fractions `a/f^n` alone.**
These exhaust `A_{(f)}` by `HomogeneousLocalization.Away.mk_surjective`, and they are the
elements for which the degreewise identity of [Stacks, Tag 01N8] gives the value of `φ^♯`. -/
theorem eq_of_appLE_eq_on_away_of_cover {ξ ξ' : Y ⟶ AlgebraicGeometry.Proj 𝒜} (hd : 0 < d)
    {W : 𝒜 d → Y.Opens} (hcover : ⨆ f : 𝒜 d, W f = ⊤)
    (hW : ∀ f : 𝒜 d, W f ≤ ξ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))
    (hW' : ∀ f : 𝒜 d, W f ≤ ξ' ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))
    (happ : ∀ (f : 𝒜 d) (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)),
      ξ.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) (W f) (hW f)
          (AlgebraicGeometry.Proj.awayToSection 𝒜 (f : A) (Away.mk 𝒜 f.2 n a ha))
        = ξ'.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) (W f) (hW' f)
          (AlgebraicGeometry.Proj.awayToSection 𝒜 (f : A) (Away.mk 𝒜 f.2 n a ha))) :
    ξ = ξ' := by
  refine eq_of_appLE_eq_of_cover 𝒜 hd hcover hW hW' fun f => ?_
  ext z
  obtain ⟨n, a, ha, hmk⟩ := Away.mk_surjective 𝒜 f.2
    ((AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 (f : A) f.2 hd).inv z)
  have hz : AlgebraicGeometry.Proj.awayToSection 𝒜 (f : A) (Away.mk 𝒜 f.2 n a ha) = z := by
    rw [← AlgebraicGeometry.Proj.basicOpenIsoAway_hom 𝒜 (f : A) f.2 hd, hmk]
    exact ConcreteCategory.congr_hom
      (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 (f : A) f.2 hd).inv_hom_id z
  rw [← hz]
  exact happ f n a ha

/-! ### The fraction `a/f^n` read in `A_{(f^k)}` -/

/-- **Two presentations of one fraction of `A_{(f)}` give the same element.** The degree recorded
in `HomogeneousLocalization.Away.mk` is part of the numerator-denominator datum but not of the
class it defines, so a fraction may be presented with the degree of `f` read in any homogeneous
component containing it. -/
theorem away_mk_congr {f : A} {d₁ d₂ : ℕ} (h₁ : f ∈ 𝒜 d₁) (h₂ : f ∈ 𝒜 d₂) (n : ℕ)
    {b₁ b₂ : A} (hb₁ : b₁ ∈ 𝒜 (n • d₁)) (hb₂ : b₂ ∈ 𝒜 (n • d₂)) (hb : b₁ = b₂) :
    Away.mk 𝒜 h₁ n b₁ hb₁ = Away.mk 𝒜 h₂ n b₂ hb₂ :=
  HomogeneousLocalization.val_injective _ (by rw [Away.val_mk, Away.val_mk, hb])

/-- **The value of `φ^♯` on the fraction `a f^{(k-1)n} / (f^k)^n` of `A_{(f^k)}` is its value on
the fraction `a/f^n` of `A_{(f)}`.** The two fractions are one and the same regular function on
`D₊(f^k) = D₊(f)`: the ring map `A_{(f)} → A_{(f^k)}` of
`HomogeneousLocalization.awayMap` sends the second to the first
(`HomogeneousLocalization.awayMap_mk`) and is compatible with the sections of the structure sheaf
(`AlgebraicGeometry.Proj.awayMap_awayToSection`). -/
theorem appLE_awayToSection_pow {ξ : Y ⟶ AlgebraicGeometry.Proj 𝒜} {f : A} {k' : ℕ}
    (hf : f ∈ 𝒜 d) (hfk : f ^ (k' + 1) ∈ 𝒜 ((k' + 1) * d)) {V : Y.Opens}
    (hV : V ≤ ξ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f ^ (k' + 1)))
    (hV' : V ≤ ξ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d))
    (hxmem : a * f ^ (k' * n) ∈ 𝒜 (n • ((k' + 1) * d))) :
    ξ.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (f ^ (k' + 1))) V hV
        (AlgebraicGeometry.Proj.awayToSection 𝒜 (f ^ (k' + 1))
          (Away.mk 𝒜 hfk n (a * f ^ (k' * n)) hxmem))
      = ξ.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 f) V hV'
        (AlgebraicGeometry.Proj.awayToSection 𝒜 f (Away.mk 𝒜 hf n a ha)) := by
  have hg : f ^ k' ∈ 𝒜 (k' * d) := pow_mem hf k'
  have hx : f ^ (k' + 1) = f * f ^ k' := by rw [pow_succ, mul_comm]
  have hmap : awayMap 𝒜 hg hx (Away.mk 𝒜 hf n a ha)
      = Away.mk 𝒜 hfk n (a * f ^ (k' * n)) hxmem := by
    rw [awayMap_mk]
    exact away_mk_congr 𝒜 _ hfk n _ hxmem (by rw [pow_mul])
  have key := ConcreteCategory.congr_hom
    (AlgebraicGeometry.Proj.awayMap_awayToSection 𝒜 hg hx) (Away.mk 𝒜 hf n a ha)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at key
  rw [hmap] at key
  rw [key]
  exact ConcreteCategory.congr_hom
    (ξ.map_appLE hV (homOfLE (AlgebraicGeometry.Proj.basicOpen_mono 𝒜 f _ ⟨_, hx⟩)).op) _

/-! ### The values of a Veronese restriction, read in the tensor powers of `L` -/

variable {L : Y.Modules}

/-- **The comparison `(L^{⊗ k})^{⊗ m} ≅ L^{⊗ km}` carries the degree-`m` value of the Veronese
restriction of `ψ` to the degree-`km` value of `ψ`**, which is how the restriction is defined. -/
theorem powVeroneseIso_hom_app_veroneseRestrict (ψ : VeroneseSections 𝒜 d L) (k m : ℕ)
    (b : 𝒜 (m * (k * d))) (b' : 𝒜 (k * m * d)) (hbb : (b' : A) = (b : A)) :
    (ProjVeroneseRestrict.powVeroneseIso L k m).hom.app ⊤
        ((ProjVeroneseRestrict.veroneseRestrict 𝒜 ψ k).toFun m b)
      = ψ.toFun (k * m) b' := by
  rw [ProjVeroneseRestrict.veroneseRestrict_toFun,
    ProjVeroneseRestrict.veroneseComp_apply 𝒜 ψ k m b b' hbb,
    ProjVeroneseRestrict.hom_app_inv_app]

/-- `powVeroneseIso_hom_app_veroneseRestrict` over an open `V`, on the restriction of the global
section: the comparison is a morphism of `𝒪_Y`-modules, so it commutes with restriction. -/
theorem resTop_veroneseRestrict (ψ : VeroneseSections 𝒜 d L) (k m : ℕ) (V : Y.Opens)
    (b : 𝒜 (m * (k * d))) (b' : 𝒜 (k * m * d)) (hbb : (b' : A) = (b : A)) :
    (ProjVeroneseRestrict.powVeroneseIso L k m).hom.app V
        (resTop (natTensorPow (natTensorPow L k) m)
          ((ProjVeroneseRestrict.veroneseRestrict 𝒜 ψ k).toFun m b) V)
      = resTop (natTensorPow L (k * m)) (ψ.toFun (k * m) b') V := by
  rw [← Stacks.TensorPowerTrivialize.resTop_app,
    powVeroneseIso_hom_app_veroneseRestrict 𝒜 ψ k m b b' hbb]

variable [Stacks.Ample.IsInvertibleModule Y L]

/-- **The local identity `ψ(a)|_V = c · ψ(f)^n|_V` propagates to `a f^j` in degree `n + j`**, by
multiplying both sides by `ψ(f)^j`: the left-hand side becomes `ψ(a f^j)` by the
multiplicativity of `ψ` and the right-hand side `c · ψ(f)^{n+j}` by
`…VeroneseSections.mulSections_pow`. This is the step that turns the fraction `a/f^n` into the
fraction `a f^j/f^{n+j}` with the same value. -/
theorem resTop_toFun_mul_pow (ψ : VeroneseSections 𝒜 d L) {f : A} (hf : f ∈ 𝒜 d) (n j : ℕ)
    {V : Y.Opens} {c : Γ(Y, V)} {a : A} (han : a ∈ 𝒜 (n * d))
    (h : resTop (natTensorPow L n) (ψ.toFun n ⟨a, han⟩) V
        = c • resTop (natTensorPow L n) (ψ.pow hf n) V)
    {m : ℕ} (hm : n + j = m) (b : 𝒜 (m * d)) (hb : (b : A) = a * f ^ j) :
    resTop (natTensorPow L m) (ψ.toFun m b) V
      = c • resTop (natTensorPow L m) (ψ.pow hf m) V := by
  subst hm
  have hprod : ψ.toFun (n + j) b = mulSections L (ψ.toFun n ⟨a, han⟩) (ψ.pow hf j) :=
    ψ.map_mul n j ⟨a, han⟩ ⟨f ^ j, pow_mem hf j⟩ b hb
  rw [hprod, ← ψ.mulSections_pow hf n j]
  exact resTop_mulSections_smul_left L (ψ.pow hf j) h

/-- **The trivializing section of the Veronese restriction at `f ^ k` is nonvanishing exactly
where `ψ(f)^k` is.** The value of the restriction at `f ^ k` *is* `ψ(f)^k`, read through the
comparison `(L^{⊗ k})^{⊗ 1} ≅ L^{⊗ k}` and the left unitor. -/
theorem nonvanishingOpen_psiSection_veroneseRestrict (ψ : VeroneseSections 𝒜 d L) (k : ℕ)
    {f : A} (hf : f ∈ 𝒜 d) (hfk : f ^ k ∈ 𝒜 (k * d)) :
    nonvanishingOpen Y (natTensorPow L k)
        (psiSection 𝒜 (ProjVeroneseRestrict.veroneseRestrict 𝒜 ψ k) ⟨f ^ k, hfk⟩)
      = nonvanishingOpen Y (natTensorPow L k) (ψ.pow hf k) := by
  rw [psiSection, ProjVeroneseRestrict.veroneseRestrict_pow_pow 𝒜 ψ k hf hfk]
  refine Opens.ext ?_
  refine (Stacks.Ample.nonvanishingLocus_congr (unitorPow (natTensorPow L k)) _).trans ?_
  refine (Stacks.Ample.nonvanishingLocus_congr
    (ProjVeroneseRestrict.powVeroneseIso L k 1).symm _).trans ?_
  exact Stacks.Ample.nonvanishingLocus_congr
    (eqToIso (congrArg (natTensorPow L) (Nat.mul_one k).symm)) _

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- **The degree-`n` local identity of [Stacks, Tag 01N8] for a pair compatible with the Veronese
restriction of `ψ`, read in `L^{⊗ kn}`.** The clause is stated in `(L^{⊗ k})^{⊗ n}`; applying the
comparison `(L^{⊗ k})^{⊗ n} ≅ L^{⊗ kn}`, which is a morphism of `𝒪_Y`-modules and therefore
commutes with restriction and with the scalar action, turns it into a statement about the
degree-`kn` value of `ψ` itself. -/
theorem resTop_of_isCompatible_veroneseRestrict {ψ : VeroneseSections 𝒜 d L} (k : ℕ)
    {q : Pair 𝒜 (natTensorPow L k) (k * d)}
    (hq : IsCompatible 𝒜 (ProjVeroneseRestrict.veroneseRestrict 𝒜 ψ k) q)
    {f : A} (hf : f ∈ 𝒜 d) (hfk : f ^ k ∈ 𝒜 (k * d)) {V : Y.Opens}
    (hV : V ≤ toProj 𝒜 q.1 ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f ^ k))
    (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • (k * d))) (b : 𝒜 (n * (k * d))) (hbx : (b : A) = x)
    (b' : 𝒜 (k * n * d)) (hb' : (b' : A) = x) :
    resTop (natTensorPow L (k * n)) (ψ.toFun (k * n) b') V
      = (toProj 𝒜 q.1).appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (f ^ k)) V hV
          (AlgebraicGeometry.Proj.awayToSection 𝒜 (f ^ k) (Away.mk 𝒜 hfk n x hx))
        • resTop (natTensorPow L (k * n)) (ψ.pow hf (k * n)) V := by
  have e := resTop_veroneseRestrict 𝒜 ψ k n V b b' (hb'.trans hbx.symm)
  have e' := resTop_veroneseRestrict 𝒜 ψ k n V ⟨(f ^ k) ^ n, pow_mem hfk n⟩
    ⟨f ^ (k * n), pow_mem hf (k * n)⟩ (pow_mul f k n)
  have h2 := congrArg (fun z => (ProjVeroneseRestrict.powVeroneseIso L k n).hom.app V z)
    (hq.2 ⟨f ^ k, hfk⟩ V hV n x hx b hbx)
  simp only [Scheme.Modules.Hom.app_smul] at h2
  rw [e] at h2
  rw [h2]
  exact congrArg _ e'

/-- **A pair compatible with `ψ` and a pair compatible with the Veronese restriction of `ψ`
induce the same ring map on the fractions `a/f^n`, `f ∈ A_d`.** Both values of `φ^♯` satisfy the
local identity for the degree-`kn` element `a f^{(k-1)n}`, whose fraction by `(f^k)^n` is
`a/f^n`, with the same left-hand side; since `ψ(f)^{kn}` is nonvanishing on `V` the two values
agree (`Stacks.AlgebraicGeometry.ProjSectionsUnique.eq_of_smul_restrict_eq`). -/
theorem appLE_eq_veroneseRestrict {ψ : VeroneseSections 𝒜 d L} {k' : ℕ}
    {p : Pair 𝒜 L d} (hp : IsCompatible 𝒜 ψ p)
    {q : Pair 𝒜 (natTensorPow L (k' + 1)) ((k' + 1) * d)}
    (hq : IsCompatible 𝒜 (ProjVeroneseRestrict.veroneseRestrict 𝒜 ψ (k' + 1)) q)
    (f : 𝒜 d) {V : Y.Opens}
    (hVp : V ≤ toProj 𝒜 p.1 ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))
    (hVq : V ≤ toProj 𝒜 q.1 ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))
    (hVnv : V ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow f.2 1))
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    (toProj 𝒜 p.1).appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) V hVp
        (AlgebraicGeometry.Proj.awayToSection 𝒜 (f : A) (Away.mk 𝒜 f.2 n a ha))
      = (toProj 𝒜 q.1).appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) V hVq
        (AlgebraicGeometry.Proj.awayToSection 𝒜 (f : A) (Away.mk 𝒜 f.2 n a ha)) := by
  have hfk : (f : A) ^ (k' + 1) ∈ 𝒜 ((k' + 1) * d) := pow_mem f.2 (k' + 1)
  have hVq' : V ≤ toProj 𝒜 q.1 ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen 𝒜 ((f : A) ^ (k' + 1)) := by
    rw [AlgebraicGeometry.Proj.basicOpen_pow 𝒜 _ (k' + 1) (Nat.succ_pos k')]
    exact hVq
  have han : a ∈ 𝒜 (n * d) := by simpa [smul_eq_mul] using ha
  have hmul := SetLike.mul_mem_graded han (pow_mem f.2 (k' * n))
  have hmem : ∀ N, n * d + k' * n * d = N → a * (f : A) ^ (k' * n) ∈ 𝒜 N := fun N h =>
    ProjVeroneseRestrict.mem_graded_of_eq 𝒜 h hmul
  have hbmem := hmem ((k' + 1) * n * d) (by ring)
  have hxmem := hmem (n • ((k' + 1) * d)) (by simp only [smul_eq_mul]; ring)
  have hbmem' := hmem (n * ((k' + 1) * d)) (by ring)
  have h0 := resTop_toFun_mul_pow 𝒜 ψ f.2 n (k' * n) han
    (hp.2 f V hVp n a ha ⟨a, han⟩ rfl) (by ring) ⟨_, hbmem⟩ rfl
  have h1 := resTop_of_isCompatible_veroneseRestrict 𝒜 (k' + 1) hq f.2 hfk hVq' n
    (a * (f : A) ^ (k' * n)) hxmem ⟨_, hbmem'⟩ rfl ⟨_, hbmem⟩ rfl
  rw [appLE_awayToSection_pow 𝒜 f.2 hfk hVq' hVq n a ha hxmem] at h1
  exact eq_of_smul_restrict_eq (natTensorPow L ((k' + 1) * n)) (ψ.pow f.2 ((k' + 1) * n))
    (hVnv.trans (ψ.le_nonvanishingOpen_pow f.2 ((k' + 1) * n))) h0 h1

/-! ### The Veronese restriction classifies the same morphism -/

/-- **The Veronese restriction of a triple at a weight `k ≥ 1` classifies the same morphism
`Y ⟶ Proj(A)`.** Both morphisms send the nonvanishing open `Y_{ψ(f)}`, `f ∈ A_d`, into the
standard open `D₊(f) = D₊(f^k)` — for the restriction because its trivializing section at `f^k`
is `ψ(f)^k` — and on `Y_{ψ(f)}` they induce the same ring map on the fractions `a/f^n`
(`appLE_eq_veroneseRestrict`). Since the `Y_{ψ(f)}` cover `Y`, the two morphisms are equal
(`eq_of_appLE_eq_on_away_of_cover`). -/
theorem classifyingMorphism_veroneseRestrict (t : Triple 𝒜 Y) (k : ℕ) (hk : 0 < k) :
    (t.veroneseRestrict k hk).classifyingMorphism = t.classifyingMorphism := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have := t.isInvertible
  have hp := isCompatible_classifyingPair 𝒜 t.deg_pos t.psi t.generated
  have hq := isCompatible_classifyingPair 𝒜 (Nat.mul_pos hk t.deg_pos)
    (ProjVeroneseRestrict.veroneseRestrict 𝒜 t.psi (k' + 1))
    (ProjVeroneseRestrict.iSup_nonvanishingOpen_veroneseRestrict 𝒜 t.psi (k' + 1) t.generated)
  have hW : ∀ f : 𝒜 t.deg,
      nonvanishingOpen Y t.module (psiSection 𝒜 t.psi f)
        ≤ toProj 𝒜 (classifyingPair 𝒜 (Nat.mul_pos hk t.deg_pos)
            (ProjVeroneseRestrict.veroneseRestrict 𝒜 t.psi (k' + 1))
            (ProjVeroneseRestrict.iSup_nonvanishingOpen_veroneseRestrict 𝒜 t.psi (k' + 1)
              t.generated)).1 ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) := fun f => by
    have hfk : (f : A) ^ (k' + 1) ∈ 𝒜 ((k' + 1) * t.deg) := pow_mem f.2 (k' + 1)
    rw [← AlgebraicGeometry.Proj.basicOpen_pow 𝒜 (f : A) (k' + 1) (Nat.succ_pos k'),
      preimage_basicOpen_eq 𝒜 hq ⟨(f : A) ^ (k' + 1), hfk⟩,
      nonvanishingOpen_psiSection_veroneseRestrict 𝒜 t.psi (k' + 1) f.2 hfk,
      nonvanishingOpen_psiSection 𝒜 t.psi f]
    exact t.psi.le_nonvanishingOpen_pow f.2 (k' + 1)
  exact eq_of_appLE_eq_on_away_of_cover 𝒜 t.deg_pos t.generated hW
    (fun f => (preimage_basicOpen_eq 𝒜 hp f).ge)
    fun f n a ha => (appLE_eq_veroneseRestrict 𝒜 hp hq f
      (preimage_basicOpen_eq 𝒜 hp f).ge (hW f)
      (nonvanishingOpen_psiSection 𝒜 t.psi f).le n a ha).symm

/-! ### Clause (3) implies clause (4) -/

/-- **Two triples of one and the same weight that an isomorphism `β` carries into one another
classify the same morphism.** This is
`Stacks.AlgebraicGeometry.ProjTripleClassifying.sameMorphism_of_sectionsEquiv` with the two
weights only *equal*, not syntactically identical, and with the degreewise condition stated for
the two readings of one homogeneous element — the shape in which clause (3) of [Stacks, Tag 01NB]
produces it, where the common degree is reached as `ad` on one side and as `a'd'` on the
other. -/
theorem classifyingMorphism_eq_of_agree (t t' : Triple 𝒜 Y) (hdeg : t.deg = t'.deg)
    (β : t.module ≅ t'.module)
    (hβ : ∀ (m : ℕ) (x : 𝒜 (m * t.deg)) (x' : 𝒜 (m * t'.deg)), (x : A) = (x' : A) →
      (natTensorPowCongr β m).hom.app ⊤ (t.psi.toFun m x) = t'.psi.toFun m x') :
    t.classifyingMorphism = t'.classifyingMorphism := by
  obtain ⟨e, he, L, hL, ψ, hgen⟩ := t
  obtain ⟨e', he', L', hL', ψ', hgen'⟩ := t'
  subst hdeg
  have := hL
  have := hL'
  exact sameMorphism_of_sectionsEquiv 𝒜 he hgen hgen'
    ⟨β, fun m x => hβ m x x rfl⟩

/-- **Stacks Tag 01NB, clause (3) implies clause (4).** Let `(d, L, ψ)` and `(d', L', ψ')` be
triples over `Y` for the graded ring `A`. Suppose that for some positive `n = ad = a'd'` there is
an isomorphism `β : L^{⊗ a} ≅ (L')^{⊗ a'}` such that `β ∘ ψ|_{A^{(n)}}` and `ψ'|_{A^{(n)}}`
agree as graded ring maps `A^{(n)} → Γ_*(Y, (L')^{⊗ a'})` — in degree `m` that `β^{⊗ m}` carries
the value of `ψ|_{A^{(n)}}` on a homogeneous element of degree `mn` to the value of
`ψ'|_{A^{(n)}}` on it. Then the two triples classify **the same morphism** `Y ⟶ Proj(A)`.

Both triples classify the same morphism as their Veronese restrictions
(`classifyingMorphism_veroneseRestrict`), and the two restrictions are triples of one and the
same weight `n` carried into one another by `β` (`classifyingMorphism_eq_of_agree`). -/
theorem sameMorphism_of_agreeAtSome (t t' : Triple 𝒜 Y) {a a' : ℕ} (ha : 0 < a) (ha' : 0 < a')
    (hn : a * t.deg = a' * t'.deg)
    (β : natTensorPow t.module a ≅ natTensorPow t'.module a')
    (hβ : ∀ (m : ℕ) (x : 𝒜 (m * (a * t.deg))) (x' : 𝒜 (m * (a' * t'.deg))),
        (x : A) = (x' : A) →
      (natTensorPowCongr β m).hom.app ⊤
          ((ProjVeroneseRestrict.veroneseRestrict 𝒜 t.psi a).toFun m x)
        = (ProjVeroneseRestrict.veroneseRestrict 𝒜 t'.psi a').toFun m x') :
    SameMorphism 𝒜 t t' :=
  ((classifyingMorphism_veroneseRestrict 𝒜 t a ha).symm.trans
    (classifyingMorphism_eq_of_agree 𝒜 (t.veroneseRestrict a ha) (t'.veroneseRestrict a' ha')
      hn β hβ)).trans (classifyingMorphism_veroneseRestrict 𝒜 t' a' ha')

/-- **Stacks Tag 01NB, clause (2) implies clause (4).** Equivalent triples — the agreement
condition at `n = dd'`, with `β : L^{⊗ d'} ≅ (L')^{⊗ d}` — classify the same morphism. This is
`sameMorphism_of_agreeAtSome` at `(a, a') = (d', d)`. -/
theorem sameMorphism_of_agree (t t' : Triple 𝒜 Y)
    (β : natTensorPow t.module t'.deg ≅ natTensorPow t'.module t.deg)
    (hβ : ∀ (m : ℕ) (x : 𝒜 (m * (t'.deg * t.deg))) (x' : 𝒜 (m * (t.deg * t'.deg))),
        (x : A) = (x' : A) →
      (natTensorPowCongr β m).hom.app ⊤
          ((ProjVeroneseRestrict.veroneseRestrict 𝒜 t.psi t'.deg).toFun m x)
        = (ProjVeroneseRestrict.veroneseRestrict 𝒜 t'.psi t.deg).toFun m x') :
    SameMorphism 𝒜 t t' :=
  sameMorphism_of_agreeAtSome 𝒜 t t' t'.deg_pos t.deg_pos (mul_comm t'.deg t.deg) β hβ

/-- **Stacks Tag 01NB, clause (1) implies clause (4).** The agreement condition at
`n = lcm(d, d')`, with `β : L^{⊗ (n/d)} ≅ (L')^{⊗ (n/d')}`, makes the two triples classify the
same morphism. This is `sameMorphism_of_agreeAtSome` at
`(a, a') = (lcm(d, d')/d, lcm(d, d')/d')`. -/
theorem sameMorphism_of_agreeAtLcm (t t' : Triple 𝒜 Y)
    (β : natTensorPow t.module (Nat.lcm t.deg t'.deg / t.deg) ≅
      natTensorPow t'.module (Nat.lcm t.deg t'.deg / t'.deg))
    (hβ : ∀ (m : ℕ) (x : 𝒜 (m * (Nat.lcm t.deg t'.deg / t.deg * t.deg)))
        (x' : 𝒜 (m * (Nat.lcm t.deg t'.deg / t'.deg * t'.deg))), (x : A) = (x' : A) →
      (natTensorPowCongr β m).hom.app ⊤
          ((ProjVeroneseRestrict.veroneseRestrict 𝒜 t.psi
            (Nat.lcm t.deg t'.deg / t.deg)).toFun m x)
        = (ProjVeroneseRestrict.veroneseRestrict 𝒜 t'.psi
            (Nat.lcm t.deg t'.deg / t'.deg)).toFun m x') :
    SameMorphism 𝒜 t t' := by
  have hlcm : 0 < Nat.lcm t.deg t'.deg := Nat.lcm_pos t.deg_pos t'.deg_pos
  refine sameMorphism_of_agreeAtSome 𝒜 t t'
    (Nat.div_pos (Nat.le_of_dvd hlcm (Nat.dvd_lcm_left t.deg t'.deg)) t.deg_pos)
    (Nat.div_pos (Nat.le_of_dvd hlcm (Nat.dvd_lcm_right t.deg t'.deg)) t'.deg_pos) ?_ β hβ
  rw [Nat.div_mul_cancel (Nat.dvd_lcm_left t.deg t'.deg),
    Nat.div_mul_cancel (Nat.dvd_lcm_right t.deg t'.deg)]

end Stacks.AlgebraicGeometry.ProjTripleVeroneseMorphism

end
