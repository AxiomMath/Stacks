module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist
public import StacksFrontier.AlgebraicGeometry.InvertibleLocallyFree.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The twisting sheaves are trivial, hence invertible, on a standard open

Let `S` be a graded ring, `X = Proj(S)`, and let `f ∈ S` be homogeneous of degree `d`. For every
integer `n` the twisting sheaf `𝒪_X(nd)` becomes trivial once restricted to the standard open
`D₊(f)`: it is isomorphic there to the structure sheaf, viewed as a module over itself. Being
isomorphic to the unit object, it is in particular invertible. The trivializing section is `f ^ n`,
the homogeneous fraction `f ^ max n 0 / f ^ max (-n) 0`.

The restriction is taken on the *restricted site*: for an open `U` of the site
`Opens(Proj S)`, Mathlib's `SheafOfModules.over` sends a sheaf of modules to a sheaf of modules
over the sheaf of rings `𝒪_X.over U` on the induced topology `J.over U` of the over-category
`Over U`. Objects of `Over U` are the opens contained in `U`, so this is exactly the restriction
of the sheaf to the open subspace, and the unit object there is `𝒪_X|_U`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTrivialization.twistingSheafOverBasicOpenIsoUnit`: the
  trivialization `𝒪_X(nd)|_{D₊(f)} ≅ 𝒪_X|_{D₊(f)}`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTrivialization.isInvertible_twistingSheafOverBasicOpen`: the
  restriction `𝒪_X(nd)|_{D₊(f)}` is invertible.
* `Stacks.AlgebraicGeometry.ProjTrivialization.bijective_trivializingHom`: on every open
  `W ⊆ D₊(f)`, multiplication by the trivializing section is a bijection
  `Γ(W, 𝒪_X) → Γ(W, 𝒪_X(nd))`.

## References

* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.ProjTrivialization

universe u w

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- The homogeneous ideal of a point of `Proj 𝒮` is a prime ideal. -/
local instance (x : ProjectiveSpectrum.top 𝒮) : x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

variable {f : S} {d : ℕ}

/-- Multiplying an element of the integer-extended degree `j` piece by `f ^ q` lands in the
nonnegative degree `j + q * d`. -/
lemma mul_pow_mem_of_mem_integerGrading (hf : f ∈ 𝒮 d) {j : ℤ} {m : S}
    (hm : m ∈ integerGrading 𝒮 j) {q N : ℕ} (hN : j + q * d = (N : ℤ)) :
    m * f ^ q ∈ 𝒮 N := by
  rcases le_or_gt 0 j with hj | hj
  · have hm' : m ∈ 𝒮 j.toNat := by simpa [integerGrading, hj] using hm
    simpa only [smul_eq_mul, show j.toNat + q * d = N by omega] using
      SetLike.mul_mem_graded hm' (SetLike.pow_mem_graded q hf)
  · obtain rfl : m = 0 := by simpa [integerGrading, not_le.mpr hj] using hm
    simp [zero_mem]

omit [GradedRing 𝒮] in
/-- The integer-extended grading in a nonnegative degree is the grading itself. -/
lemma mem_integerGrading_natCast {j : ℕ} {m : S} (hm : m ∈ 𝒮 j) :
    m ∈ integerGrading 𝒮 (j : ℤ) := by
  simpa [integerGrading] using hm

/-- A power of a homogeneous element of degree `d` is homogeneous of the multiple degree. -/
lemma pow_toNat_mem (hf : f ∈ 𝒮 d) (p : ℕ) : f ^ p ∈ 𝒮 (p * d) := by
  simpa only [smul_eq_mul] using SetLike.pow_mem_graded p hf

/-- For `n : ℤ` and `d k : ℕ`, `(k + n * d) + max (-n) 0 * d = k + max n 0 * d` in `ℤ`. -/
lemma toNat_degree_add (n : ℤ) (d k : ℕ) :
    (((k : ℤ) + n * d) + (((-n).toNat * d : ℕ) : ℤ)) = ((k + n.toNat * d : ℕ) : ℤ) := by
  have key : ((-n).toNat : ℤ) + n = n.toNat := by omega
  push_cast
  linear_combination (d : ℤ) * key

/-- `f ^ n`, read as an element of the local ring at a point `x` of `D₊(f)`: the fraction with
numerator `f ^ max n 0` and denominator `f ^ max (-n) 0`. -/
noncomputable def trivializingFun (n : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) (x : W) :
    Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl :=
  Localization.mk (f ^ n.toNat)
    ⟨f ^ (-n).toNat, x.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hW x.2) _⟩

/-- The inverse of `trivializingFun`, namely `f ^ (-n)`. -/
noncomputable def trivializingFunInv (n : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) (x : W) :
    Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl :=
  Localization.mk (f ^ (-n).toNat)
    ⟨f ^ n.toNat, x.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hW x.2) _⟩

/-- `trivializingFunInv` is a right inverse of `trivializingFun`. -/
lemma trivializingFun_mul_inv (n : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) (x : W) :
    trivializingFun 𝒮 n hW x * trivializingFunInv 𝒮 n hW x = 1 := by
  rw [trivializingFun, trivializingFunInv, Localization.mk_mul, ← Localization.mk_one]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp [mul_comm]))

/-- At every point of `D₊(f)` the element `f ^ n` is a unit of the local ring. -/
lemma isUnit_trivializingFun (n : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) (x : W) :
    IsUnit (trivializingFun 𝒮 n hW x) :=
  IsUnit.of_mul_eq_one _ (trivializingFun_mul_inv 𝒮 n hW x)

/-- The trivializing function is a section of the twisting sheaf: it is the single homogeneous
fraction `f ^ max n 0 / f ^ max (-n) 0`, whose numerator and denominator have degrees differing
by exactly `n * d`. -/
lemma trivializingFun_mem (hf : f ∈ 𝒮 d) (n : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    trivializingFun 𝒮 n hW ∈ moduleSections 𝒮 (twistGrading 𝒮 (n * d)) W := by
  intro x
  refine ⟨W, x.2, 𝟙 _, (-n).toNat * d, f ^ n.toNat, f ^ (-n).toNat, ?_,
    pow_toNat_mem 𝒮 hf _,
    fun y ↦ y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hW y.2) _, fun y ↦ rfl⟩
  show f ^ n.toNat ∈ integerGrading 𝒮 ((((-n).toNat * d : ℕ) : ℤ) + n * d)
  rw [show (((-n).toNat * d : ℕ) : ℤ) + n * d = ((n.toNat * d : ℕ) : ℤ) by
    have h := toNat_degree_add n d 0
    push_cast at h ⊢
    linarith]
  exact mem_integerGrading_natCast 𝒮 (pow_toNat_mem 𝒮 hf _)

/-- The trivializing section of `𝒪(nd)` over an open contained in `D₊(f)`. -/
noncomputable def trivializingSection (hf : f ∈ 𝒮 d) (n : ℤ)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    moduleSections 𝒮 (twistGrading 𝒮 (n * d)) W :=
  ⟨trivializingFun 𝒮 n hW, trivializingFun_mem 𝒮 hf n hW⟩

/-- Multiplication by the trivializing section, as a map of modules over the ring of sections
of the structure sheaf on `W`. -/
noncomputable def trivializingHom (hf : f ∈ 𝒮 d) (n : ℤ)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W) →ₗ[
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W)]
      moduleSections 𝒮 (twistGrading 𝒮 (n * d)) W :=
  LinearMap.toSpanSingleton _ _ (trivializingSection 𝒮 hf n hW)

/-- The value of `trivializingHom` on `r` at `x` is `r x` times the trivializing value. -/
lemma trivializingHom_apply (hf : f ∈ 𝒮 d) (n : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W)) (x : W) :
    (trivializingHom 𝒮 hf n hW r).1 x =
      HomogeneousLocalization.val (r.1 x) * trivializingFun 𝒮 n hW x := rfl

/-- Two elements of the local ring whose products with the trivializing value agree are
equal. -/
lemma eq_of_val_mul_eq (n : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) (x : W)
    {ρ ρ' : HomogeneousLocalization.AtPrime 𝒮 x.1.asHomogeneousIdeal.toIdeal}
    (h : HomogeneousLocalization.val ρ * trivializingFun 𝒮 n hW x =
      HomogeneousLocalization.val ρ' * trivializingFun 𝒮 n hW x) : ρ = ρ' :=
  HomogeneousLocalization.val_injective _
    ((isUnit_trivializingFun 𝒮 n hW x).mul_right_cancel h)

/-- Locally on `D₊(f)`, a section of `𝒪(nd)` is the trivializing value times a fraction `u / v`
whose numerator and denominator are homogeneous of the same degree. -/
lemma exists_isFraction_of_mem (hf : f ∈ 𝒮 d) (n : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (a : moduleSections 𝒮 (twistGrading 𝒮 (n * d)) W) (x : W) :
    ∃ (V : Opens (ProjectiveSpectrum.top 𝒮)) (_ : x.1 ∈ V) (i : V ⟶ W) (N : ℕ) (u v : S)
      (_ : u ∈ 𝒮 N) (_ : v ∈ 𝒮 N) (hv : ∀ y : V, v ∉ y.1.asHomogeneousIdeal),
      ∀ y : V, Localization.mk u ⟨v, hv y⟩ * trivializingFun 𝒮 n hW (i y) = a.1 (i y) := by
  obtain ⟨V, hxV, i, k, m, s, hm, hs, hnin, heq⟩ := a.2 x
  refine ⟨V, hxV, i, k + n.toNat * d, m * f ^ (-n).toNat, s * f ^ n.toNat,
    mul_pow_mem_of_mem_integerGrading 𝒮 hf hm (toNat_degree_add n d k),
    SetLike.mul_mem_graded hs (pow_toNat_mem 𝒮 hf n.toNat),
    fun y ↦ y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hnin y)
      (y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hW (i y).2) _), fun y ↦ ?_⟩
  have hy : a.1 (i y) = Localization.mk m ⟨s, hnin y⟩ := heq y
  rw [trivializingFun, Localization.mk_mul, hy]
  exact Localization.mk_eq_mk_iff.mpr
    (Localization.r_of_eq (by simp only [Submonoid.coe_mul]; ring))

/-- Pointwise, every section of `𝒪(nd)` on an open of `D₊(f)` is the trivializing value times
an element of the local ring. -/
lemma exists_val_mul_eq (hf : f ∈ 𝒮 d) (n : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (a : moduleSections 𝒮 (twistGrading 𝒮 (n * d)) W) (x : W) :
    ∃ ρ : HomogeneousLocalization.AtPrime 𝒮 x.1.asHomogeneousIdeal.toIdeal,
      HomogeneousLocalization.val ρ * trivializingFun 𝒮 n hW x = a.1 x := by
  obtain ⟨V, hxV, i, N, u, v, hu, hv, hvn, heq⟩ := exists_isFraction_of_mem 𝒮 hf n hW a x
  exact ⟨HomogeneousLocalization.mk ⟨N, ⟨u, hu⟩, ⟨v, hv⟩, hvn ⟨x.1, hxV⟩⟩, heq ⟨x.1, hxV⟩⟩

/-- The pointwise quotient of a section of `𝒪(nd)` by the trivializing value. -/
noncomputable def preimageFun (hf : f ∈ 𝒮 d) (n : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (a : moduleSections 𝒮 (twistGrading 𝒮 (n * d)) W) (x : W) :
    HomogeneousLocalization.AtPrime 𝒮 x.1.asHomogeneousIdeal.toIdeal :=
  (exists_val_mul_eq 𝒮 hf n hW a x).choose

/-- `preimageFun` times the trivializing value is the given section. -/
lemma preimageFun_spec (hf : f ∈ 𝒮 d) (n : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (a : moduleSections 𝒮 (twistGrading 𝒮 (n * d)) W) (x : W) :
    HomogeneousLocalization.val (preimageFun 𝒮 hf n hW a x) * trivializingFun 𝒮 n hW x =
      a.1 x :=
  (exists_val_mul_eq 𝒮 hf n hW a x).choose_spec

/-- The pointwise quotient of a section of `𝒪(nd)` by the trivializing value is a section of
the structure sheaf. -/
lemma preimageFun_mem (hf : f ∈ 𝒮 d) (n : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (a : moduleSections 𝒮 (twistGrading 𝒮 (n * d)) W) :
    (ProjectiveSpectrum.StructureSheaf.isLocallyFraction 𝒮).pred
      (preimageFun 𝒮 hf n hW a) := by
  intro x
  obtain ⟨V, hxV, i, N, u, v, hu, hv, hvn, heq⟩ := exists_isFraction_of_mem 𝒮 hf n hW a x
  refine ⟨V, hxV, i, N, ⟨u, hu⟩, ⟨v, hv⟩, hvn, fun y ↦ eq_of_val_mul_eq 𝒮 n hW (i y) ?_⟩
  rw [preimageFun_spec, HomogeneousLocalization.val_mk]
  exact (heq y).symm

/-- Multiplication by the trivializing section is a bijection
`Γ(W, 𝒪) → Γ(W, 𝒪(nd))` on every open `W` contained in `D₊(f)`. -/
lemma bijective_trivializingHom (hf : f ∈ 𝒮 d) (n : ℤ)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    Function.Bijective (trivializingHom 𝒮 hf n hW) :=
  ⟨fun _ _ h ↦ Subtype.ext (funext fun x ↦
      eq_of_val_mul_eq 𝒮 n hW x (congr_fun (congr_arg Subtype.val h) x)),
    fun a ↦ ⟨⟨preimageFun 𝒮 hf n hW a, preimageFun_mem 𝒮 hf n hW a⟩,
      Subtype.ext (funext (preimageFun_spec 𝒮 hf n hW a))⟩⟩

/-- The trivialization of `𝒪(nd)` over an open contained in `D₊(f)`, at the level of sections. -/
noncomputable def trivializingEquiv (hf : f ∈ 𝒮 d) (n : ℤ)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W) ≃ₗ[
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W)]
      moduleSections 𝒮 (twistGrading 𝒮 (n * d)) W :=
  LinearEquiv.ofBijective _ (bijective_trivializingHom 𝒮 hf n hW)

/-- At every point of `W`, the inverse of `trivializingEquiv` applied to a section `t` of `𝒪(nd)`,
times the trivializing value, is the value of `t`. -/
lemma val_trivializingEquiv_symm_mul (hf : f ∈ 𝒮 d) (n : ℤ)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (t : moduleSections 𝒮 (twistGrading 𝒮 (n * d)) W) (x : W) :
    HomogeneousLocalization.val (((trivializingEquiv 𝒮 hf n hW).symm t).1 x) *
      trivializingFun 𝒮 n hW x = t.1 x :=
  congr_fun (congr_arg Subtype.val ((trivializingEquiv 𝒮 hf n hW).apply_symm_apply t)) x

/-- The structure sheaf of `Proj 𝒮`, read as a sheaf of (not necessarily commutative) rings on
the site `Opens (ProjectiveSpectrum.top 𝒮)`: the sheaf of rings over which the twisting sheaves
are modules. It is Mathlib's `AlgebraicGeometry.Scheme.ringCatSheaf` of `Proj 𝒮`. -/
noncomputable abbrev projRingSheaf :
    Sheaf (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮)) RingCat.{u} :=
  (sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
    (forget₂ CommRingCat.{u} RingCat.{u})).obj (ProjectiveSpectrum.Proj.structureSheaf 𝒮)

/-- `projRingSheaf` is Mathlib's sheaf of rings of the scheme `Proj 𝒮`. -/
lemma ringCatSheaf_eq :
    (_root_.AlgebraicGeometry.Proj 𝒮).ringCatSheaf = projRingSheaf 𝒮 := rfl

/-- Finite direct sums of sheaves of modules over `projRingSheaf 𝒮` exist, and agree with finite
products. -/
instance hasFiniteBiproducts_projRingSheaf :
    Limits.HasFiniteBiproducts (SheafOfModules.{u} (projRingSheaf 𝒮)) :=
  Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-- `D₊(f)` as an open of the scheme `Proj 𝒮` is the open of the site on which the twisting
sheaves live. -/
lemma proj_basicOpen_eq (g : S) :
    _root_.AlgebraicGeometry.Proj.basicOpen 𝒮 g = ProjectiveSpectrum.basicOpen 𝒮 g := rfl

/-- The sections of the restricted twisting sheaf over an object of the restricted site are the
sections of the twisting sheaf over the underlying open. -/
lemma twistingSheafOver_obj_carrier (n : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒮))
    (V : (Over U)ᵒᵖ) :
    (((twistingSheaf 𝒮 n).over U).val.obj V : Type u) =
      ↥(moduleSections 𝒮 (twistGrading 𝒮 n) V.unop.left) := rfl

/-- The sections of the unit object of the restricted site are the sections of the structure
sheaf over the underlying open. -/
lemma unitOver_obj_carrier (U : Opens (ProjectiveSpectrum.top 𝒮)) (V : (Over U)ᵒᵖ) :
    ((SheafOfModules.unit
        ((projRingSheaf 𝒮).over U)).val.obj V : Type u) =
      ((ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op V.unop.left) : Type u) := rfl

/-- The trivialization of `𝒪(nd)` on the restricted site of `D₊(f)`, as an isomorphism of
presheaves of modules out of the structure sheaf. -/
noncomputable def unitOverIsoTwistingSheafOver (hf : f ∈ 𝒮 d) (n : ℤ) :
    (SheafOfModules.unit ((projRingSheaf 𝒮).over
        (ProjectiveSpectrum.basicOpen 𝒮 f))).val ≅
      ((twistingSheaf 𝒮 (n * d)).over (ProjectiveSpectrum.basicOpen 𝒮 f)).val :=
  PresheafOfModules.isoMk
    (fun V ↦ (trivializingEquiv 𝒮 hf n (leOfHom V.unop.hom)).toModuleIso)
    (fun {_ _} _ ↦ ModuleCat.hom_ext (LinearMap.ext fun _ ↦ Subtype.ext (funext fun _ ↦ rfl)))

/-- For `f` homogeneous of degree `d`, the twisting sheaf `𝒪(nd)` restricted to the standard
open `D₊(f)` is trivial: it is isomorphic to the structure sheaf of the restricted site. The
trivializing section is `f ^ n`. -/
@[ega "II 2.5.7",
  ega "II 3.2.5" "O(nd)|X_f ≅ O|X_f",
  ega "II 2.6.4" "(f)",
  ega "II 8.14.7" "more general"]
noncomputable def twistingSheafOverBasicOpenIsoUnit (hf : f ∈ 𝒮 d) (n : ℤ) :
    (twistingSheaf 𝒮 (n * d)).over (ProjectiveSpectrum.basicOpen 𝒮 f) ≅
      SheafOfModules.unit ((projRingSheaf 𝒮).over
        (ProjectiveSpectrum.basicOpen 𝒮 f)) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (unitOverIsoTwistingSheafOver 𝒮 hf n).symm

/-- For `f` homogeneous of degree `d`, the twisting sheaf `𝒪(nd)` restricted to the standard
open `D₊(f)` is invertible. -/
@[ega "II 2.5.8" "single D_+(f)",
  ega "II 2.5.7" "invertibility only",
  ega "II 3.2.5" "invertibility on X_f"]
theorem isInvertible_twistingSheafOverBasicOpen (hf : f ∈ 𝒮 d) (n : ℤ) :
    _root_.AlgebraicGeometry.SheafOfModules.IsInvertible
      ((Over.forget (ProjectiveSpectrum.basicOpen 𝒮 f)).op ⋙
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj)
      ((projRingSheaf 𝒮).over (ProjectiveSpectrum.basicOpen 𝒮 f)).property
      ((twistingSheaf 𝒮 (n * d)).over (ProjectiveSpectrum.basicOpen 𝒮 f)) :=
  Stacks.InvertibleLocallyFree.isInvertible_of_isTrivial _ _
    ⟨twistingSheafOverBasicOpenIsoUnit 𝒮 hf n⟩

end Stacks.AlgebraicGeometry.ProjTrivialization

end
