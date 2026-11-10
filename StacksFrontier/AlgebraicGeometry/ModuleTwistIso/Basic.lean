module

public import StacksFrontier.AlgebraicGeometry.GoodOpenClose.Basic
public import StacksFrontier.AlgebraicGeometry.ProjShifted.Basic
public import StacksFrontier.AlgebraicGeometry.TwistTensor.Basic

/-!
# The comparison map `M̃ ⊗ 𝒪(nd) → M(nd)~` is an isomorphism on the invertible locus

Let `S` be a graded ring, `X = Proj(S)`, `M` a `ℤ`-graded `S`-module with grading `𝒨`, and `d` a
natural number. Let `W_d` be the largest open on which every twist `𝒪_X(dn)` is invertible and
every multiplication map `𝒪_X(dn) ⊗ 𝒪_X(dm) → 𝒪_X(dn + dm)` is an isomorphism. This file proves
that the canonical comparison

`M̃ ⊗_{𝒪_X} 𝒪_X(dn) ⟶ M(dn)~`

of `Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap` restricts to an isomorphism on `W_d`,
for every graded module and every integer `n`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleTwistIso.moduleTwistMap_isIso_on_whereInvertible`: the
  comparison map is an isomorphism on `W_d`.
* `Stacks.AlgebraicGeometry.ModuleTwistIso.isIso_restrictFunctor_moduleTwistMap`: the same for
  every open contained in the ratio locus `⋃ D₊(fg)`, `deg f = deg g + d`; `W_d` is contained in
  it by `Stacks.AlgebraicGeometry.GoodOpenClose.whereInvertible_le_ratioLocus`.
* `Stacks.AlgebraicGeometry.ModuleTwistIso.isIso_stalkFunctor_map_moduleTwist`: at every point of
  a standard open `D₊(pq)` with `deg p = deg q + d` the comparison is an isomorphism on stalks,
  with no hypothesis on `d`.
* `Stacks.AlgebraicGeometry.ModuleTwistIso.bijective_ratioModuleHom`: on every open
  `W ⊆ D₊(pq)`, multiplication by `(p/q)^n` is a bijection `Γ(W, M̃) → Γ(W, M(nd)~)`.

## Implementation notes

* `attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf` and
  `attribute [local instance_reducible] ProjectiveSpectrum.top` are needed because the carrier of
  `Proj 𝒮` is spelled `ProjectiveSpectrum.top 𝒮` by the trivialization machinery and
  `↥(Proj 𝒮).toRingedSpace` by the tensor machinery. The two spellings are interchangeable by
  `exact` but not by `rw`.
* In `bijective_moduleTwistMap_toTensorSheafSection` the left tensor factor is pinned with
  `(A := moduleSections 𝒮 𝒨 W)`; read off the morphism instead, it becomes
  `(associatedModuleSheaf 𝒮 𝒨).val.obj (op W)`, and the `Module` instance over
  `(structureSheaf 𝒮).obj.obj (op W)` is then not found.
* `SetLike.GradedSMul.smul_mem` is given `(A := 𝒮) (B := 𝒨)` explicitly in `ratioInvSMul_mem`:
  its membership hypothesis is about `shiftedGrading 𝒨 c`, and with the arguments implicit the
  elaborator reads the family off that hypothesis.
* In `isIso_stalkFunctor_map_moduleTwist` the `Functor.map_comp` and `isIso_comp_left_iff` steps
  are given as explicit terms with the `IsIso` instance supplied positionally, because instance
  search does not see through the abbreviations `modulePreTensor`, `moduleUnitAb` and
  `moduleTwistAb`.
* The twist index is carried as a variable `c` with the hypothesis `n * d = c`: the statement
  writes `d * n` while the trivialization is indexed by `n * d`, and the two are equal only
  propositionally in `ℤ`.
* The `VAdd ℕ ℤ` action is the scoped `Stacks.GradedLocalization.instVAddNatInt`, the one
  `Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap` is stated with.
* The positivity hypothesis `0 < d` of `moduleTwistMap_isIso_on_whereInvertible` is not used.
* Local freeness of rank one of `𝒪(1)` at a point does not place that point in the ratio locus:
  for `S = k[α, β]` with `deg α = 1`, `deg β = 2` and `x` the homogeneous prime `(α)`, the stalk
  of `𝒪(1)` at `x` is free of rank one over the local ring — every homogeneous element of odd
  degree is divisible by `α`, every one outside `(α)` has even degree, and `S` is a domain —
  while `x` is not in `ratioLocus 𝒮 1` by parity.
* The global statement `M̃ ⊗ 𝒪(a) ≅ M(a)~` on all of `Proj S` is false for a general graded ring.

## References

* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 01MK](https://stacks.math.columbia.edu/tag/01MK)
* [Stacks Project, Tag 0AG2](https://stacks.math.columbia.edu/tag/0AG2)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open Stacks.AlgebraicGeometry.ProjShifted
open Stacks.GradedLocalization
open Stacks.GradedModule (shiftedGrading)
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.ModuleTwistIso

universe u w t

variable {S M : Type u} {σ : Type w} {τ : Type t} [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-! ### A rank-one free right factor recognizes isomorphisms out of a tensor product -/

section Abstract

variable {R A B C : Type*} [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]

/-- A map out of `A ⊗ B` is bijective as soon as `B` is free of rank one and tensoring with its
generator is a bijection `A → C`. -/
lemma bijective_of_tmul_right_generator (eB : R ≃ₗ[R] B) (h : A ⊗[R] B → C) (g : A → C)
    (hg : ∀ x : A, h (x ⊗ₜ[R] eB 1) = g x) (hbij : Function.Bijective g) :
    Function.Bijective h := by
  set ψ : A ≃ₗ[R] A ⊗[R] B :=
    (TensorProduct.rid R A).symm.trans (TensorProduct.congr (LinearEquiv.refl R A) eB) with hψ
  have hψ_apply : ∀ x : A, ψ x = x ⊗ₜ[R] eB 1 := by
    intro x
    rw [hψ]
    simp [TensorProduct.congr_tmul]
  have hcomp : (h : A ⊗[R] B → C) = g ∘ (ψ.symm : A ⊗[R] B → A) := by
    funext z
    have hz : ψ (ψ.symm z) = z := ψ.apply_symm_apply z
    simp only [Function.comp_apply]
    rw [← hg, ← hψ_apply, hz]
  rw [hcomp]
  exact hbij.comp ψ.symm.bijective

end Abstract

/-! ### The pointwise formula for the comparison map -/

/-- The localization of the right unitor `M ⊗_S S → M`, read through the identification of the
localization of a tensor product with the tensor product of the localizations, is the action of
the second local value on the first. -/
lemma map_rid_tensorLocalization (P : Submonoid S) (u : LocalizedModule P M)
    (v : LocalizedModule P S) :
    LocalizedModule.map P (TensorProduct.rid S M).toLinearMap
      (tensorLocalizationEquivOverLocalization (S := S) (M := M) (N := S) P (u ⊗ₜ[S] v))
      = v • u := by
  induction u using LocalizedModule.induction_on with
  | h x s =>
    induction v using LocalizedModule.induction_on with
    | h y t =>
      rw [tensorLocalizationEquivOverLocalization_mk, LocalizedModule.map_mk,
        LinearEquiv.coe_coe, TensorProduct.rid_tmul, mul_comm s t]
      exact (LocalizedModule.mk_smul_mk y x t s).symm

/-- The comparison map `M̃ ⊗ 𝒪(a) → M(a)~` sends the image of a pure tensor of honest sections
to the section whose value at each point is the local value of the twist acting on the local
value of the module section. -/
lemma moduleTwistMap_tmul (a : ℤ) (W : Opens (ProjectiveSpectrum.top 𝒮))
    (ς : ProjectiveSpectrum.Proj.moduleSections 𝒮 𝒨 W)
    (ϑ : ProjectiveSpectrum.Proj.moduleSections 𝒮 (twistGrading (S := S) 𝒮 a) W) (x : W) :
    ((((moduleTwistMap 𝒮 𝒨 a).val.app (op W)).hom
      (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection (AlgebraicGeometry.Proj
        𝒮).toRingedSpace
        (associatedModuleSheaf 𝒮 𝒨) (twistingSheaf 𝒮 a) (op W) (ς ⊗ₜ[_] ϑ))).1 x)
      = ϑ.1 x • ς.1 x := by
  let _ := tensorGrading_decomposition (S := S) 𝒮 𝒨 (twistGrading (S := S) 𝒮 a)
  let _ := tensorGrading_gradedSMul (S := S) 𝒮 𝒨 (twistGrading (S := S) 𝒮 a)
  have hcomp : ((moduleTwistMap 𝒮 𝒨 a).val.app (op W)).hom
      (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection (AlgebraicGeometry.Proj
        𝒮).toRingedSpace
        (associatedModuleSheaf 𝒮 𝒨) (twistingSheaf 𝒮 a) (op W) (ς ⊗ₜ[_] ϑ))
      = ((associatedModuleSheafMap 𝒮
          (Stacks.GradedModule.tensorGrading 𝒨 (twistGrading (S := S) 𝒮 a))
          (shiftedGrading 𝒨 a) (TensorProduct.rid S M).toLinearMap
          (Stacks.GradedModule.rid_mem_shiftedGrading 𝒮 𝒨 a)).val.app (op W)).hom
        (((associatedModuleSheafTensorMap 𝒮 𝒨
            (twistGrading (S := S) 𝒮 a)).val.app (op W)).hom
          (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection (AlgebraicGeometry.Proj
            𝒮).toRingedSpace
            (associatedModuleSheaf 𝒮 𝒨) (twistingSheaf 𝒮 a) (op W) (ς ⊗ₜ[_] ϑ))) := rfl
  have hstep : ((moduleTwistMap 𝒮 𝒨 a).val.app (op W)).hom
      (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection (AlgebraicGeometry.Proj
        𝒮).toRingedSpace
        (associatedModuleSheaf 𝒮 𝒨) (twistingSheaf 𝒮 a) (op W) (ς ⊗ₜ[_] ϑ))
      = ((associatedModuleSheafMap 𝒮
          (Stacks.GradedModule.tensorGrading 𝒨 (twistGrading (S := S) 𝒮 a))
          (shiftedGrading 𝒨 a) (TensorProduct.rid S M).toLinearMap
          (Stacks.GradedModule.rid_mem_shiftedGrading 𝒮 𝒨 a)).val.app (op W)).hom
        (tensorModuleSectionsAddHom 𝒮 𝒨 (twistGrading (S := S) 𝒮 a) W (ς ⊗ₜ[_] ϑ)) :=
    hcomp.trans (congrArg _ (associatedModuleSheafTensorMap_app_toTensorSheafSection 𝒮 𝒨
      (twistGrading (S := S) 𝒮 a) (op W) _))
  rw [hstep, tensorModuleSectionsAddHom_tmul]
  exact map_rid_tensorLocalization _ _ _

/-! ### The trivialization of the shift on the sections over an open of `D₊(pq)` -/

variable {p q : S} {e d : ℕ}

/-- The index identity behind the module trivialization: multiplying by `(p/q)^n` turns a local
fraction of `M̃` of degrees `(k, k)` into one of degrees `(numDeg + k, denDeg + k)`, and
`denDeg + k` in the shifted grading is exactly `numDeg + k`. -/
lemma shift_index_eq {n c : ℤ} (hc : (n : ℤ) * d = c) (k : ℕ) :
    ((denDeg e d n + k : ℕ) : ℤ) + c = ((numDeg e d n : ℕ) : ℤ) + (k : ℤ) := by
  have h := denDeg_add_mul e d n
  rw [hc] at h
  push_cast at h ⊢
  linarith

/-- Multiplying a section of `𝒩₁~` by the local value of `a / b`, where `b ∈ 𝒮 j` is invertible at
every point of `W` and `a` carries `𝒩₁ k` into `𝒩₂ (j + k)`, gives a section of `𝒩₂~`. -/
private lemma smul_mk_mem_moduleSections (𝒩₁ 𝒩₂ : ℤ → τ) [SetLike.GradedSMul 𝒮 𝒩₁]
    [SetLike.GradedSMul 𝒮 𝒩₂] {W : Opens (ProjectiveSpectrum.top 𝒮)} {a b : S} {j : ℕ}
    (hb : b ∈ 𝒮 j) (hbW : ∀ x : W, b ∈ x.1.asHomogeneousIdeal.toIdeal.primeCompl)
    (ha : ∀ (k : ℕ) (m : M), m ∈ 𝒩₁ k → a • m ∈ 𝒩₂ ((j + k : ℕ) : ℤ))
    (f : ∀ x : W, Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl)
    (hf : ∀ x, f x = Localization.mk a ⟨b, hbW x⟩)
    (ς : ProjectiveSpectrum.Proj.moduleSections 𝒮 𝒩₁ W) :
    (fun x => f x • ς.1 x) ∈ ProjectiveSpectrum.Proj.moduleSections 𝒮 𝒩₂ W := by
  intro x
  obtain ⟨V, hxV, i, k, m, s, hm, hs, hn, hy⟩ := ς.2 x
  refine ⟨V, hxV, i, j + k, a • m, b * s, ha k m hm, SetLike.mul_mem_graded hb hs,
    fun y => y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hbW (i y)) (hn y), fun y => ?_⟩
  have hy' : ς.1 (i y) = LocalizedModule.mk m ⟨s, hn y⟩ := hy y
  change f (i y) • ς.1 (i y) = _
  rw [hy', hf]
  exact LocalizedModule.mk_smul_mk _ _ _ _

omit [DirectSum.Decomposition 𝒨] in
/-- Multiplying a section of `M̃` by the trivializing value `(p/q)^n` gives a section of
`M(nd)~`. -/
lemma ratioSMul_mem (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n c : ℤ} (hc : (n : ℤ) * d = c)
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q))
    (ς : ProjectiveSpectrum.Proj.moduleSections 𝒮 𝒨 W) :
    (fun x => ratioFun 𝒮 n hW x • ς.1 x) ∈
      ProjectiveSpectrum.Proj.moduleSections 𝒮 (shiftedGrading 𝒨 c) W :=
  smul_mk_mem_moduleSections 𝒮 𝒨 _ (ratioDen_mem 𝒮 hp hq n)
    (fun x => denMonomial_mem_primeCompl 𝒮 (hW x.2) n.toNat (-n).toNat) (fun k m hm => by
      have hsm := SetLike.GradedSMul.smul_mem (A := 𝒮) (B := 𝒨) (ratioNum_mem 𝒮 hp hq n) hm
      change _ ∈ 𝒨 (((denDeg e d n + k : ℕ) : ℤ) + c)
      rw [shift_index_eq (d := d) hc k]
      exact hsm) _ (fun _ => rfl) ς

omit [DirectSum.Decomposition 𝒨] in
/-- Multiplying a section of `M(nd)~` by the inverse value `(q/p)^n` gives a section of `M̃`. -/
lemma ratioInvSMul_mem (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n c : ℤ} (hc : (n : ℤ) * d = c)
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q))
    (ϑ : ProjectiveSpectrum.Proj.moduleSections 𝒮 (shiftedGrading 𝒨 c) W) :
    (fun x => ratioFunInv 𝒮 n hW x • ϑ.1 x) ∈
      ProjectiveSpectrum.Proj.moduleSections 𝒮 𝒨 W :=
  smul_mk_mem_moduleSections 𝒮 _ 𝒨 (ratioNum_mem 𝒮 hp hq n)
    (fun x => numMonomial_mem_primeCompl 𝒮 (hW x.2) n.toNat (-n).toNat) (fun k m hm => by
      have hm' : m ∈ 𝒨 ((k : ℤ) + c) := hm
      have hsm := SetLike.GradedSMul.smul_mem (A := 𝒮) (B := 𝒨) (ratioDen_mem 𝒮 hp hq n) hm'
      change _ ∈ 𝒨 ((numDeg e d n + k : ℕ) : ℤ)
      rw [show ((numDeg e d n + k : ℕ) : ℤ)
          = (denDeg e d n : ℕ) +ᵥ ((k : ℤ) + c) from by
        change _ = ((denDeg e d n : ℕ) : ℤ) + ((k : ℤ) + c)
        have h := shift_index_eq (d := d) (e := e) hc k
        push_cast at h ⊢
        linarith]
      exact hsm) _ (fun _ => rfl) ϑ

omit [DirectSum.Decomposition 𝒨] in
/-- On every open `W ⊆ D₊(pq)`, multiplication by the trivializing value `(p/q)^n` is a
bijection `Γ(W, M̃) → Γ(W, M(nd)~)`. -/
lemma bijective_ratioModuleHom (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n c : ℤ}
    (hc : (n : ℤ) * d = c) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q)) :
    Function.Bijective
      (fun ς : ProjectiveSpectrum.Proj.moduleSections 𝒮 𝒨 W =>
        (⟨fun x => ratioFun 𝒮 n hW x • ς.1 x, ratioSMul_mem 𝒮 𝒨 hp hq hc hW ς⟩ :
          ProjectiveSpectrum.Proj.moduleSections 𝒮 (shiftedGrading 𝒨 c) W)) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun ϑ => ⟨fun x => ratioFunInv 𝒮 n hW x • ϑ.1 x,
      ratioInvSMul_mem 𝒮 𝒨 hp hq hc hW ϑ⟩, fun ς => ?_, fun ϑ => ?_⟩
  · refine Subtype.ext (funext fun x => ?_)
    change ratioFunInv 𝒮 n hW x • ratioFun 𝒮 n hW x • ς.1 x = ς.1 x
    rw [smul_smul, mul_comm, ratioFun_mul_inv, one_smul]
  · refine Subtype.ext (funext fun x => ?_)
    change ratioFun 𝒮 n hW x • ratioFunInv 𝒮 n hW x • ϑ.1 x = ϑ.1 x
    rw [smul_smul, ratioFun_mul_inv, one_smul]

/-! ### Bijectivity on the sections of the presheaf tensor product -/

/-- On every open `W ⊆ D₊(pq)`, the sheafification unit followed by the comparison map is a
bijection `M̃(W) ⊗_{𝒪(W)} 𝒪(nd)(W) → M(nd)~(W)`. -/
lemma bijective_moduleTwistMap_toTensorSheafSection
    (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n c : ℤ} (hc : (n : ℤ) * d = c)
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q)) :
    Function.Bijective (fun z => ((moduleTwistMap 𝒮 𝒨 c).val.app (op W)).hom
      (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection (AlgebraicGeometry.Proj
        𝒮).toRingedSpace
        (associatedModuleSheaf 𝒮 𝒨) (twistingSheaf 𝒮 c) (op W) z)) := by
  have hgen : (ratioEquiv 𝒮 hp hq hc hW) 1 = ratioSection 𝒮 hp hq hc hW :=
    TwistTensor.ratioEquiv_one 𝒮 hp hq hc hW
  refine bijective_of_tmul_right_generator
    (A := ProjectiveSpectrum.Proj.moduleSections 𝒮 𝒨 W) (ratioEquiv 𝒮 hp hq hc hW) _
    (fun ς => ⟨fun x => ratioFun 𝒮 n hW x • ς.1 x, ratioSMul_mem 𝒮 𝒨 hp hq hc hW ς⟩)
    (fun ς => ?_) (bijective_ratioModuleHom 𝒮 𝒨 hp hq hc hW)
  rw [hgen]
  exact Subtype.ext (funext fun x =>
    moduleTwistMap_tmul 𝒮 𝒨 c W ς (ratioSection 𝒮 hp hq hc hW) x)

/-! ### From sections over the opens of `D₊(pq)` to the stalks -/

/-- The presheaf tensor product of the associated sheaf of `M` with a twisting sheaf. -/
noncomputable abbrev modulePreTensor (a : ℤ) :
    PresheafOfModules (Stacks.SheafOfModules.TensorStalkRingedSpace.O (AlgebraicGeometry.Proj
      𝒮).toRingedSpace) :=
  (PresheafOfModules.tensorObj (O := ((AlgebraicGeometry.Proj
    𝒮).toRingedSpace).presheaf) ((associatedModuleSheaf 𝒮 𝒨).val) ((twistingSheaf 𝒮 a).val))

/-- The sheafification unit of that presheaf tensor product, read on the underlying presheaves
of abelian groups. -/
noncomputable def moduleUnitAb (a : ℤ) :=
  (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorStalkRingedSpace.O
    (AlgebraicGeometry.Proj 𝒮).toRingedSpace)).map
    (Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit (AlgebraicGeometry.Proj
      𝒮).toRingedSpace
      (modulePreTensor 𝒮 𝒨 a))

/-- The comparison map `M̃ ⊗ 𝒪(a) → M(a)~`, read on the underlying presheaves of abelian
groups. -/
noncomputable def moduleTwistAb (a : ℤ) :=
  (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorStalkRingedSpace.O
    (AlgebraicGeometry.Proj 𝒮).toRingedSpace)).map
    (moduleTwistMap 𝒮 𝒨 a).val

/-- At every point of `D₊(pq)` the comparison map is an isomorphism on stalks. -/
lemma isIso_stalkFunctor_map_moduleTwist (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n c : ℤ}
    (hc : (n : ℤ) * d = c) {x : ProjectiveSpectrum.top 𝒮}
    (hx : x ∈ ProjectiveSpectrum.basicOpen 𝒮 (p * q)) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (moduleTwistAb 𝒮 𝒨 c)) := by
  set U : Opens ↑(AlgebraicGeometry.Proj 𝒮).toRingedSpace.toPresheafedSpace :=
    ProjectiveSpectrum.basicOpen 𝒮 (p * q) with hU
  have hwhisk : IsIso (Functor.whiskerLeft (TopCat.Presheaf.imF U).op
      (moduleUnitAb 𝒮 𝒨 c ≫ moduleTwistAb 𝒮 𝒨 c)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_moduleTwistMap_toTensorSheafSection 𝒮 𝒨 hp hq hc
      (W := (TopCat.Presheaf.imF U).obj V.unop) (TwistTensor.imF_obj_le U V.unop)
  have h2 : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
      (⟨x, hx⟩ : ↥U)).map (Functor.whiskerLeft (TopCat.Presheaf.imF U).op
      (moduleUnitAb 𝒮 𝒨 c ≫ moduleTwistAb 𝒮 𝒨 c))) := inferInstance
  have h3 := (TopCat.Presheaf.isIso_stalkFunctor_map_whiskerLeft_iff U _ _
    (moduleUnitAb 𝒮 𝒨 c ≫ moduleTwistAb 𝒮 𝒨 c) ⟨x, hx⟩).mp h2
  have h4 : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (U.inclusion' ⟨x, hx⟩)).map
      (moduleUnitAb 𝒮 𝒨 c ≫ moduleTwistAb 𝒮 𝒨 c)
      = (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (U.inclusion' ⟨x, hx⟩)).map
          (moduleUnitAb 𝒮 𝒨 c) ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (U.inclusion' ⟨x, hx⟩)).map
          (moduleTwistAb 𝒮 𝒨 c) := Functor.map_comp _ _ _
  rw [h4] at h3
  have hηiso : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
      (U.inclusion' ⟨x, hx⟩)).map (moduleUnitAb 𝒮 𝒨 c)) :=
    Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMap_sheafifyUnit_isIso (AlgebraicGeometry.Proj
      𝒮).toRingedSpace _ _
  exact (@isIso_comp_left_iff _ _ _ _ _ _ _ hηiso).mp h3

/-! ### The comparison map on the invertible locus -/

/-- The comparison map is bijective on the sections over every open contained in the ratio
locus. -/
lemma bijective_moduleTwistAb_app_of_le_ratioLocus
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjShared.ratioLocus 𝒮 d)
    {n c : ℤ} (hc : (n : ℤ) * d = c) :
    Function.Bijective (ConcreteCategory.hom ((moduleTwistAb 𝒮 𝒨 c).app (op W))) := by
  refine TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective
    ((SheafOfModules.toSheaf (structureSheafRing
      (AlgebraicGeometry.Proj 𝒮).toRingedSpace)).map (moduleTwistMap 𝒮 𝒨 c)) W
    fun x hx => ?_
  obtain ⟨e', f, g, hf, hg, hfx, hgx⟩ := (ProjShared.mem_ratioLocus_iff 𝒮 d x).mp (hW hx)
  have hx' : x ∈ ProjectiveSpectrum.basicOpen 𝒮 (f * g) := fun hmul =>
    (x.isPrime.mem_or_mem hmul).elim hfx hgx
  exact (ConcreteCategory.isIso_iff_bijective _).mp
    (isIso_stalkFunctor_map_moduleTwist 𝒮 𝒨 hf hg hc hx')

/-- On an open contained in the union of the standard opens `D₊(fg)` with `deg f = deg g + d`,
the canonical map `M̃ ⊗ 𝒪(dn) → M(dn)~` restricts to an isomorphism. -/
theorem isIso_restrictFunctor_moduleTwistMap {U : (AlgebraicGeometry.Proj 𝒮).Opens}
    (hU : U ≤ ProjShared.ratioLocus 𝒮 d) (n : ℤ) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (moduleTwistMap 𝒮 𝒨 ((d : ℤ) * n))) := by
  have hpre : IsIso ((Scheme.Modules.toPresheaf U.toScheme).map
      ((Scheme.Modules.restrictFunctor U.ι).map (moduleTwistMap 𝒮 𝒨 ((d : ℤ) * n)))) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_moduleTwistAb_app_of_le_ratioLocus 𝒮 𝒨
      ((U.ι_image_le V.unop).trans hU) (mul_comm (n : ℤ) (d : ℤ))
  exact isIso_of_reflects_iso _ (Scheme.Modules.toPresheaf U.toScheme)

/-- On the largest open on which the `d`-divisible twists are invertible and their multiplication
maps are isomorphisms, the canonical comparison from the tensor product of an associated sheaf
with such a twist to the associated sheaf of the shifted module is an isomorphism, for every
graded module and every integral multiple of `d`. The hypothesis `0 < d` is not used. -/
@[stacks 01MU "comparison for associated modules"]
theorem moduleTwistMap_isIso_on_whereInvertible (d : ℕ) (_hd : 0 < d) (n : ℤ) :
    IsIso ((Scheme.Modules.restrictFunctor (whereInvertible 𝒮 d).ι).map
      (moduleTwistMap 𝒮 𝒨 ((d : ℤ) * n))) :=
  isIso_restrictFunctor_moduleTwistMap 𝒮 𝒨
    (GoodOpenClose.whereInvertible_le_ratioLocus 𝒮 d) n

end Stacks.AlgebraicGeometry.ModuleTwistIso

end
