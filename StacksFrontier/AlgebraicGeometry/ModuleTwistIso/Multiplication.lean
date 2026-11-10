module

public import StacksFrontier.AlgebraicGeometry.ModuleTwistIso.Basic

/-!
# The multiplication map `𝒪(nd) ⊗ 𝒪(m) → 𝒪(nd+m)` for an arbitrary second index

Let `S` be a graded ring, `X = Proj(S)` and `d` a natural number. Equation 01MO's
multiplication map `𝒪_X(a) ⊗_{𝒪_X} 𝒪_X(b) ⟶ 𝒪_X(a+b)` restricts to an isomorphism on every
open contained in the ratio locus `⋃ D₊(fg)`, `deg f = deg g + d`, as soon as the *first* index
is a multiple of `d`: the second index is arbitrary. This is what Tag 01MS and Tag 01MW (3)
assert, and it is strictly stronger than the form in
`StacksFrontier/AlgebraicGeometry/GoodOpenClose/Basic.lean`, where both indices are multiples of
`d` because both twists are trivialized.

The two tagged statements of Tag 01MS about the canonical maps of the section are recorded
here, for the standard open `D₊(f)` of a homogeneous element of degree `d`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleTwistIso.isIso_restrictFunctor_twistMultiplicationMap_left`:
  **the general form.** On an open contained in the ratio locus, the multiplication map
  `𝒪(dn) ⊗ 𝒪(m) ⟶ 𝒪(dn + m)` restricts to an isomorphism, for every integer `m`.
* `Stacks.AlgebraicGeometry.ModuleTwistIso.bijective_ratioMulHom`: **the arithmetic heart.** On
  an open `W ⊆ D₊(pq)` multiplication by the trivializing value `(p/q)^n` is a bijection
  `Γ(W, 𝒪(m)) → Γ(W, 𝒪(nd + m))`.
* `Stacks.AlgebraicGeometry.ModuleTwistIso.isIso_restrict_twistMultiplicationMap_basicOpen`:
  **Stacks Tag 01MS**, Equation 01MO restricted to `D₊(f)`.
* `Stacks.AlgebraicGeometry.ModuleTwistIso.isIso_restrict_moduleTwistMap_basicOpen`:
  **Stacks Tag 01MS**, Equation 01MQ restricted to `D₊(f)`, for every graded module.

## The route

The source obtains the clause for an arbitrary second index from the comparison map of
Equation 01MQ at the graded module `S(m)`, whose source is `𝒪(m) ⊗ 𝒪(nd)` — the two factors in
the other order. The symmetry of the sheaf tensor product is not available here (nothing in
this repository identifies `F ⊗ G` with `G ⊗ F` for
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`), so the proof instead runs the
module argument of `StacksFrontier/AlgebraicGeometry/ModuleTwistIso/Basic.lean` with the *left*
factor trivialized:

1. **Sections.** On an open `W ⊆ D₊(pq)` with `deg p = deg q + d` the left factor `𝒪(nd)(W)` is
   free of rank one on the trivializing section `(p/q)^n`
   (`Stacks.AlgebraicGeometry.ProjInvertibleLocus.ratioEquiv`), so the sheafification unit
   followed by the multiplication map collapses to multiplication by that section,
   `Γ(W, 𝒪(m)) → Γ(W, 𝒪(nd+m))`, by `bijective_of_tmul_left_generator` and the pointwise
   formula `Stacks.AlgebraicGeometry.TwistTensor.twistMultiplicationMap_tmul`. That
   multiplication is a bijection because `(p/q)^n` is a unit of every local ring of `D₊(pq)`:
   this is `bijective_ratioModuleHom` at the graded module `S(m)`, whose values at a
   point lie in the same local module as those of `𝒪(nd+m)`.
2. **Stalks, then sections globally.** Verbatim as for the two existing maps: the composite is a
   stalkwise isomorphism on `D₊(pq)`, the sheafification unit cancels, every point of an open
   of the ratio locus lies in some `D₊(fg)`, and both sides are sheaves.

Tag 01MS's hypothesis `f ∈ S_d` gives `D₊(f) ≤ ratioLocus 𝒮 d` by
`Stacks.AlgebraicGeometry.ProjShared.basicOpen_le_ratioLocus`, so both tagged statements are
instances of the general form; the positivity `0 < d` of the source is not used.

## Implementation notes

* The target of step 1 is `Γ(W, 𝒪(nd+m))`, whose grading is `twistGrading 𝒮 (nd+m)`, while
  `bijective_ratioModuleHom` produces sections of the *shifted* grading
  `shiftedGrading (twistGrading 𝒮 m) (nd)`. The two gradings are equal but not definitionally
  equal, and `moduleSections` takes a decomposition and a graded action of the grading as
  instance arguments, so the equality cannot be rewritten inside it: the motive is not type
  correct. `mem_moduleSections_congr` crosses that gap once, by `subst`, using that the
  local-fraction predicate mentions the grading only through membership of its pieces.
* `smul_eq_mul` reconciles the action of the local ring on `LocalizedModule 𝔭_x S` with the
  multiplication of `Localization 𝔭_x`: the multiplication map's pointwise formula is stated
  with the product and the module argument with the action.

## References

* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 01MQ](https://stacks.math.columbia.edu/tag/01MQ)
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

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-! ### A rank-one free left factor recognizes isomorphisms out of a tensor product -/

section Abstract

variable {R A B C : Type*} [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]

/-- A map out of `A ⊗ B` is bijective as soon as `A` is free of rank one and tensoring with its
generator is a bijection `B → C`. This is the mirror image of
`bijective_of_tmul_right_generator`, with the same reason for taking the witnessing bijection as
a separate argument: the two sides are stated with different, definitionally equal, spellings of
the ring of sections. -/
lemma bijective_of_tmul_left_generator (eA : R ≃ₗ[R] A) (h : A ⊗[R] B → C) (g : B → C)
    (hg : ∀ y : B, h (eA 1 ⊗ₜ[R] y) = g y) (hbij : Function.Bijective g) :
    Function.Bijective h := by
  set ψ : B ≃ₗ[R] A ⊗[R] B :=
    (TensorProduct.lid R B).symm.trans (TensorProduct.congr eA (LinearEquiv.refl R B)) with hψ
  have hψ_apply : ∀ y : B, ψ y = eA 1 ⊗ₜ[R] y := by
    intro y
    rw [hψ]
    simp [TensorProduct.congr_tmul]
  have hcomp : (h : A ⊗[R] B → C) = g ∘ (ψ.symm : A ⊗[R] B → B) := by
    funext z
    have hz : ψ (ψ.symm z) = z := ψ.apply_symm_apply z
    simp only [Function.comp_apply]
    rw [← hg, ← hψ_apply, hz]
  rw [hcomp]
  exact hbij.comp ψ.symm.bijective

end Abstract

/-! ### The twist of a twist, and the sections it cuts out -/

omit [GradedRing 𝒮] in
/-- The twist of the twist is the twist by the sum: the graded module `S(m)(c)` has degree-`i`
piece `S_{i + c + m}`, which is the degree-`i` piece of `S(m + c)`. -/
theorem shiftedGrading_twistGrading (m c : ℤ) :
    shiftedGrading (twistGrading (S := S) 𝒮 m) c = twistGrading (S := S) 𝒮 (m + c) := by
  funext i
  change integerGrading (S := S) 𝒮 (i + c + m) = integerGrading (S := S) 𝒮 (i + (m + c))
  exact congrArg (integerGrading (S := S) 𝒮) (by ring)

/-- Two equal gradings cut out the same sections. The predicate defining `moduleSections` is the
local existence of a homogeneous fraction, which mentions the grading only through membership of
its pieces; the decomposition and the graded action, which `moduleSections` carries as instance
arguments, do not enter. Those instance arguments are why the equality of the gradings cannot be
rewritten inside `moduleSections` directly. -/
lemma mem_moduleSections_congr {M : Type u} [AddCommGroup M] [Module S M] {τ : Type t}
    [SetLike τ M] [AddSubgroupClass τ M]
    (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨]
    (𝒩 : ℤ → τ) [DirectSum.Decomposition 𝒩] [SetLike.GradedSMul 𝒮 𝒩] (h : 𝒨 = 𝒩)
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (a : ∀ x : W, ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x.1) :
    a ∈ ProjectiveSpectrum.Proj.moduleSections 𝒮 𝒨 W ↔
      a ∈ ProjectiveSpectrum.Proj.moduleSections 𝒮 𝒩 W := by
  subst h
  exact Iff.rfl

/-! ### The arithmetic heart: multiplying an arbitrary twist by the trivializing ratio -/

section Local

variable {p q : S} {e d : ℕ}

omit [GradedRing 𝒮] in
/-- The identification of the two spellings of the grading of `𝒪(nd + m)` that the arithmetic
heart is read through. -/
private theorem shiftedGrading_twistGrading' (b c : ℤ) :
    shiftedGrading (twistGrading (S := S) 𝒮 b) c = twistGrading (S := S) 𝒮 (c + b) :=
  (shiftedGrading_twistGrading 𝒮 b c).trans
    (congrArg (twistGrading (S := S) 𝒮) (add_comm b c))

/-- Multiplying a section of `𝒪(m)` by the trivializing value `(p/q)^n` gives a section of
`𝒪(nd + m)`: this is the degree bookkeeping of `ratioSMul_mem` at the graded module `S(m)`,
read through the identification of `S(m)(nd)` with `S(nd + m)`. -/
lemma ratioMul_mem (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n c : ℤ} (hc : (n : ℤ) * d = c)
    (b : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q))
    (ϑ : ProjectiveSpectrum.Proj.moduleSections 𝒮 (twistGrading (S := S) 𝒮 b) W) :
    (fun x => ratioFun 𝒮 n hW x • ϑ.1 x) ∈
      ProjectiveSpectrum.Proj.moduleSections 𝒮 (twistGrading (S := S) 𝒮 (c + b)) W :=
  (mem_moduleSections_congr 𝒮 (shiftedGrading (twistGrading (S := S) 𝒮 b) c)
      (twistGrading (S := S) 𝒮 (c + b)) (shiftedGrading_twistGrading' 𝒮 b c) _).mp
    (ratioSMul_mem 𝒮 (twistGrading (S := S) 𝒮 b) hp hq hc hW ϑ)

/-- Multiplying a section of `𝒪(nd + m)` by the inverse value `(q/p)^n` gives a section of
`𝒪(m)`: the same bookkeeping read backwards. -/
lemma ratioInvMul_mem (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n c : ℤ} (hc : (n : ℤ) * d = c)
    (b : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q))
    (ϑ : ProjectiveSpectrum.Proj.moduleSections 𝒮 (twistGrading (S := S) 𝒮 (c + b)) W) :
    (fun x => ratioFunInv 𝒮 n hW x • ϑ.1 x) ∈
      ProjectiveSpectrum.Proj.moduleSections 𝒮 (twistGrading (S := S) 𝒮 b) W :=
  ratioInvSMul_mem 𝒮 (twistGrading (S := S) 𝒮 b) hp hq hc hW
    ⟨ϑ.1, (mem_moduleSections_congr 𝒮 (twistGrading (S := S) 𝒮 (c + b))
      (shiftedGrading (twistGrading (S := S) 𝒮 b) c)
      (shiftedGrading_twistGrading' 𝒮 b c).symm _).mp ϑ.2⟩

/-- **The arithmetic heart.** On every open `W ⊆ D₊(pq)`, multiplication by the trivializing
value `(p/q)^n` is a bijection `Γ(W, 𝒪(m)) → Γ(W, 𝒪(nd + m))`, for an arbitrary integer `m`:
the ratio is a unit of every local ring there, and both sides take their values in the same
local module, so the inverse is multiplication by `(q/p)^n`. -/
lemma bijective_ratioMulHom (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n c : ℤ}
    (hc : (n : ℤ) * d = c) (b : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q)) :
    Function.Bijective
      (fun ϑ : ProjectiveSpectrum.Proj.moduleSections 𝒮 (twistGrading (S := S) 𝒮 b) W =>
        (⟨fun x => ratioFun 𝒮 n hW x • ϑ.1 x, ratioMul_mem 𝒮 hp hq hc b hW ϑ⟩ :
          ProjectiveSpectrum.Proj.moduleSections 𝒮
            (twistGrading (S := S) 𝒮 (c + b)) W)) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun ϑ => ⟨fun x => ratioFunInv 𝒮 n hW x • ϑ.1 x, ratioInvMul_mem 𝒮 hp hq hc b hW ϑ⟩,
      fun ς => ?_, fun ϑ => ?_⟩
  · refine Subtype.ext (funext fun x => ?_)
    change ratioFunInv 𝒮 n hW x • ratioFun 𝒮 n hW x • ς.1 x = ς.1 x
    rw [smul_smul, mul_comm, ratioFun_mul_inv, one_smul]
  · refine Subtype.ext (funext fun x => ?_)
    change ratioFun 𝒮 n hW x • ratioFunInv 𝒮 n hW x • ϑ.1 x = ϑ.1 x
    rw [smul_smul, ratioFun_mul_inv, one_smul]

/-! ### Bijectivity on the sections of the presheaf tensor product -/

/-- On every open `W ⊆ D₊(pq)`, the sheafification unit followed by the multiplication map is a
bijection `𝒪(nd)(W) ⊗_{𝒪(W)} 𝒪(m)(W) → 𝒪(nd+m)(W)`. The left factor is free of rank one on the
trivializing section, so the tensor product collapses to `𝒪(m)(W)` and the induced map is
multiplication by that section, which is `bijective_ratioMulHom`. -/
lemma bijective_twistMultiplicationMap_toTensorSheafSection_left
    (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n c : ℤ} (hc : (n : ℤ) * d = c) (b : ℤ)
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 (p * q)) :
    Function.Bijective (fun z => ((twistMultiplicationMap 𝒮 c b).val.app (op W)).hom
      (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection (AlgebraicGeometry.Proj
        𝒮).toRingedSpace
        (twistingSheaf 𝒮 c) (twistingSheaf 𝒮 b) (op W) z)) := by
  have hgen : (ratioEquiv 𝒮 hp hq hc hW) 1 = ratioSection 𝒮 hp hq hc hW :=
    TwistTensor.ratioEquiv_one 𝒮 hp hq hc hW
  refine bijective_of_tmul_left_generator
    (B := ProjectiveSpectrum.Proj.moduleSections 𝒮 (twistGrading (S := S) 𝒮 b) W)
    (ratioEquiv 𝒮 hp hq hc hW) _
    (fun ϑ => ⟨fun x => ratioFun 𝒮 n hW x • ϑ.1 x, ratioMul_mem 𝒮 hp hq hc b hW ϑ⟩)
    (fun ϑ => ?_) (bijective_ratioMulHom 𝒮 hp hq hc b hW)
  rw [hgen]
  refine Subtype.ext (funext fun x => ?_)
  refine (TwistTensor.twistMultiplicationMap_tmul 𝒮 c b W
    (ratioSection 𝒮 hp hq hc hW) ϑ x).trans ?_
  exact (smul_eq_mul (ratioFun 𝒮 n hW x) (ϑ.1 x)).symm

/-! ### From sections over the opens of `D₊(pq)` to the stalks -/

/-- **The stalk step.** At every point of `D₊(pq)` the multiplication map `𝒪(nd) ⊗ 𝒪(m) →
𝒪(nd+m)` is an isomorphism on stalks. Its composite with the sheafification unit restricts to an
isomorphism of abelian presheaves on the space `D₊(pq)`, hence is a stalkwise isomorphism there;
and the unit is a stalkwise isomorphism for free. -/
lemma isIso_stalkFunctor_map_twistMultiplication_left
    (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n c : ℤ} (hc : (n : ℤ) * d = c) (b : ℤ)
    {x : ProjectiveSpectrum.top 𝒮}
    (hx : x ∈ ProjectiveSpectrum.basicOpen 𝒮 (p * q)) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (TwistTensor.twistMultAb 𝒮 c b)) := by
  set U : Opens ↑(AlgebraicGeometry.Proj 𝒮).toRingedSpace.toPresheafedSpace :=
    ProjectiveSpectrum.basicOpen 𝒮 (p * q) with hU
  have hwhisk : IsIso (Functor.whiskerLeft (TopCat.Presheaf.imF U).op
      (TwistTensor.twistUnitAb 𝒮 c b ≫ TwistTensor.twistMultAb 𝒮 c b)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_twistMultiplicationMap_toTensorSheafSection_left 𝒮 hp hq hc b
      (W := (TopCat.Presheaf.imF U).obj V.unop) (TwistTensor.imF_obj_le U V.unop)
  have h2 : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
      (⟨x, hx⟩ : ↥U)).map (Functor.whiskerLeft (TopCat.Presheaf.imF U).op
      (TwistTensor.twistUnitAb 𝒮 c b ≫ TwistTensor.twistMultAb 𝒮 c b))) := inferInstance
  have h3 := (TopCat.Presheaf.isIso_stalkFunctor_map_whiskerLeft_iff U _ _
    (TwistTensor.twistUnitAb 𝒮 c b ≫ TwistTensor.twistMultAb 𝒮 c b) ⟨x, hx⟩).mp h2
  have h4 : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (U.inclusion' ⟨x, hx⟩)).map
      (TwistTensor.twistUnitAb 𝒮 c b ≫ TwistTensor.twistMultAb 𝒮 c b)
      = (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (U.inclusion' ⟨x, hx⟩)).map
          (TwistTensor.twistUnitAb 𝒮 c b) ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (U.inclusion' ⟨x, hx⟩)).map
          (TwistTensor.twistMultAb 𝒮 c b) := Functor.map_comp _ _ _
  rw [h4] at h3
  have hηiso : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
      (U.inclusion' ⟨x, hx⟩)).map (TwistTensor.twistUnitAb 𝒮 c b)) :=
    Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMap_sheafifyUnit_isIso (AlgebraicGeometry.Proj
      𝒮).toRingedSpace _ _
  exact (@isIso_comp_left_iff _ _ _ _ _ _ _ hηiso).mp h3

/-- The multiplication map `𝒪(nd) ⊗ 𝒪(m) → 𝒪(nd+m)` is bijective on the sections over every
open contained in the ratio locus: it is a stalk isomorphism at every point of such an open, and
both sides are sheaves. -/
lemma bijective_twistMultAb_app_of_le_ratioLocus_left
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjShared.ratioLocus 𝒮 d)
    {n c : ℤ} (hc : (n : ℤ) * d = c) (b : ℤ) :
    Function.Bijective (ConcreteCategory.hom ((TwistTensor.twistMultAb 𝒮 c b).app (op W))) := by
  refine TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective
    ((SheafOfModules.toSheaf (structureSheafRing
      (AlgebraicGeometry.Proj 𝒮).toRingedSpace)).map (twistMultiplicationMap 𝒮 c b)) W
    fun x hx => ?_
  obtain ⟨e', f, g, hf, hg, hfx, hgx⟩ := (ProjShared.mem_ratioLocus_iff 𝒮 d x).mp (hW hx)
  have hx' : x ∈ ProjectiveSpectrum.basicOpen 𝒮 (f * g) := fun hmul =>
    (x.isPrime.mem_or_mem hmul).elim hfx hgx
  exact (ConcreteCategory.isIso_iff_bijective _).mp
    (isIso_stalkFunctor_map_twistMultiplication_left 𝒮 hf hg hc b hx')

/-- **Equation 01MO with one arbitrary index, for every open of the ratio locus.** On an open
contained in the union of the standard opens `D₊(fg)` with `deg f = deg g + d`, the
multiplication map `𝒪(dn) ⊗ 𝒪(m) ⟶ 𝒪(dn + m)` restricts to an isomorphism, for every integer
`n` and *every* integer `m` — only the first index is required to be a multiple of `d`. -/
theorem isIso_restrictFunctor_twistMultiplicationMap_left
    {U : (AlgebraicGeometry.Proj 𝒮).Opens} (hU : U ≤ ProjShared.ratioLocus 𝒮 d) (n m : ℤ) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (twistMultiplicationMap 𝒮 ((d : ℤ) * n) m)) := by
  have hpre : IsIso ((Scheme.Modules.toPresheaf U.toScheme).map
      ((Scheme.Modules.restrictFunctor U.ι).map
        (twistMultiplicationMap 𝒮 ((d : ℤ) * n) m))) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_twistMultAb_app_of_le_ratioLocus_left 𝒮
      ((U.ι_image_le V.unop).trans hU) (mul_comm (n : ℤ) (d : ℤ)) m
  exact isIso_of_reflects_iso _ (Scheme.Modules.toPresheaf U.toScheme)

end Local

/-! ### Stacks Tag 01MS: the canonical maps on a standard open -/

/-- **Stacks Tag 01MS.** Let `f` be homogeneous of degree `d`. Then for all integers `n` and `m`
the multiplication map of Equation 01MO,

`𝒪_X(nd)|_{D₊(f)} ⊗_{𝒪_{D₊(f)}} 𝒪_X(m)|_{D₊(f)} ⟶ 𝒪_X(nd+m)|_{D₊(f)}`,

is an isomorphism. The second index is arbitrary, as in the source; the positivity of `d` is not
used. -/
theorem isIso_restrict_twistMultiplicationMap_basicOpen {f : S} {d : ℕ} (hf : f ∈ 𝒮 d)
    (n m : ℤ) :
    IsIso ((Scheme.Modules.restrictFunctor (AlgebraicGeometry.Proj.basicOpen 𝒮 f).ι).map
      (twistMultiplicationMap 𝒮 ((d : ℤ) * n) m)) :=
  isIso_restrictFunctor_twistMultiplicationMap_left 𝒮
    (ProjShared.basicOpen_le_ratioLocus 𝒮 (dvd_refl d) hf) n m

/-- **Stacks Tag 01MS.** Let `f` be homogeneous of degree `d` and let `M` be a graded
`S`-module. Then for every integer `n` the comparison map of Equation 01MQ,

`M̃|_{D₊(f)} ⊗_{𝒪_{D₊(f)}} 𝒪_X(nd)|_{D₊(f)} ⟶ M(nd)~|_{D₊(f)}`,

is an isomorphism. -/
theorem isIso_restrict_moduleTwistMap_basicOpen {M : Type u} [AddCommGroup M] [Module S M]
    {τ : Type t} [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ)
    [DirectSum.Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨] {f : S} {d : ℕ} (hf : f ∈ 𝒮 d)
    (n : ℤ) :
    IsIso ((Scheme.Modules.restrictFunctor (AlgebraicGeometry.Proj.basicOpen 𝒮 f).ι).map
      (moduleTwistMap 𝒮 𝒨 ((d : ℤ) * n))) :=
  isIso_restrictFunctor_moduleTwistMap 𝒮 𝒨
    (ProjShared.basicOpen_le_ratioLocus 𝒮 (dvd_refl d) hf) n

end Stacks.AlgebraicGeometry.ModuleTwistIso

end
