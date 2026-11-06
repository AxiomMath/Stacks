module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentKernelImageCokernel
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentLocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedFlatFppfRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsEssentialImage

/-!
# The image of a map of quasi-coherent modules need not be quasi-coherent

**Stacks 0GQL** part (2) asserts that for a map `φ : 𝓕 → 𝓖` of quasi-coherent modules on an
algebraic stack `𝒳`, the image `Im(φ)` computed in `Mod(𝒪_𝒳)` is quasi-coherent and is the image
of `φ` in `QCoh(𝒪_𝒳)`. The first half is false, and this file proves that it is: for
`𝒳 = Spec ℤ` and `φ = 2 : 𝒪 → 𝒪`, the image computed in `Mod(𝒪_𝒳)` is not quasi-coherent
(`AlgebraicGeometry.Stack.ImageCounterexample.not_forall_isQuasicoherentOnSite_image`). This is
the reason the part is registered in a corrected form, in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorCanonical`: the image lies in
`LQCoh^fbc(𝒪_𝒳)`, and the coherator of it is the image in `QCoh(𝒪_𝒳)`.

## The argument

Write `I ⊆ 𝒪` for the image of `2` computed in `Mod(𝒪_𝒳)`, on the big fppf site of `Spec ℤ`.

* `I` has no nonzero sections over `Spec 𝔽₂`: a section is, fppf locally, the image of a
  function `t`, so its image in `𝒪` is locally `t + t`, which vanishes on every `𝔽₂`-scheme; the
  inclusion `I ⟶ 𝒪` is injective on sections
  (`AlgebraicGeometry.Stack.ImageCounterexample.imageModule_fiber_eq_zero`).
* If `I` were quasi-coherent it would be cartesian along `Spec 𝔽₂ ⟶ Spec ℤ`
  (`AlgebraicGeometry.FibredSite.isIso_restrictionBaseChange_of_isQuasicoherentOnSite`), so
  `𝔽₂ ⊗_ℤ I(Spec ℤ) = I(Spec 𝔽₂) = 0`, and every `ℤ`-linear map from `I(Spec ℤ)` to `𝔽₂` would
  vanish.
* But the inclusion `I(Spec ℤ) ⟶ ℤ` takes values in the even integers, since its reduction mod
  `2` is such a linear map; halving and then reducing mod `2` is then a linear map
  `I(Spec ℤ) → 𝔽₂`, and it sends the image of `1`, whose image in `ℤ` is `2`, to `1 ≠ 0`.

## References

* [Stacks Project, Tag 0GQL](https://stacks.math.columbia.edu/tag/0GQL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack.ImageCounterexample

/-- The ring `ℤ`, in the universe of the schemes. -/
abbrev intRing : CommRingCat.{u} := .of (ULift.{u} ℤ)

/-- The field `𝔽₂`, in the universe of the schemes. -/
abbrev fieldTwo : CommRingCat.{u} := .of (ULift.{u} (ZMod 2))

/-- The reduction map `ℤ → 𝔽₂`. -/
def reduction : intRing.{u} ⟶ fieldTwo.{u} :=
  CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    ((Int.castRingHom (ZMod 2)).comp ULift.ringEquiv.toRingHom))

/-- `Spec 𝔽₂ ⟶ Spec ℤ`. -/
def toBase : Spec fieldTwo.{u} ⟶ Spec intRing.{u} := Spec.map reduction

/-- A big fppf site containing `Spec ℤ` and `Spec 𝔽₂`. -/
theorem exists_site : ∃ B : BigFppfSite.{u},
    B.Contains (Spec intRing.{u}) ∧ B.Contains (Spec fieldTwo.{u}) := by
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing ({Spec intRing.{u}, Spec fieldTwo.{u}} :
    Set Scheme.{u})
  exact ⟨B, hB _ (by simp), hB _ (by simp)⟩

/-- The chosen site. -/
def site : BigFppfSite.{u} := exists_site.{u}.choose

/-- The chosen site contains `Spec ℤ`. -/
theorem site_contains_base : site.{u}.Contains (Spec intRing.{u}) := exists_site.choose_spec.1

/-- The chosen site contains `Spec 𝔽₂`. -/
theorem site_contains_fiber : site.{u}.Contains (Spec fieldTwo.{u}) := exists_site.choose_spec.2

/-- `Spec ℤ`, as an object of the big fppf site over itself. -/
abbrev baseObj : BigFppfOver site.{u} (Spec intRing.{u}) site_contains_base :=
  Over.mk (𝟙 _)

/-- `Spec 𝔽₂ ⟶ Spec ℤ`, as an object of the big fppf site over `Spec ℤ`. -/
abbrev fiberObj : BigFppfOver site.{u} (Spec intRing.{u}) site_contains_base :=
  Over.mk (site.inclusion.preimage (X := site.obj site_contains_fiber)
    (Y := site.obj site_contains_base) toBase)

/-- The algebraic stack `Spec ℤ` over itself. -/
def stack : AlgebraicStacks.{u, w} site.{u} (Spec intRing.{u}) site_contains_base :=
  schemeStack.{u, w} _ _ _ baseObj

/-- `Spec ℤ` as an object of the stack. -/
abbrev yZ : (stack.{u, w}).val.val.obj := Over.mk (𝟙 baseObj)

/-- `Spec 𝔽₂` as an object of the stack. -/
abbrev yF : (stack.{u, w}).val.val.obj :=
  Over.mk (Over.homMk (site.inclusion.preimage (X := site.obj site_contains_fiber)
    (Y := site.obj site_contains_base) toBase) (by simp) : fiberObj ⟶ baseObj)

/-- The arrow `Spec 𝔽₂ ⟶ Spec ℤ` of the stack. -/
abbrev arrow : yF.{u, w} ⟶ yZ.{u, w} := Over.homMk (Over.homMk (site.inclusion.preimage
  (X := site.obj site_contains_fiber) (Y := site.obj site_contains_base) toBase) (by simp))
    (by simp)

section Image

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat

/-- The structure sheaf of rings of the fppf site of the stack. -/
abbrev ringSheaf := FibredSite.ringStructureSheafCore site.{u} (Spec intRing.{u})
  site_contains_base (stack.{u, w}).val.val.p (stack.{u, w}).val.isFiberedInGroupoids .fppf

/-- Multiplication by `2` on `𝒪`. -/
def two : SheafOfModules.unit ringSheaf.{u, w} ⟶ SheafOfModules.unit ringSheaf.{u, w} :=
  𝟙 _ + 𝟙 _

/-- `2` acts on sections by doubling. -/
theorem two_app (Y : (stack.{u, w}).val.val.obj)
    (t : (SheafOfModules.unit ringSheaf.{u, w}).val.obj (op Y)) :
    (two.{u, w}).val.app (op Y) t = t + t := rfl

/-- `2 = 0` in the ring of functions on `Spec 𝔽₂`. -/
theorem two_eq_zero_fiber :
    (1 + 1 : ringSheaf.{u, w}.obj.obj (op yF.{u, w})) = 0 := by
  show (1 + 1 : Γ(Spec fieldTwo.{u}, ⊤)) = 0
  apply (Scheme.ΓSpecIso fieldTwo.{u}).commRingCatIsoToRingEquiv.injective
  rw [map_add, map_one, map_zero]
  exact ULift.ext (by decide)

/-- `Γ(Spec 𝔽₂)` is not the zero ring. -/
theorem one_ne_zero_fiber : (1 : ringSheaf.{u, w}.obj.obj (op yF.{u, w})) ≠ 0 := by
  show (1 : Γ(Spec fieldTwo.{u}, ⊤)) ≠ 0
  intro h
  have := congrArg (Scheme.ΓSpecIso fieldTwo.{u}).commRingCatIsoToRingEquiv h
  rw [map_one, map_zero] at this
  exact absurd (congrArg ULift.down this) (by decide)

/-- The identification of `Γ(Spec ℤ)` with `ℤ`. -/
def intEquiv : ringSheaf.{u, w}.obj.obj (op yZ.{u, w}) ≃+* ℤ :=
  (Scheme.ΓSpecIso intRing.{u}).commRingCatIsoToRingEquiv.trans ULift.ringEquiv

/-- Every function on `Spec ℤ` is even or odd. -/
theorem even_or_odd_base (k : ringSheaf.{u, w}.obj.obj (op yZ.{u, w})) :
    (∃ a, k = (1 + 1) * a) ∨ ∃ a, k = 1 + (1 + 1) * a := by
  rcases Int.even_or_odd (intEquiv.{u, w} k) with ⟨a, ha⟩ | ⟨a, ha⟩
  · refine Or.inl ⟨intEquiv.symm a, intEquiv.injective ?_⟩
    rw [ha, map_mul, map_add, map_one, RingEquiv.apply_symm_apply]
    ring
  · refine Or.inr ⟨intEquiv.symm a, intEquiv.injective ?_⟩
    rw [ha, map_add, map_mul, map_add, map_one, RingEquiv.apply_symm_apply]
    ring

/-- `2` is a non-zero-divisor on `Spec ℤ`. -/
theorem cancel_two_base {a b : ringSheaf.{u, w}.obj.obj (op yZ.{u, w})}
    (h : (1 + 1) * a = (1 + 1) * b) : a = b := by
  apply intEquiv.{u, w}.injective
  have := congrArg intEquiv.{u, w} h
  simp only [map_mul, map_add, map_one] at this
  omega

/-- In a ring in which `1 + 1 = 0`, every element is its own negative. -/
theorem add_self_eq_zero_of_one_add_one {A : Type*} [Ring A] (h : (1 + 1 : A) = 0) (t : A) :
    t + t = 0 := by
  rw [← one_mul t, ← add_mul, h, zero_mul]

/-- The image of `2 : 𝒪 ⟶ 𝒪` computed in `Mod(𝒪)`. -/
abbrev imageModule : SheafOfModules ringSheaf.{u, w} := Abelian.image two.{u, w}

/-- The projection `𝒪 ⟶ Im(2)`. -/
abbrev imageπ : SheafOfModules.unit ringSheaf.{u, w} ⟶ imageModule.{u, w} :=
  Abelian.factorThruImage two.{u, w}

/-- The inclusion `Im(2) ⟶ 𝒪`. -/
abbrev imageι : imageModule.{u, w} ⟶ SheafOfModules.unit ringSheaf.{u, w} :=
  Abelian.image.ι two.{u, w}

/-- The composite `𝒪 ⟶ Im(2) ⟶ 𝒪` doubles sections. -/
theorem imageπ_imageι_app (Y : (stack.{u, w}).val.val.obj)
    (t : (SheafOfModules.unit ringSheaf.{u, w}).val.obj (op Y)) :
    imageι.val.app (op Y) (imageπ.val.app (op Y) t) = t + t := by
  simpa only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    two_app] using congrArg (fun φ => φ.val.app (op Y) t) (Abelian.image.fac two.{u, w})

/-- **The image of `2` has no nonzero sections over `Spec 𝔽₂`.** A section is locally in the
image of `𝒪 ⟶ Im(2)`, so its image in `𝒪` is locally of the form `t + t`, which vanishes on every
`𝔽₂`-scheme; the inclusion into `𝒪` is injective. -/
theorem imageModule_fiber_eq_zero (s : (imageModule.{u, w}).val.obj (op yF.{u, w})) : s = 0 := by
  have := Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi imageπ.{u, w}
  have hmem := Presheaf.imageSieve_mem
    (BigFppfOver.associatedTopology _ _ _ (stack.{u, w}).val.val.p .fppf)
    ((PresheafOfModules.toPresheaf _).map imageπ.{u, w}.val) (U := op yF.{u, w}) s
  have hO := Stacks.SheafOfModules.ChangeOfRings.isSheafOfTypes_of_isSheaf _
    (SheafOfModules.unit ringSheaf.{u, w}).isSheaf
  have key : imageι.val.app (op yF.{u, w}) s = 0 := by
    refine (hO _ hmem).isSeparatedFor.ext ?_
    rintro Z g ⟨t, ht⟩
    show (SheafOfModules.unit ringSheaf.{u, w}).val.map g.op (imageι.val.app _ s) =
      (SheafOfModules.unit ringSheaf.{u, w}).val.map g.op 0
    rw [map_zero, ← PresheafOfModules.naturality_apply]
    show imageι.val.app (op Z) ((imageModule.{u, w}).val.map g.op s) = 0
    rw [← show imageπ.val.app (op Z) t = (imageModule.{u, w}).val.map g.op s from ht]
    refine (imageπ_imageι_app Z t).trans ?_
    have h2 : (1 + 1 : ringSheaf.{u, w}.obj.obj (op Z)) = 0 := by
      have := congrArg (ringSheaf.{u, w}.obj.map g.op).hom two_eq_zero_fiber.{u, w}
      rwa [map_add, map_one, map_zero] at this
    exact add_self_eq_zero_of_one_add_one h2 (t : ringSheaf.{u, w}.obj.obj (op Z))
  exact Stacks.SheafOfModules.injective_app_of_mono (φ := imageι.{u, w}) (op yF.{u, w})
    (key.trans (map_zero _).symm)

open scoped ChangeOfRings in
/-- A linear map into the restriction of scalars of a ring vanishes as soon as the extension of
scalars of its source is zero: it factors through that extension. -/
theorem eq_zero_of_subsingleton_extendScalars {A B : CommRingCat.{u}} (f : A ⟶ B)
    (M : ModuleCat.{u} A) (hM : Subsingleton ((ModuleCat.extendScalars f.hom).obj M))
    (ψ : M ⟶ (ModuleCat.restrictScalars f.hom).obj (ModuleCat.of B B)) (b : M) : ψ b = 0 := by
  let adj := ModuleCat.extendRestrictScalarsAdj f.hom
  have h : ((adj.homEquiv _ _).symm ψ) ((1 : B) ⊗ₜ[A, f.hom] b) = ψ b := by
    rw [Adjunction.homEquiv_counit]
    show (adj.counit.app _) ((ModuleCat.extendScalars f.hom).map ψ ((1 : B) ⊗ₜ[A, f.hom] b)) = _
    rw [ModuleCat.ExtendScalars.map_tmul]
    exact ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul f.hom _ _
  rw [← h, show ((1 : B) ⊗ₜ[A, f.hom] b : (ModuleCat.extendScalars f.hom).obj M) = 0 from
    hM.elim _ _]
  exact ((adj.homEquiv _ _).symm ψ).hom.map_zero

/-- `AlgebraicGeometry.Stack.ImageCounterexample.eq_zero_of_subsingleton_extendScalars` for a
function which is additive and semilinear along `f`. -/
theorem eq_zero_of_subsingleton_extendScalars_of_semilinear {A B : CommRingCat.{u}} (f : A ⟶ B)
    (M : ModuleCat.{u} A) (hM : Subsingleton ((ModuleCat.extendScalars f.hom).obj M))
    (lam : M → B) (hadd : ∀ x y, lam (x + y) = lam x + lam y)
    (hsmul : ∀ (r : A) (x : M), lam (r • x) = f.hom r * lam x) (b : M) : lam b = 0 :=
  eq_zero_of_subsingleton_extendScalars f M hM
    (ModuleCat.ofHom (X := M) (Y := (ModuleCat.restrictScalars f.hom).obj (ModuleCat.of B B))
      { toFun := lam
        map_add' := hadd
        map_smul' := fun r x => (hsmul r x).trans
          (ModuleCat.restrictScalars.smul_def' (M := ModuleCat.of B B) f.hom r (lam x)).symm })
    b

/-- The commutative structure presheaf of the fppf site of the stack. -/
abbrev commRingPresheaf := (FibredSite.structureSheaf site.{u} (Spec intRing.{u})
  site_contains_base (stack.{u, w}).val.val.p (stack.{u, w}).val.isFiberedInGroupoids .fppf).obj

/-- The image of `2` is cartesian along `Spec 𝔽₂ ⟶ Spec ℤ` if it is quasi-coherent, so its
extension of scalars from `Spec ℤ` to `Spec 𝔽₂` vanishes. -/
theorem subsingleton_extendScalars_of_isQuasicoherentOnSite
    (hQC : (imageModule.{u, w}).IsQuasicoherentOnSite) :
    Subsingleton ((ModuleCat.extendScalars (commRingPresheaf.{u, w}.map arrow.{u, w}.op).hom).obj
      ((imageModule.{u, w}).val.obj (op yZ.{u, w}))) := by
  have hZ : IsAffine ((BigFppfOver.toScheme _ _ _).obj ((stack.{u, w}).val.val.p.obj yZ.{u, w})) :=
    inferInstanceAs (IsAffine (Spec intRing.{u}))
  have hF : IsAffine ((BigFppfOver.toScheme _ _ _).obj ((stack.{u, w}).val.val.p.obj yF.{u, w})) :=
    inferInstanceAs (IsAffine (Spec fieldTwo.{u}))
  have hcart := FibredSite.isIso_restrictionBaseChange_of_isQuasicoherentOnSite
    (imageModule.{u, w}) hQC arrow.{u, w} hF hZ
  rw [ConcreteCategory.isIso_iff_bijective] at hcart
  exact ⟨fun a b => hcart.1 ((imageModule_fiber_eq_zero _).trans
    (imageModule_fiber_eq_zero _).symm)⟩

/-- **The image of `2 : 𝒪 ⟶ 𝒪` computed in `Mod(𝒪)` is not quasi-coherent.** -/
theorem not_isQuasicoherentOnSite_imageModule :
    ¬ (imageModule.{u, w}).IsQuasicoherentOnSite := by
  intro hQC
  have hsub := subsingleton_extendScalars_of_isQuasicoherentOnSite hQC
  let f := commRingPresheaf.{u, w}.map arrow.{u, w}.op
  let φ : ringSheaf.{u, w}.obj.obj (op yZ.{u, w}) →+* ringSheaf.{u, w}.obj.obj (op yF.{u, w}) :=
    f.hom
  let m : (imageModule.{u, w}).val.obj (op yZ.{u, w}) → ringSheaf.{u, w}.obj.obj (op yZ.{u, w}) :=
    fun b => imageι.val.app (op yZ) b
  have hm_add : ∀ b b', m (b + b') = m b + m b' := fun b b' =>
    (imageι.{u, w}.val.app (op yZ.{u, w})).hom.map_add b b'
  have hm_smul : ∀ (r : ringSheaf.{u, w}.obj.obj (op yZ.{u, w})) b, m (r • b) = r * m b :=
    fun r b => (imageι.{u, w}.val.app (op yZ.{u, w})).hom.map_smul r b
  -- the reduction of every additive, semilinear function `M → 𝒪(Spec ℤ)` vanishes
  have hz : ∀ g : (imageModule.{u, w}).val.obj (op yZ.{u, w}) → ringSheaf.{u, w}.obj.obj
      (op yZ.{u, w}), (∀ x y, g (x + y) = g x + g y) → (∀ r x, g (r • x) = r * g x) →
        ∀ b, φ (g b) = 0 := fun g hadd hsmul =>
    eq_zero_of_subsingleton_extendScalars_of_semilinear f _ hsub (fun b => φ (g b))
      (fun x y => (congrArg φ (hadd x y)).trans (map_add φ _ _))
      (fun r x => (congrArg φ (hsmul r x)).trans (map_mul φ r (g x)))
  have hφ2 : φ (1 + 1) = 0 := by
    rw [map_add, map_one]
    exact two_eq_zero_fiber.{u, w}
  have heven : ∀ b, ∃ c, m b = (1 + 1) * c := fun b =>
    (even_or_odd_base (m b)).resolve_right fun ⟨a, ha⟩ => one_ne_zero_fiber.{u, w} (by
      have := hz m hm_add hm_smul b
      rwa [ha, map_add, map_mul, hφ2, zero_mul, add_zero, map_one] at this)
  choose c hc using heven
  -- halving, then reducing, is semilinear
  have hc_add : ∀ x y, c (x + y) = c x + c y := fun x y =>
    cancel_two_base (by rw [← hc, hm_add, hc x, hc y, mul_add])
  have hc_smul : ∀ (r : ringSheaf.{u, w}.obj.obj (op yZ.{u, w})) x, c (r • x) = r * c x :=
    fun r x => cancel_two_base (by
      have hcomm : r * (1 + 1) = (1 + 1) * r :=
        mul_comm (G := commRingPresheaf.{u, w}.obj (op yZ.{u, w})) r (1 + 1)
      rw [← hc, hm_smul, hc x, ← mul_assoc, ← mul_assoc, hcomm])
  let one : (SheafOfModules.unit ringSheaf.{u, w}).val.obj (op yZ.{u, w}) :=
    (1 : ringSheaf.{u, w}.obj.obj (op yZ.{u, w}))
  have h2 := hz c hc_add hc_smul (imageπ.{u, w}.val.app (op yZ.{u, w}) one)
  have hc1 : c (imageπ.{u, w}.val.app (op yZ.{u, w}) one) = 1 :=
    cancel_two_base (by rw [← hc, mul_one]; exact imageπ_imageι_app yZ one)
  rw [hc1, map_one] at h2
  exact one_ne_zero_fiber.{u, w} h2

/-- `𝒪`, as a quasi-coherent module. -/
def structureQC :
    AlgebraicStacks.quasicoherentModules site.{u} (Spec intRing.{u}) site_contains_base
      stack.{u, w} :=
  ⟨SheafOfModules.unit ringSheaf.{u, w}, SheafOfModules.isQuasicoherentOnSite_unit _⟩

/-- **Stacks 0GQL, part (2), fails as written.** It is not true that for every map `φ` of
quasi-coherent modules on an algebraic stack the image of `φ` computed in `Mod(𝒪_𝒳)` is
quasi-coherent: multiplication by `2` on `𝒪` over `Spec ℤ` is a counterexample. The corrected
part (2) is `AlgebraicGeometry.Stack.AlgebraicStacks.lqcohSheafFbc_image_quasicoherentInclusion`
(the image lies in `LQCoh^fbc(𝒪_𝒳)`) together with
`AlgebraicGeometry.Stack.AlgebraicStacks.coheratorImageIsImage` (its coherator is the image in
`QCoh(𝒪_𝒳)`). -/
@[stacks 0GQL "part (2) as printed is false, and the inclusion QCoh(𝒪_𝒳) → Mod(𝒪_𝒳) is not \
  exact in general: for multiplication by 2 on 𝒪 over Spec ℤ the image computed in Mod(𝒪_𝒳) is \
  not quasi-coherent (it vanishes on Spec 𝔽₂ while its would-be module 2ℤ ⊗ 𝔽₂ does not); the \
  corrected part (2) is lqcohSheafFbc_image_quasicoherentInclusion and coheratorImageIsImage"]
theorem not_forall_isQuasicoherentOnSite_image :
    ¬ ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
      (𝒳 : AlgebraicStacks.{u, w} B S hS) (F G : AlgebraicStacks.quasicoherentModules B S hS 𝒳)
      (φ : F ⟶ G),
      (Abelian.image
        ((AlgebraicStacks.quasicoherentInclusion B S hS 𝒳).map φ)).IsQuasicoherentOnSite :=
  fun h => not_isQuasicoherentOnSite_imageModule.{u, w}
    (h site.{u} (Spec intRing.{u}) site_contains_base stack.{u, w} structureQC structureQC
      (ObjectProperty.homMk two.{u, w}))

end Image

end AlgebraicGeometry.Stack.ImageCounterexample

end
