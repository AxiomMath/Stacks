module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelThickeningRingHom
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceCompletedBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.TwistedBaseChange

/-!
# The sections of a quasi-coherent crystal over a pointed affine object

Let `ℱ` be a crystal in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)`, with `X` and `S` affine,
let `D = D(0)` be the completed divided power envelope of the situation's own presentation and
let `M = lim_e Γ((X, T(0)_e, δ), ℱ)` be its module of [Stacks, Lemma 60.17.3, Tag 07JG]
(`...SmallSite.wholeSpaceSections`).  An object `A = (U, T, δ)` of `Cris(X/S)` together with a
morphism `h : A ⟶ T(0)_e` to one of the levels is a *pointed* object: `h` makes `Γ(T, 𝒪_T)` a
`D`-algebra, through `ptRing h : D → Γ(T(0)_e, 𝒪) → Γ(T, 𝒪_T)`.  This module proves that for
`A` affine the sections of `ℱ` over `A` are the base change of `M` along that ring map:

`Γ(T, 𝒪_T) ⊗_{D, ptRing h} M ≅ ℱ(A)`,  `b ⊗ m ↦ b · h^* m_e`,

which is how the sections of `ℱ` over an arbitrary affine object are recovered from the pair
`(M, ∇)` in the proof of [Stacks, Proposition 60.17.4, Tag 07JH].

## The argument

The map factors through the level `T(0)_e`:

* the reduction `D → Γ(T(0)_e, 𝒪)` is surjective with kernel `(p)^{N+e}`
  (`...SmallSite.surjective_levelSectionsScalars`, `...SmallSite.levelSectionsScalars_eq_zero_iff`)
  and the reduction `M → Γ(T(0)_e, ℱ)` is surjective with kernel `(p)^{N+e} M`
  (`...SmallSite.levelSectionsTopReduce_eq_zero_iff`), so
  `Γ(T, 𝒪_T) ⊗_D M ≅ Γ(T, 𝒪_T) ⊗_{Γ(T(0)_e, 𝒪)} Γ(T(0)_e, ℱ)`
  (`...SmallSite.bijective_crystalPointReduce`, whose inverse is written down);
* the base change of the sections of a quasi-coherent crystal along `h` is bijective
  (`...SmallSite.bijective_crysAmbientBaseChange`).

## Main definitions and results

* `...SmallSite.ptRing` — the ring map `D → Γ(T, 𝒪_T)` of a pointed object.
* `...SmallSite.crystalPointMap` — the map `Γ(T, 𝒪_T) ⊗_D M → ℱ(A)`, with
  `...SmallSite.crystalPointMap_tmul`.
* `...SmallSite.bijective_crystalPointMap` and `...SmallSite.crystalPointEquiv` — **it is
  bijective for `A` affine.**
* `...SmallSite.crystalPointMap_comp` — naturality in the pointed object.
* `...SmallSite.crystalPointMap_naturality` — naturality in the crystal.

## Implementation notes

The ring `Γ(T, 𝒪_T)` is spelled `Crystalline.GlobalCrystallineSituation.crysSheafRing S A.obj`:
it is the same ring as `Γ(A.obj.thickening.target.scheme, ⊤)` and as the sections of
`...structureSheaf S` over `A`, and it is the spelling carrying both a `CommRing` instance and the
module structure on the sections of a sheaf of `𝒪_{X/S}`-modules
(`...SmallSite.moduleCrysSheafRingSections`).

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Simplicial
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open CohomologyRestriction

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]

section Point

variable {e : ℕ} {A : CrystallineThickening S}

/-- **The ring map `D → Γ(T, 𝒪_T)` of a pointed object** `h : (U, T, δ) ⟶ T(0)_e`: the reduction
`...SmallSite.levelSectionsScalars` of `D` to the level `T(0)_e` followed by the restriction map
of `𝒪_{X/S}` along `h`. -/
def ptRing (h : A ⟶ levelObj hp 0 e) :
    ((wholeSpaceEnvelopeRing hp).obj ⦋0⦌ : Type u) →+* crysSheafRing S A.obj :=
  (crysSheafRingMap h.hom).comp (levelSectionsScalars hp ⦋0⦌ e)

/-- `...SmallSite.ptRing` is reduction to the level followed by restriction along `h`. -/
theorem ptRing_apply (h : A ⟶ levelObj hp 0 e)
    (d : ((wholeSpaceEnvelopeRing hp).obj ⦋0⦌ : Type u)) :
    ptRing hp h d = crysSheafRingMap h.hom (levelSectionsScalars hp ⦋0⦌ e d) := rfl

/-- **The ring map of a composite pointing** `k ≫ h` is that of `h` followed by the restriction
map of `𝒪_{X/S}` along `k`. -/
theorem ptRing_comp {A' : CrystallineThickening S} (k : A' ⟶ A) (h : A ⟶ levelObj hp 0 e) :
    ptRing hp (k ≫ h) = (crysSheafRingMap k.hom).comp (ptRing hp h) :=
  RingHom.ext fun d ↦
    (crysSheafRingMap_comp k.hom h.hom (bigRingSection _ (levelSectionsScalars hp ⦋0⦌ e d))).symm

variable (F : QuasiCoherentCrystal S)

/-- **The semilinear map `M → ℱ(A)`, `m ↦ h^* m_e`, of a pointed object**: the component of `m` at
the level `e`, restricted along `h`.  It is semilinear over `...SmallSite.ptRing`. -/
def crystalPointSemilinear (h : A ⟶ levelObj hp 0 e) :
    wholeSpaceSections hp F ⦋0⦌ →ₛₗ[ptRing hp h] F.obj.val.obj (op A) where
  toFun m := crysRestrict F.obj h (wholeSpaceSectionsVal hp F m e)
  map_add' x y := by rw [wholeSpaceSectionsVal_add, map_add]
  map_smul' d m := by
    rw [wholeSpaceSectionsVal_smul]
    exact F.obj.val.map_smul h.op _ _

/-- **The sections of a quasi-coherent crystal over a pointed object, from the module `M`**:

`Γ(T, 𝒪_T) ⊗_{D, ptRing h} M ⟶ ℱ(A)`,  `b ⊗ m ↦ b · h^* m_e`,

the base change of `...SmallSite.crystalPointSemilinear`.  It is bijective for `A` affine,
`...SmallSite.bijective_crystalPointMap`. -/
def crystalPointMap (h : A ⟶ levelObj hp 0 e) :
    TwistedScalars (ptRing hp h) ⊗[((wholeSpaceEnvelopeRing hp).obj ⦋0⦌ : Type u)]
        wholeSpaceSections hp F ⦋0⦌ →ₗ[crysSheafRing S A.obj] F.obj.val.obj (op A) :=
  semilinearBaseChange (crystalPointSemilinear hp F h)

/-- `...SmallSite.crystalPointMap` on a pure tensor: `b ⊗ m ↦ b · h^* m_e`. -/
@[simp] theorem crystalPointMap_tmul (h : A ⟶ levelObj hp 0 e)
    (b : TwistedScalars (ptRing hp h)) (m : wholeSpaceSections hp F ⦋0⦌) :
    crystalPointMap hp F h (b ⊗ₜ m) =
      b.val • crysRestrict F.obj h (wholeSpaceSectionsVal hp F m e) :=
  rfl

end Point

section Bijective

variable (F : QuasiCoherentCrystal S) {e : ℕ} {A : CrystallineThickening S}
  (h : A ⟶ levelObj hp 0 e)

/-- The biadditive map of `...SmallSite.crystalPointReduce`. -/
def crystalPointReduceAux :
    TwistedScalars (ptRing hp h) →+ wholeSpaceSections hp F ⦋0⦌ →+
      ringAlong h.hom ⊗[Γ((levelObj hp 0 e).obj.thickening.target.scheme, ⊤)]
        Γ(ambientSchemeOf (levelObj hp 0 e).obj
          (moduleRestrictionSheaf F.obj (levelObj hp 0 e)), ⊤) :=
  AddMonoidHom.mk'
    (fun b ↦ AddMonoidHom.mk'
      (fun m ↦ ringAlongSection h.hom b.val ⊗ₜ levelSectionsTopReduce hp F 0 e m)
      fun m m' ↦ by rw [map_add, TensorProduct.tmul_add])
    fun b b' ↦ AddMonoidHom.ext fun m ↦ TensorProduct.add_tmul _ _ _

/-- **The reduction of `Γ(T, 𝒪_T) ⊗_D M` to the level `T(0)_e`**:

`Γ(T, 𝒪_T) ⊗_D M ⟶ Γ(T, 𝒪_T) ⊗_{Γ(T(0)_e, 𝒪)} Γ(T(0)_e, ℱ_{T(0)_e})`,  `b ⊗ m ↦ b ⊗ m_e`,

the target being the source of the base change of ambient sections along `h`. -/
def crystalPointReduce :
    TwistedScalars (ptRing hp h) ⊗[((wholeSpaceEnvelopeRing hp).obj ⦋0⦌ : Type u)]
        wholeSpaceSections hp F ⦋0⦌ →+
      ringAlong h.hom ⊗[Γ((levelObj hp 0 e).obj.thickening.target.scheme, ⊤)]
        Γ(ambientSchemeOf (levelObj hp 0 e).obj
          (moduleRestrictionSheaf F.obj (levelObj hp 0 e)), ⊤) :=
  TensorProduct.liftAddHom (crystalPointReduceAux hp F h) fun d b m ↦ by
    change ringAlongSection h.hom (ptRing hp h d * b.val) ⊗ₜ levelSectionsTopReduce hp F 0 e m =
      ringAlongSection h.hom b.val ⊗ₜ levelSectionsTopReduce hp F 0 e (d • m)
    rw [levelSectionsTopReduce_smul, ← TensorProduct.smul_tmul]
    congr 1
    exact (ambientRingSection_smul_ringAlong h.hom
      (bigRingSection _ (levelSectionsScalars hp ⦋0⦌ e d)) (ringAlongSection h.hom b.val)).symm

/-- `...SmallSite.crystalPointReduce` on a pure tensor. -/
theorem crystalPointReduce_tmul (b : TwistedScalars (ptRing hp h))
    (m : wholeSpaceSections hp F ⦋0⦌) :
    crystalPointReduce hp F h (b ⊗ₜ m) =
      ringAlongSection h.hom b.val ⊗ₜ levelSectionsTopReduce hp F 0 e m := rfl

/-- **`b ⊗ m` vanishes as soon as `m` vanishes at the level `e`**: such an `m` lies in
`(p)^{N+e} M`, and `(p)^{N+e}` dies in `Γ(T(0)_e, 𝒪)`, hence acts by zero on `Γ(T, 𝒪_T)`. -/
theorem crystalPoint_tmul_eq_zero (b : TwistedScalars (ptRing hp h))
    {m : wholeSpaceSections hp F ⦋0⦌} (hm : levelSectionsTopReduce hp F 0 e m = 0) :
    b ⊗ₜ[((wholeSpaceEnvelopeRing hp).obj ⦋0⦌ : Type u)] m = 0 := by
  have hmem := (levelSectionsTopReduce_eq_zero_iff hp e
    (isSurjectiveComparison_of_isSheafCrystal F.property.2) 0 m).1 hm
  refine Submodule.smul_induction_on hmem (fun a ha x _ ↦ ?_) (fun x y hx hy ↦ ?_)
  · rw [← TensorProduct.smul_tmul]
    have hab : a • b = 0 := by
      have h0 : ptRing hp h a = 0 :=
        (congrArg (crysSheafRingMap h.hom)
          ((levelSectionsScalars_eq_zero_iff hp ⦋0⦌ e a).2 ha)).trans (map_zero _)
      change ptRing hp h a * b.val = (0 : crysSheafRing S A.obj)
      rw [h0, zero_mul]
    rw [hab, TensorProduct.zero_tmul]
  · rw [TensorProduct.tmul_add, hx, hy, add_zero]

/-- `b ⊗ m` depends only on the component of `m` at the level `e`. -/
theorem crystalPoint_tmul_eq_of_eq (b : TwistedScalars (ptRing hp h))
    {m m' : wholeSpaceSections hp F ⦋0⦌}
    (hm : levelSectionsTopReduce hp F 0 e m = levelSectionsTopReduce hp F 0 e m') :
    b ⊗ₜ[((wholeSpaceEnvelopeRing hp).obj ⦋0⦌ : Type u)] m = b ⊗ₜ m' := by
  rw [← sub_eq_zero, ← TensorProduct.tmul_sub]
  exact crystalPoint_tmul_eq_zero hp F h b (by rw [map_sub, hm, sub_self])

/-- The function `(b, m_e) ↦ b ⊗ m` underlying `...SmallSite.crystalPointLift`, through a chosen
preimage of the section at the level. -/
def crystalPointLiftFun (b : ringAlong h.hom)
    (s : Γ(ambientSchemeOf (levelObj hp 0 e).obj
      (moduleRestrictionSheaf F.obj (levelObj hp 0 e)), ⊤)) :
    TwistedScalars (ptRing hp h) ⊗[((wholeSpaceEnvelopeRing hp).obj ⦋0⦌ : Type u)]
        wholeSpaceSections hp F ⦋0⦌ :=
  TwistedScalars.mk (ptRing hp h) (siteRingAlong h.hom b) ⊗ₜ
    Function.surjInv (surjective_levelSectionsTopReduce hp e
      (isSurjectiveComparison_of_isSheafCrystal F.property.2) 0) s

/-- `...SmallSite.crystalPointLiftFun` on a reduction: `(b, m_e) ↦ b ⊗ m`. -/
theorem crystalPointLiftFun_reduce (b : ringAlong h.hom) (m : wholeSpaceSections hp F ⦋0⦌) :
    crystalPointLiftFun hp F h b (levelSectionsTopReduce hp F 0 e m) =
      TwistedScalars.mk (ptRing hp h) (siteRingAlong h.hom b) ⊗ₜ m :=
  crystalPoint_tmul_eq_of_eq hp F h _ (Function.surjInv_eq _ _)

/-- The biadditive map of `...SmallSite.crystalPointLift`. -/
def crystalPointLiftAux : ringAlong h.hom →+
    Γ(ambientSchemeOf (levelObj hp 0 e).obj
      (moduleRestrictionSheaf F.obj (levelObj hp 0 e)), ⊤) →+
    TwistedScalars (ptRing hp h) ⊗[((wholeSpaceEnvelopeRing hp).obj ⦋0⦌ : Type u)]
        wholeSpaceSections hp F ⦋0⦌ :=
  have hsurj := surjective_levelSectionsTopReduce hp e
    (isSurjectiveComparison_of_isSheafCrystal F.property.2) 0
  AddMonoidHom.mk'
    (fun b ↦ AddMonoidHom.mk' (crystalPointLiftFun hp F h b) fun s s' ↦ by
      obtain ⟨m, rfl⟩ := hsurj s
      obtain ⟨m', rfl⟩ := hsurj s'
      rw [← map_add, crystalPointLiftFun_reduce, crystalPointLiftFun_reduce,
        crystalPointLiftFun_reduce, TensorProduct.tmul_add])
    fun b b' ↦ AddMonoidHom.ext fun s ↦ TensorProduct.add_tmul _ _ _

/-- **The inverse of `...SmallSite.crystalPointReduce`**: `b ⊗ m_e ↦ b ⊗ m`. -/
def crystalPointLift :
    ringAlong h.hom ⊗[Γ((levelObj hp 0 e).obj.thickening.target.scheme, ⊤)]
        Γ(ambientSchemeOf (levelObj hp 0 e).obj
          (moduleRestrictionSheaf F.obj (levelObj hp 0 e)), ⊤) →+
      TwistedScalars (ptRing hp h) ⊗[((wholeSpaceEnvelopeRing hp).obj ⦋0⦌ : Type u)]
        wholeSpaceSections hp F ⦋0⦌ :=
  TensorProduct.liftAddHom (crystalPointLiftAux hp F h) fun r b s ↦ by
    obtain ⟨d, rfl⟩ := surjective_levelSectionsScalars hp ⦋0⦌ e r
    obtain ⟨m, rfl⟩ := surjective_levelSectionsTopReduce hp e
      (isSurjectiveComparison_of_isSheafCrystal F.property.2) 0 s
    change crystalPointLiftFun hp F h (levelAmbientScalars hp 0 e d • b)
        (levelSectionsTopReduce hp F 0 e m) =
      crystalPointLiftFun hp F h b
        (levelAmbientScalars hp 0 e d • levelSectionsTopReduce hp F 0 e m)
    rw [← levelSectionsTopReduce_smul, crystalPointLiftFun_reduce, crystalPointLiftFun_reduce,
      ← TensorProduct.smul_tmul]
    congr 1
    exact congrArg (TwistedScalars.mk (ptRing hp h))
      (congrArg (siteRingAlong h.hom) (ambientRingSection_smul_ringAlong h.hom
        (bigRingSection _ (levelSectionsScalars hp ⦋0⦌ e d)) b))

/-- `...SmallSite.crystalPointLift` is a left inverse of the reduction. -/
theorem crystalPointLift_reduce (z) :
    crystalPointLift hp F h (crystalPointReduce hp F h z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul b m => exact crystalPointLiftFun_reduce hp F h _ m
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- `...SmallSite.crystalPointLift` is a right inverse of the reduction. -/
theorem crystalPointReduce_lift (w) :
    crystalPointReduce hp F h (crystalPointLift hp F h w) = w := by
  induction w using TensorProduct.inductionOn with
  | tmul b s =>
    obtain ⟨m, rfl⟩ := surjective_levelSectionsTopReduce hp e
      (isSurjectiveComparison_of_isSheafCrystal F.property.2) 0 s
    change crystalPointReduce hp F h (crystalPointLiftFun hp F h b _) = _
    rw [crystalPointLiftFun_reduce, crystalPointReduce_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **The reduction of `Γ(T, 𝒪_T) ⊗_D M` to the level `T(0)_e` is bijective.** -/
theorem bijective_crystalPointReduce : Function.Bijective (crystalPointReduce hp F h) :=
  Function.bijective_iff_has_inverse.2
    ⟨crystalPointLift hp F h, crystalPointLift_reduce hp F h, crystalPointReduce_lift hp F h⟩

attribute [local instance] isAffineTargetWholeSpaceSystem

/-- **`...SmallSite.crystalPointMap` is the reduction to the level followed by the base change of
ambient sections along `h`**, read on the sections over the whole of the ambient scheme. -/
theorem crysSectionTop_crystalPointMap [IsAffine A.obj.thickening.target.scheme]
    [(ambientSchemeOf (levelObj hp 0 e).obj
      (moduleRestrictionSheaf F.obj (levelObj hp 0 e))).IsQuasicoherent] (z) :
    crysSectionTop F.obj A (crystalPointMap hp F h z) =
      ambientBaseChangeTensorFun h.hom (moduleRestrictionSheaf F.obj (levelObj hp 0 e))
        (moduleRestrictionSheaf F.obj A) (moduleFMapSheaf F.obj h)
        (crystalPointReduce hp F h z) := by
  induction z using TensorProduct.inductionOn with
  | tmul b m =>
    rw [crystalPointMap_tmul, crystalPointReduce_tmul, ambientBaseChangeTensorFun_tmul,
      levelSectionsTopReduce_apply, fmapTopSection_crysSectionTop]
    exact crysSectionTop_smul F.obj A (bigRingSection A b.val) _
  | add x y hx hy =>
    rw [map_add, ← crysSectionTopHom_apply, map_add, crysSectionTopHom_apply,
      crysSectionTopHom_apply, hx, hy, map_add, ambientBaseChangeTensorFun_add]

/-- **The sections of a quasi-coherent crystal over an affine pointed object are the base change of
`M = lim_e Γ(T(0)_e, ℱ)`**: for `A` affine and `h : A ⟶ T(0)_e`,

`Γ(T, 𝒪_T) ⊗_{D, ptRing h} M ⟶ ℱ(A)`,  `b ⊗ m ↦ b · h^* m_e`,

is bijective. -/
theorem bijective_crystalPointMap (hA : IsAffineObject S A) :
    Function.Bijective (crystalPointMap hp F h) := by
  have := hA.2
  have := isQuasicoherent_ambientWholeSpaceSystem hp F.obj
    (isLocallyQuasiCoherent_of_isQuasicoherentOnSite F.obj F.property.1) 0 e
  refine (Function.Bijective.of_comp_iff' (bijective_crysSectionTop F.obj A) _).1 ?_
  have hfun : crysSectionTop F.obj A ∘ crystalPointMap hp F h =
      ambientBaseChangeTensorFun h.hom (moduleRestrictionSheaf F.obj (levelObj hp 0 e))
        (moduleRestrictionSheaf F.obj A) (moduleFMapSheaf F.obj h) ∘
        crystalPointReduce hp F h :=
    funext fun z ↦ crysSectionTop_crystalPointMap hp F h z
  rw [hfun]
  exact (bijective_crysAmbientBaseChange F.obj h F.property.2).comp
    (bijective_crystalPointReduce hp F h)

/-- **The sections of a quasi-coherent crystal over an affine pointed object**, as a
`Γ(T, 𝒪_T)`-linear equivalence `Γ(T, 𝒪_T) ⊗_{D, ptRing h} M ≃ ℱ(A)`. -/
def crystalPointEquiv (hA : IsAffineObject S A) :
    TwistedScalars (ptRing hp h) ⊗[((wholeSpaceEnvelopeRing hp).obj ⦋0⦌ : Type u)]
        wholeSpaceSections hp F ⦋0⦌ ≃ₗ[crysSheafRing S A.obj] F.obj.val.obj (op A) :=
  LinearEquiv.ofBijective (crystalPointMap hp F h) (bijective_crystalPointMap hp F h hA)

/-- `...SmallSite.crystalPointEquiv` is `...SmallSite.crystalPointMap`. -/
@[simp] theorem crystalPointEquiv_apply (hA : IsAffineObject S A) (z) :
    crystalPointEquiv hp F h hA z = crystalPointMap hp F h z := rfl

end Bijective

section Naturality

variable {e : ℕ} {A A' : CrystallineThickening S} (k : A' ⟶ A) (h : A ⟶ levelObj hp 0 e)

/-- **The change of pointed object** along `k : A' ⟶ A`: the restriction map
`Γ(T, 𝒪_T) → Γ(T', 𝒪_{T'})`, which is `D`-linear from the structure along `h` to the structure
along `k ≫ h`. -/
def ptPush :
    TwistedScalars (ptRing hp h) →ₗ[((wholeSpaceEnvelopeRing hp).obj ⦋0⦌ : Type u)]
      TwistedScalars (ptRing hp (k ≫ h)) where
  toFun b := TwistedScalars.mk _ (crysSheafRingMap k.hom b.val)
  map_add' b b' := map_add (crysSheafRingMap k.hom) b.val b'.val
  map_smul' d b := by
    change crysSheafRingMap k.hom (ptRing hp h d * b.val) =
      ptRing hp (k ≫ h) d * crysSheafRingMap k.hom b.val
    rw [map_mul]
    exact congrArg (· * crysSheafRingMap k.hom b.val)
      (crysSheafRingMap_comp k.hom h.hom (bigRingSection _ (levelSectionsScalars hp ⦋0⦌ e d)))

/-- `...SmallSite.ptPush` is the restriction map of `𝒪_{X/S}` along `k`. -/
@[simp] theorem ptPush_val (b : TwistedScalars (ptRing hp h)) :
    (ptPush hp k h b).val = crysSheafRingMap k.hom b.val := rfl

/-- **Naturality of `...SmallSite.crystalPointMap` in the pointed object**: for `k : A' ⟶ A`,
`crystalPointMap (k ≫ h) (O(k)(b) ⊗ m) = k^* (crystalPointMap h (b ⊗ m))`. -/
theorem crystalPointMap_comp (F : QuasiCoherentCrystal S) (z) :
    crystalPointMap hp F (k ≫ h) (LinearMap.rTensor _ (ptPush hp k h) z) =
      crysRestrict F.obj k (crystalPointMap hp F h z) := by
  induction z using TensorProduct.inductionOn with
  | tmul b m =>
    rw [LinearMap.rTensor_tmul, crystalPointMap_tmul, crystalPointMap_tmul, ptPush_val,
      map_smulₛₗ, crysRestrict_comp]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

/-- **The `D`-linear map `M(ℱ) → M(𝒢)` induced by a morphism of crystals**:
`(wholeSpaceLevelScalars hp 0).sectionsMap ψ`, read over `D = (wholeSpaceEnvelopeRing hp).obj ⦋0⦌`.
-/
def wholeSpaceSectionsLinearMap {F G : QuasiCoherentCrystal S} (ψ : F ⟶ G) :
    wholeSpaceSections hp F ⦋0⦌ →ₗ[((wholeSpaceEnvelopeRing hp).obj ⦋0⦌ : Type u)]
      wholeSpaceSections hp G ⦋0⦌ where
  toFun := (wholeSpaceLevelScalars hp 0).sectionsMap ψ
  map_add' := map_add _
  map_smul' d m :=
    LinearMap.map_smul ((wholeSpaceLevelScalars hp 0).sectionsMap ψ)
      ((wholeSpaceSystemEnvelopeRingEquiv hp 0).symm d)
      (show (wholeSpaceLevelScalars hp 0).sections F from m)

/-- `...SmallSite.wholeSpaceSectionsLinearMap ψ` is `(wholeSpaceLevelScalars hp 0).sectionsMap ψ`.
-/
theorem wholeSpaceSectionsLinearMap_apply {F G : QuasiCoherentCrystal S} (ψ : F ⟶ G)
    (m : wholeSpaceSections hp F ⦋0⦌) :
    wholeSpaceSectionsLinearMap hp ψ m = (wholeSpaceLevelScalars hp 0).sectionsMap ψ m := rfl

/-- The component at a level of `...SmallSite.wholeSpaceSectionsLinearMap ψ` is `ψ` there. -/
theorem wholeSpaceSectionsVal_linearMap {F G : QuasiCoherentCrystal S} (ψ : F ⟶ G)
    (m : wholeSpaceSections hp F ⦋0⦌) (e : ℕ) :
    wholeSpaceSectionsVal hp G (wholeSpaceSectionsLinearMap hp ψ m) e =
      (((quasiCoherentCrystalι S).map ψ).val.app (op (levelObj hp 0 e))).hom
        (wholeSpaceSectionsVal hp F m e) := rfl

/-- **Naturality of `...SmallSite.crystalPointMap` in the crystal**: for `ψ : ℱ ⟶ 𝒢`,
`ψ_A ∘ crystalPointMap ℱ h = crystalPointMap 𝒢 h ∘ (id ⊗ ψ_*)`. -/
theorem crystalPointMap_naturality {F G : QuasiCoherentCrystal S} (ψ : F ⟶ G) (z) :
    (((quasiCoherentCrystalι S).map ψ).val.app (op A)).hom (crystalPointMap hp F h z) =
      crystalPointMap hp G h (LinearMap.lTensor _ (wholeSpaceSectionsLinearMap hp ψ) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul b m =>
    rw [LinearMap.lTensor_tmul, crystalPointMap_tmul, crystalPointMap_tmul,
      wholeSpaceSectionsVal_linearMap]
    refine (LinearMap.map_smul _ _ _).trans ?_
    congr 1
    exact PresheafOfModules.naturality_apply _ h.op _
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

end Naturality

end Crystalline.GlobalCrystallineSituation.SmallSite

end
