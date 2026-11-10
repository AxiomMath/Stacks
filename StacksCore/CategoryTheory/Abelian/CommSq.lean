module

public import Mathlib.CategoryTheory.Abelian.CommSq

/-!
# Cartesian and cocartesian squares via exact sequences

A commutative square in an abelian category

```
X₁ ⟶ X₂
|    |
v    v
X₃ ⟶ X₄
```

is cartesian if and only if the associated sequence `0 ⟶ X₁ ⟶ X₂ ⊞ X₃ ⟶ X₄` is exact, and
cocartesian if and only if the sequence `X₁ ⟶ X₂ ⊞ X₃ ⟶ X₄ ⟶ 0` is exact. As a consequence,
a cartesian square with epic right edge is cocartesian, and a cocartesian square with monic
top edge is cartesian.

As an application of Mathlib's `Abelian.mono_cokernel_map_of_isPullback`, the last section proves
the third isomorphism theorem: for `k : X ⟶ Y` and a monomorphism `n : Y ⟶ A`, the induced
`Y/X ⟶ A/X` is a monomorphism and a kernel of `A/X ⟶ A/Y`, so `Y/X ≅ Ker(A/X → A/Y)`
(`Abelian.cokernelIsoKernelCokernelMap`); that `A/X ⟶ A/Y` is a cokernel of `Y/X ⟶ A/X` needs no
hypothesis. The maps are spelled `cokernel.map` as in Mathlib's `kernelCokernelCompSequence`. This
is the underlying-object content of Stacks 0129
(`StacksCore.CategoryTheory.Filtration.Subquotient`).

## Main results

* `CategoryTheory.CommSq.isPullback_iff_exact_and_mono_f` (Stacks 08N2 (1))
* `CategoryTheory.CommSq.isPushout_iff_exact_and_epi_g` (Stacks 08N2 (2))
* `CategoryTheory.CommSq.IsPullback.epi_to_isPushout` (Stacks 08N4 (1))
* `CategoryTheory.CommSq.IsPushout.mono_to_isPullback` (Stacks 08N4 (2))
* `CategoryTheory.Abelian.isColimitCokernelCoforkCokernelMap`, `isLimitKernelForkCokernelMap`,
  `cokernelIsoKernelCokernelMap`: the third isomorphism theorem `Y/X ≅ Ker(A/X → A/Y)`
-/

@[expose] public section

namespace CategoryTheory.CommSq

open Limits

variable {C : Type*} [Category* C] [Abelian C] {X₁ X₂ X₃ X₄ : C}

/-- A commutative square in an abelian category is cartesian if and only if the associated
sequence `0 ⟶ X₁ ⟶ X₂ ⊞ X₃ ⟶ X₄` is exact, where the first map is `biprod.lift fst snd` and
the second is `biprod.desc f (-g)`. -/
@[stacks 08N2 "(1)"]
lemma isPullback_iff_exact_and_mono_f {fst : X₁ ⟶ X₂} {snd : X₁ ⟶ X₃} {f : X₂ ⟶ X₄}
    {g : X₃ ⟶ X₄} (sq : CommSq fst snd f g) :
    IsPullback fst snd f g ↔ sq.shortComplex'.Exact ∧ Mono sq.shortComplex'.f :=
  ⟨fun h ↦ ⟨h.exact_shortComplex', h.mono_shortComplex'_f⟩,
    fun ⟨hS, _⟩ ↦ .of_isLimit' sq (sq.isLimitEquivIsLimitKernelFork.symm hS.fIsKernel)⟩

/-- A commutative square in an abelian category is cocartesian if and only if the associated
sequence `X₁ ⟶ X₂ ⊞ X₃ ⟶ X₄ ⟶ 0` is exact, where the first map is `biprod.lift f (-g)` and
the second is `biprod.desc inl inr`. -/
@[stacks 08N2 "(2)"]
lemma isPushout_iff_exact_and_epi_g {f : X₁ ⟶ X₂} {g : X₁ ⟶ X₃} {inl : X₂ ⟶ X₄}
    {inr : X₃ ⟶ X₄} (sq : CommSq f g inl inr) :
    IsPushout f g inl inr ↔ sq.shortComplex.Exact ∧ Epi sq.shortComplex.g :=
  ⟨fun h ↦ ⟨h.exact_shortComplex, h.epi_shortComplex_g⟩,
    fun ⟨hS, _⟩ ↦ .of_isColimit' sq (sq.isColimitEquivIsColimitCokernelCofork.symm hS.gIsCokernel)⟩

variable {W X Y Z : C} {g : W ⟶ X} {f : W ⟶ Y} {k : X ⟶ Z} {h : Y ⟶ Z} (hComm : CommSq g f k h)

/-- The pushout-flavoured short complex `biprod.lift g (-f) ≫ biprod.desc k h` of a commutative
square is isomorphic to its pullback-flavoured short complex `biprod.lift g f ≫ biprod.desc k (-h)`
via `biprod.map (𝟙 X) (-𝟙 Y)` in the middle. -/
noncomputable def shortComplexIsoShortComplex' : hComm.shortComplex ≅ hComm.shortComplex' :=
  ShortComplex.isoMk (Iso.refl _) (biprod.mapIso (Iso.refl _) (-Iso.refl _)) (Iso.refl _)
    (by dsimp [CommSq.shortComplex, CommSq.shortComplex']; ext <;> simp)
    (by dsimp [CommSq.shortComplex, CommSq.shortComplex']; ext <;> simp)

@[stacks 08N4 "(1)"]
lemma IsPullback.epi_to_isPushout (hP : IsPullback g f k h) [Epi k] :
    IsPushout g f k h ∧ Epi f :=
  ⟨hP.toCommSq.isPushout_iff_exact_and_epi_g.2 ⟨ShortComplex.exact_of_iso
    (shortComplexIsoShortComplex' hP.toCommSq).symm hP.exact_shortComplex',
    inferInstanceAs (Epi (biprod.desc k h))⟩,
    Abelian.epi_snd_of_isLimit _ _ hP.isLimit⟩

@[stacks 08N4 "(2)"]
lemma IsPushout.mono_to_isPullback (hP : IsPushout g f k h) [Mono g] :
    IsPullback g f k h ∧ Mono h :=
  ⟨hP.toCommSq.isPullback_iff_exact_and_mono_f.2 ⟨ShortComplex.exact_of_iso
    (shortComplexIsoShortComplex' hP.toCommSq) hP.exact_shortComplex,
    inferInstanceAs (Mono (biprod.lift g f))⟩, Abelian.mono_inr_of_isColimit _ _ hP.isColimit⟩

end CategoryTheory.CommSq

/-! ### The third isomorphism theorem -/

namespace CategoryTheory.Abelian

open Limits

variable {C : Type*} [Category* C] [Abelian C] {X Y A : C} (k : X ⟶ Y) (n : Y ⟶ A)

/-- `Y/X ⟶ A/X`: the morphism `Coker k ⟶ Coker (k ≫ n)` induced by `n` is a monomorphism when
`n` is, the square `k, 𝟙 X, n, k ≫ n` being a fibre product (`X = Y ∩ X` inside `A`). -/
instance mono_cokernel_map_comp [Mono n] : Mono (cokernel.map k (k ≫ n) (𝟙 X) n (by simp)) :=
  mono_cokernel_map_of_isPullback (IsPullback.of_vert_isIso_mono ⟨by simp⟩)

/-- `Y/X ⟶ A/X ⟶ A/Y` is zero. -/
@[reassoc (attr := simp)]
lemma cokernel_map_comp_cokernel_map :
    cokernel.map k (k ≫ n) (𝟙 X) n (by simp) ≫ cokernel.map (k ≫ n) n k (𝟙 A) (by simp) = 0 := by
  ext; simp

/-- `A/X ⟶ A/Y` is a cokernel of `Y/X ⟶ A/X`: as `Y → A → A/X` is `Y → Y/X → A/X`, a morphism `φ`
out of `A/X` killing `Y/X ⟶ A/X` has `n ≫ π_X ≫ φ = 0`, so `π_X ≫ φ` factors through
`A/Y = Coker n`, hence so does `φ`, `π_X` being an epimorphism (uniquely, `A/X ⟶ A/Y` being one
too). No hypothesis on `k` or `n`: `Y/X` is `Y/Im k` and `A/Y` is `A/Im n`. -/
noncomputable def isColimitCokernelCoforkCokernelMap :
    IsColimit (CokernelCofork.ofπ (cokernel.map (k ≫ n) n k (𝟙 A) (by simp))
      (cokernel_map_comp_cokernel_map k n)) := by
  have hq : cokernel.π k ≫ cokernel.map k (k ≫ n) (𝟙 X) n (by simp) = n ≫ cokernel.π (k ≫ n) :=
    cokernel.π_desc _ _ _
  refine CokernelCofork.IsColimit.ofπ' _ _ fun {T} φ hφ =>
    ⟨cokernel.desc n (cokernel.π (k ≫ n) ≫ φ) ?_, ?_⟩
  · rw [← Category.assoc, ← hq, Category.assoc, hφ, comp_zero]
  · ext; simp

/-- The third isomorphism theorem: `Y/X ⟶ A/X` is a kernel of `A/X ⟶ A/Y`, for a monomorphism
`n : Y ⟶ A` (so that `Y/X ⟶ A/X` is a monomorphism, and a monomorphism is the kernel of its
cokernel in an abelian category). -/
noncomputable def isLimitKernelForkCokernelMap [Mono n] :
    IsLimit (KernelFork.ofι (cokernel.map k (k ≫ n) (𝟙 X) n (by simp))
      (cokernel_map_comp_cokernel_map k n)) :=
  monoIsKernelOfCokernel _ (isColimitCokernelCoforkCokernelMap k n)

/-- The third isomorphism theorem as an isomorphism, `Y/X ≅ Ker(A/X → A/Y)` for `X ⊆ Y ⊆ A`,
i.e. for `k : X ⟶ Y` and a monomorphism `n : Y ⟶ A`; it is compatible with the maps to `A/X`
(`cokernelIsoKernelCokernelMap_hom_comp_ι`). -/
noncomputable def cokernelIsoKernelCokernelMap [Mono n] :
    cokernel k ≅ kernel (cokernel.map (k ≫ n) n k (𝟙 A) (by simp)) :=
  IsLimit.conePointUniqueUpToIso
    (t := KernelFork.ofι (kernel.ι (cokernel.map (k ≫ n) n k (𝟙 A) (by simp)))
      (kernel.condition _))
    (isLimitKernelForkCokernelMap k n)
    (kernelIsKernel (cokernel.map (k ≫ n) n k (𝟙 A) (by simp)))

/-- The third isomorphism `Y/X ≅ Ker(A/X → A/Y)` is compatible with the maps to `A/X`. -/
@[reassoc (attr := simp)]
lemma cokernelIsoKernelCokernelMap_hom_comp_ι [Mono n] :
    (cokernelIsoKernelCokernelMap k n).hom ≫
        kernel.ι (cokernel.map (k ≫ n) n k (𝟙 A) (by simp)) =
      cokernel.map k (k ≫ n) (𝟙 X) n (by simp) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

/-- The inverse of the third isomorphism `Y/X ≅ Ker(A/X → A/Y)`, followed by `Y/X ⟶ A/X`, is the
kernel inclusion. -/
@[reassoc (attr := simp)]
lemma cokernelIsoKernelCokernelMap_inv_comp_cokernel_map [Mono n] :
    (cokernelIsoKernelCokernelMap k n).inv ≫ cokernel.map k (k ≫ n) (𝟙 X) n (by simp) =
      kernel.ι (cokernel.map (k ≫ n) n k (𝟙 A) (by simp)) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingParallelPair.zero

end CategoryTheory.Abelian
