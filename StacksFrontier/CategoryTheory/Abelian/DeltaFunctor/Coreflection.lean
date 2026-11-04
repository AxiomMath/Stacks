module

public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Basic
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.Coreflective
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# δ-functors through exact coreflections

Let `𝒜` be an abelian category, `L ⊆ 𝒜` a weak Serre subcategory (**Stacks 0754**), and
`i : 𝒞 ⥤ 𝒜` a fully faithful additive functor out of a preadditive category, landing in `L`,
with a right adjoint `Q : 𝒜 ⥤ 𝒞` whose restriction to `L` is right exact.  This is the shape of
the inclusion `QCoh(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` of an algebraic stack with its coherator, `L` being
`LQCoh^fbc(𝒪_𝒳)` (**Stacks 0771**, **Stacks 0778**, **Stacks 0779**).  Then `𝒞` is abelian
(`CategoryTheory.abelianOfCoreflection`), although `i` need not be exact.

Suppose given a second such datum `(ℬ, 𝒟, i', Q', L')` and a cohomological δ-functor
`D = {Dⁿ} : 𝒜 ⥤ ℬ` (**Stacks 010Q**) which carries `L` into `L'` and carries every object of `L`
killed by `Q` to an object whose image under `Dⁿ` is killed by `Q'`.  This file shows that the
family `n ↦ i ⋙ Dⁿ ⋙ Q'` is a cohomological δ-functor `𝒞 ⥤ 𝒟`
(`CategoryTheory.DeltaFunctor.ofCoreflections`).  This is the argument of the source for the
higher direct images `R^i f_{QCoh,*}` in **Stacks 077A**, stated for abstract categories.

## The connecting morphism

A short exact sequence `0 → F₁ → F₂ → F₃ → 0` of `𝒞` is in general not short exact after `i`.
Since `i` is a left adjoint, `i F₂ → i F₃` is still an epimorphism; let `K` be its kernel in `𝒜`
and `k : i F₁ → K` the induced map.  Then `0 → K → i F₂ → i F₃ → 0` is short exact in `𝒜`, all
its terms lie in `L`, and `Q k` is an isomorphism, since `Q` preserves kernels and `Q ∘ i ≅ 𝟭`.
The second point is that `Q' (Dⁿ k)` is then an isomorphism for every `n`
(`CategoryTheory.DeltaFunctor.isIso_map_map_of_isIso_map`): the kernel and the cokernel of `k`
lie in `L` and are killed by `Q`, so by hypothesis `Q' ∘ Dⁿ` kills them in every degree, and the
long exact sequences of `D`, mapped by `Q'`, which is exact on `L'`, show that `Q' ∘ Dⁿ` inverts
both halves of the image factorisation of `k`.  The connecting morphism of `n ↦ i ⋙ Dⁿ ⋙ Q'` is
then `Q'(δ) ≫ Q'(Dⁿ⁺¹ k)⁻¹`, `δ` being the connecting morphism of `D` at
`0 → K → i F₂ → i F₃ → 0`.

The source breaks the image of the sequence under `i` into four short exact sequences with
parasitic outer terms.  The fourth outer term is `0` here, because `i` preserves epimorphisms,
which is why one sequence suffices.

## Main definitions

* `CategoryTheory.DeltaFunctor.ofCoreflections`: the δ-functor `n ↦ i ⋙ Dⁿ ⋙ Q'`.

## Main results

* `CategoryTheory.DeltaFunctor.shortExact_map_of_prop` and
  `CategoryTheory.DeltaFunctor.exact_map_of_prop`: `Q` preserves short exact and exact sequences
  of `𝒜` whose terms lie in `L`.
* `CategoryTheory.DeltaFunctor.isIso_map_map_of_isIso_map`: `Q' ∘ Dⁿ` inverts every morphism
  between objects of `L` which `Q` inverts.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 077A](https://stacks.math.columbia.edu/tag/077A)
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

namespace CategoryTheory.DeltaFunctor

section Coreflection

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜]
  {𝒞 : Type u₂} [Category.{v₂} 𝒞] [Preadditive 𝒞]
  {i : 𝒞 ⥤ 𝒜} {Q : 𝒜 ⥤ 𝒞} (adj : i ⊣ Q) [i.Full] [i.Faithful] [Q.Additive]
  (L : ObjectProperty 𝒜) [L.IsWeakSerreClass] (hi : ∀ X, L (i.obj X))
  [PreservesFiniteColimits (L.ι ⋙ Q)]

/-- The adjunction `i ⊣ Q` restricted to the subcategory `L` through which `i` factors. -/
def coreflectionAdjunction : L.lift i hi ⊣ L.ι ⋙ Q :=
  adj.restrictFullyFaithful (Functor.FullyFaithful.id _) L.fullyFaithfulι
    (i.leftUnitor ≪≫ (L.liftCompιIso i hi).symm) (Functor.rightUnitor _).symm

/-- **A coreflective subcategory through an exact coreflector on a weak Serre class is
abelian.**  This is `CategoryTheory.abelianOfCoreflection` applied to the coreflection of the
abelian category `L` (**Stacks 0754**) onto `𝒞`. -/
@[instance_reducible]
def abelianOfCoreflectionOnClass : Abelian 𝒞 :=
  abelianOfCoreflection (coreflectionAdjunction adj L hi)

/-- The short complex of `L` lying over a short complex of `𝒜` whose terms are in `L`. -/
@[simps]
def liftShortComplex (S : ShortComplex 𝒜) (h₁ : L S.X₁) (h₂ : L S.X₂) (h₃ : L S.X₃) :
    ShortComplex L.FullSubcategory where
  X₁ := ⟨S.X₁, h₁⟩
  X₂ := ⟨S.X₂, h₂⟩
  X₃ := ⟨S.X₃, h₃⟩
  f := ObjectProperty.homMk S.f
  g := ObjectProperty.homMk S.g
  zero := by ext; exact S.zero

/-- The lifted short complex maps back to the original one. -/
def liftShortComplexMapιIso (S : ShortComplex 𝒜) (h₁ : L S.X₁) (h₂ : L S.X₂) (h₃ : L S.X₃) :
    (liftShortComplex L S h₁ h₂ h₃).map L.ι ≅ S :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)

omit [Preadditive 𝒞] [i.Full] [i.Faithful] [Q.Additive] [PreservesFiniteColimits (L.ι ⋙ Q)] in
include adj in
/-- The functor `L ⥤ 𝒞` induced by `Q` is exact. -/
theorem preservesFiniteLimits_ι_comp : PreservesFiniteLimits (L.ι ⋙ Q) :=
  have := L.preservesFiniteLimits_ι_of_isWeakSerreClass
  have := adj.rightAdjoint_preservesLimits
  comp_preservesFiniteLimits _ _

/-- A short complex of `𝒜` with terms in `L` which is exact lifts to an exact one in `L`. -/
private theorem exact_liftShortComplex {S : ShortComplex 𝒜} (hS : S.Exact) (h₁ : L S.X₁)
    (h₂ : L S.X₂) (h₃ : L S.X₃) : (liftShortComplex L S h₁ h₂ h₃).Exact :=
  have := L.preservesFiniteLimits_ι_of_isWeakSerreClass
  have := L.preservesFiniteColimits_ι_of_isWeakSerreClass
  (ShortComplex.exact_map_iff_of_faithful _ L.ι).1
    (ShortComplex.exact_of_iso (liftShortComplexMapιIso L S h₁ h₂ h₃).symm hS)

include adj hi in
/-- **The coherator preserves short exact sequences whose terms lie in `L`.** -/
theorem shortExact_map_of_prop {S : ShortComplex 𝒜} (hS : S.ShortExact) (h₁ : L S.X₁)
    (h₂ : L S.X₂) (h₃ : L S.X₃) : (S.map Q).ShortExact := by
  let := abelianOfCoreflectionOnClass adj L hi
  have := preservesFiniteLimits_ι_comp adj L
  have := L.preservesFiniteLimits_ι_of_isWeakSerreClass
  have := L.preservesFiniteColimits_ι_of_isWeakSerreClass
  have := adj.isRightAdjoint
  have := hS.mono_f
  have := hS.epi_g
  exact (ShortComplex.ShortExact.mk' (exact_liftShortComplex L hS.exact h₁ h₂ h₃)
    (L.ι.mono_of_mono_map ‹_›) (L.ι.epi_of_epi_map ‹_›)).map_of_exact (L.ι ⋙ Q)

include adj hi in
/-- **The coherator preserves exactness of short complexes whose terms lie in `L`.** -/
theorem exact_map_of_prop {S : ShortComplex 𝒜} (hS : S.Exact) (h₁ : L S.X₁) (h₂ : L S.X₂)
    (h₃ : L S.X₃) : (S.map Q).Exact := by
  let := abelianOfCoreflectionOnClass adj L hi
  have := preservesFiniteLimits_ι_comp adj L
  have := L.preservesFiniteLimits_ι_of_isWeakSerreClass
  have := L.preservesFiniteColimits_ι_of_isWeakSerreClass
  have := adj.isRightAdjoint
  exact (exact_liftShortComplex L hS h₁ h₂ h₃).map (L.ι ⋙ Q)

omit [i.Full] [i.Faithful] in
include adj in
/-- If `j ≫ k = 0` with `j` a monomorphism and `Q k` a monomorphism, then `Q` kills the source
of `j`. -/
theorem isZero_obj_of_mono_of_comp_eq_zero {Z X Y : 𝒜} (j : Z ⟶ X) [Mono j] (k : X ⟶ Y)
    [Mono (Q.map k)] (h : j ≫ k = 0) : IsZero (Q.obj Z) := by
  have := adj.isRightAdjoint
  refine IsZero.of_mono_eq_zero (Q.map j) ?_
  rw [← cancel_mono (Q.map k), ← Q.map_comp, h, Q.map_zero, zero_comp]

omit [i.Full] [i.Faithful] [L.IsWeakSerreClass] in
include adj in
/-- Dually, if `k ≫ p = 0` with `p` an epimorphism between objects of `L` and `Q k` an
epimorphism, then `Q` kills the target of `p`. -/
theorem isZero_obj_of_epi_of_comp_eq_zero {X Y Z : 𝒜} (k : X ⟶ Y) (p : Y ⟶ Z) [Epi p]
    (hY : L Y) (hZ : L Z) [Epi (Q.map k)] (h : k ≫ p = 0) : IsZero (Q.obj Z) := by
  let p' : (⟨Y, hY⟩ : L.FullSubcategory) ⟶ ⟨Z, hZ⟩ := ObjectProperty.homMk p
  have : Epi (L.ι.map p') := ‹Epi p›
  have : Epi p' := L.ι.epi_of_epi_map this
  have : Epi (Q.map p) := ((L.ι ⋙ Q).map_epi p' :)
  refine IsZero.of_epi_eq_zero (Q.map p) ?_
  rw [← cancel_epi (Q.map k), ← Q.map_comp, h, Q.map_zero, comp_zero]

end Coreflection

section Transfer

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜]
  {𝒞 : Type u₂} [Category.{v₂} 𝒞] [Preadditive 𝒞]
  {ℬ : Type u₃} [Category.{v₃} ℬ] [Abelian ℬ]
  {𝒟 : Type u₄} [Category.{v₄} 𝒟] [Preadditive 𝒟]
  {i : 𝒞 ⥤ 𝒜} {Q : 𝒜 ⥤ 𝒞} (adj : i ⊣ Q) [i.Full] [i.Faithful] [Q.Additive]
  (L : ObjectProperty 𝒜) [L.IsWeakSerreClass] (hi : ∀ X, L (i.obj X))
  [PreservesFiniteColimits (L.ι ⋙ Q)]
  {i' : 𝒟 ⥤ ℬ} {Q' : ℬ ⥤ 𝒟} (adj' : i' ⊣ Q') [i'.Full] [i'.Faithful] [Q'.Additive]
  (L' : ObjectProperty ℬ) [L'.IsWeakSerreClass] (hi' : ∀ X, L' (i'.obj X))
  [PreservesFiniteColimits (L'.ι ⋙ Q')]
  (D : DeltaFunctor 𝒜 ℬ) (hD : ∀ X, L X → ∀ n, L' ((D.functor n).obj X))
  (hDQ : ∀ X, L X → IsZero (Q.obj X) → ∀ n, IsZero (Q'.obj ((D.functor n).obj X)))

omit [Preadditive 𝒞] [Q.Additive] [L.IsWeakSerreClass] [PreservesFiniteColimits (L.ι ⋙ Q)] in
include adj' hi' hD hDQ in
/-- If `0 → K → X → Y → 0` is short exact in `𝒜` with all terms in `L` and `Q` kills `K`, then
`Q' ∘ Dⁿ` inverts `X → Y` in every degree. -/
theorem isIso_map_map_g_of_isZero {S : ShortComplex 𝒜} (hS : S.ShortExact) (h₁ : L S.X₁)
    (h₂ : L S.X₂) (h₃ : L S.X₃) (hK : IsZero (Q.obj S.X₁)) (n : ℕ) :
    IsIso (Q'.map ((D.functor n).map S.g)) := by
  let := abelianOfCoreflectionOnClass adj' L' hi'
  have hz : ∀ m, IsZero (Q'.obj ((D.functor m).obj S.X₁)) := hDQ _ h₁ hK
  have e₁ := exact_map_of_prop adj' L' hi' (D.exact_map hS n) (hD _ h₁ n) (hD _ h₂ n)
    (hD _ h₃ n)
  have e₂ := exact_map_of_prop adj' L' hi' (D.exact_δ₁ hS n) (hD _ h₂ n) (hD _ h₃ n)
    (hD _ h₁ (n + 1))
  have : Mono (Q'.map ((D.functor n).map S.g)) := e₁.mono_g ((hz n).eq_of_src _ _)
  have : Epi (Q'.map ((D.functor n).map S.g)) := e₂.epi_f ((hz (n + 1)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

omit [Preadditive 𝒞] [Q.Additive] [L.IsWeakSerreClass] [PreservesFiniteColimits (L.ι ⋙ Q)] in
include adj' hi' hD hDQ in
/-- If `0 → X → Y → C → 0` is short exact in `𝒜` with all terms in `L` and `Q` kills `C`, then
`Q' ∘ Dⁿ` inverts `X → Y` in every degree. -/
theorem isIso_map_map_f_of_isZero {S : ShortComplex 𝒜} (hS : S.ShortExact) (h₁ : L S.X₁)
    (h₂ : L S.X₂) (h₃ : L S.X₃) (hC : IsZero (Q.obj S.X₃)) (n : ℕ) :
    IsIso (Q'.map ((D.functor n).map S.f)) := by
  let := abelianOfCoreflectionOnClass adj' L' hi'
  have := adj'.isRightAdjoint
  have hz : ∀ m, IsZero (Q'.obj ((D.functor m).obj S.X₃)) := hDQ _ h₃ hC
  have e₁ := exact_map_of_prop adj' L' hi' (D.exact_map hS n) (hD _ h₁ n) (hD _ h₂ n)
    (hD _ h₃ n)
  have : Epi (Q'.map ((D.functor n).map S.f)) := e₁.epi_f ((hz n).eq_of_tgt _ _)
  have : Mono (Q'.map ((D.functor n).map S.f)) := by
    cases n with
    | zero =>
      have := D.mono_map_f hS
      infer_instance
    | succ m =>
      have e₂ := exact_map_of_prop adj' L' hi' (D.exact_δ₂ hS m) (hD _ h₃ m)
        (hD _ h₁ (m + 1)) (hD _ h₂ (m + 1))
      exact e₂.mono_g ((hz m).eq_of_src _ _)
  exact isIso_of_mono_of_epi _

omit [i.Full] [i.Faithful] in
include adj hi adj' hi' hD hDQ in
/-- **`Q' ∘ Dⁿ` inverts every morphism of `L` which `Q` inverts.**  The kernel and the cokernel
of such a morphism lie in `L` and are killed by `Q`, so the two halves of its image
factorisation are inverted by `Q' ∘ Dⁿ`, by the long exact sequences of `D`. -/
theorem isIso_map_map_of_isIso_map {X Y : 𝒜} (k : X ⟶ Y) (hX : L X) (hY : L Y)
    [IsIso (Q.map k)] (n : ℕ) : IsIso (Q'.map ((D.functor n).map k)) := by
  have hI : L (Abelian.image k) := L.prop_kernel _ hY (L.prop_cokernel _ hX hY)
  have hK : L (kernel (Abelian.factorThruImage k)) := L.prop_kernel _ hX hI
  have hC : L (cokernel (Abelian.image.ι k)) := L.prop_cokernel _ hI hY
  have z1 : IsZero (Q.obj (kernel (Abelian.factorThruImage k))) :=
    isZero_obj_of_mono_of_comp_eq_zero adj (kernel.ι (Abelian.factorThruImage k)) k
        ((kernel.ι _ ≫= Abelian.image.fac k).symm.trans
          (by rw [kernel.condition_assoc, zero_comp]))
  have z2 : IsZero (Q.obj (cokernel (Abelian.image.ι k))) :=
    isZero_obj_of_epi_of_comp_eq_zero adj L k (cokernel.π (Abelian.image.ι k)) hY hC
        ((Abelian.image.fac k =≫ cokernel.π (Abelian.image.ι k)).symm.trans
          (by rw [Category.assoc, cokernel.condition, comp_zero]))
  have h₁ : IsIso (Q'.map ((D.functor n).map (Abelian.factorThruImage k))) :=
    isIso_map_map_g_of_isZero (L := L) (adj' := adj') (L' := L') (hi' := hi') (D := D) (hD := hD)
      (hDQ := hDQ) (S := ShortComplex.kernelSequence (Abelian.factorThruImage k))
      (ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact _)
        inferInstance (inferInstance : Epi (Abelian.factorThruImage k))) hK hX hI z1 n
  have h₂ : IsIso (Q'.map ((D.functor n).map (Abelian.image.ι k))) :=
    isIso_map_map_f_of_isZero (L := L) (adj' := adj') (L' := L') (hi' := hi') (D := D) (hD := hD)
      (hDQ := hDQ) (S := ShortComplex.cokernelSequence (Abelian.image.ι k))
      (ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact _)
        (inferInstance : Mono (Abelian.image.ι k)) inferInstance) hI hY hC z2 n
  rw [← Abelian.image.fac k, Functor.map_comp, Functor.map_comp]
  infer_instance

end Transfer

section Construction

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜]
  {𝒞 : Type u₂} [Category.{v₂} 𝒞] [Preadditive 𝒞]
  {ℬ : Type u₃} [Category.{v₃} ℬ] [Abelian ℬ]
  {𝒟 : Type u₄} [Category.{v₄} 𝒟] [Preadditive 𝒟]
  {i : 𝒞 ⥤ 𝒜} {Q : 𝒜 ⥤ 𝒞} (adj : i ⊣ Q) [i.Full] [i.Faithful] [i.Additive] [Q.Additive]
  (L : ObjectProperty 𝒜) [L.IsWeakSerreClass] (hi : ∀ X, L (i.obj X))
  [PreservesFiniteColimits (L.ι ⋙ Q)]
  {i' : 𝒟 ⥤ ℬ} {Q' : ℬ ⥤ 𝒟} (adj' : i' ⊣ Q') [i'.Full] [i'.Faithful] [Q'.Additive]
  (L' : ObjectProperty ℬ) [L'.IsWeakSerreClass] (hi' : ∀ X, L' (i'.obj X))
  [PreservesFiniteColimits (L'.ι ⋙ Q')]
  (D : DeltaFunctor 𝒜 ℬ) (hD : ∀ X, L X → ∀ n, L' ((D.functor n).obj X))
  (hDQ : ∀ X, L X → IsZero (Q.obj X) → ∀ n, IsZero (Q'.obj ((D.functor n).obj X)))

/-- The comparison `i F₁ ⟶ Ker(i F₂ ⟶ i F₃)` attached to a short complex of `𝒞`. -/
def coreflectionComparison (S : ShortComplex 𝒞) : i.obj S.X₁ ⟶ kernel (i.map S.g) :=
  kernel.lift _ (i.map S.f) (by rw [← i.map_comp, S.zero, i.map_zero])

omit [i.Full] [i.Faithful] in
/-- The comparison `i F₁ ⟶ Ker(i F₂ ⟶ i F₃)` followed by the kernel inclusion is `i.map S.f`. -/
@[reassoc (attr := simp)]
theorem coreflectionComparison_ι (S : ShortComplex 𝒞) :
    coreflectionComparison (i := i) S ≫ kernel.ι (i.map S.g) = i.map S.f :=
  kernel.lift_ι _ _ _

/-- The short complex `Ker(i F₂ → i F₃) → i F₂ → i F₃` of `𝒜` attached to a short complex of
`𝒞`. -/
abbrev coreflectionKernelSequence (S : ShortComplex 𝒞) : ShortComplex 𝒜 where
  X₁ := kernel (i.map S.g)
  X₂ := i.obj S.X₂
  X₃ := i.obj S.X₃
  f := kernel.ι (i.map S.g)
  g := i.map S.g
  zero := kernel.condition _

omit [i.Full] [i.Faithful] [i.Additive] in
include hi in
/-- The kernel `Ker(i F₂ → i F₃)` lies in `L`, which is closed under kernels. -/
theorem prop_coreflectionKernelSequence_X₁ (S : ShortComplex 𝒞) :
    L (coreflectionKernelSequence (i := i) S).X₁ :=
  L.prop_kernel _ (hi _) (hi _)

omit [i.Full] [i.Faithful] [i.Additive] [Q.Additive] in
include adj in
/-- For a short exact sequence `0 → F₁ → F₂ → F₃ → 0` of `𝒞`, the sequence
`0 → Ker(i F₂ → i F₃) → i F₂ → i F₃ → 0` is short exact in `𝒜`: `i` preserves epimorphisms,
being a left adjoint. -/
theorem shortExact_coreflectionKernelSequence {S : ShortComplex 𝒞} (hS : S.ShortExact) :
    (coreflectionKernelSequence (i := i) S).ShortExact := by
  have := adj.isLeftAdjoint
  have := hS.epi_g
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ ?_)
    (inferInstance : Mono (kernel.ι (i.map S.g))) (inferInstance : Epi (i.map S.g))
  exact KernelFork.IsLimit.ofι _ _ (fun g hg => kernel.lift _ g hg)
    (fun g hg => kernel.lift_ι _ g hg)
    (fun g hg m hm => (cancel_mono (kernel.ι (i.map S.g))).1 ((kernel.lift_ι _ g hg).symm ▸ hm))

include adj hi in
/-- **The coherator inverts the comparison `i F₁ ⟶ Ker(i F₂ → i F₃)`** of a short complex of `𝒞`
which is exact with `F₁ ⟶ F₂` a monomorphism: the coherator preserves kernels and
`Q ∘ i ≅ 𝟭`. -/
theorem isIso_map_coreflectionComparison_of_exact {S : ShortComplex 𝒞} (hS : S.Exact)
    [Mono S.f] : IsIso (Q.map (coreflectionComparison (i := i) S)) := by
  let := abelianOfCoreflectionOnClass adj L hi
  have := adj.isRightAdjoint
  have hf : Q.map (i.map S.f) = inv (adj.unit.app S.X₁) ≫ S.f ≫ adj.unit.app S.X₂ := by
    rw [IsIso.eq_inv_comp]
    exact (adj.unit.naturality S.f).symm
  have : Mono (Q.map (i.map S.f)) := by rw [hf]; infer_instance
  let T : ShortComplex 𝒞 := S.map (i ⋙ Q)
  have hT : T.Exact := ShortComplex.exact_of_iso (S.mapNatIso (asIso adj.unit)) hS
  have : Mono T.f := ‹Mono (Q.map (i.map S.f))›
  have hk : Q.map (kernel.ι (i.map S.g)) ≫ T.g = 0 := by
    change Q.map _ ≫ Q.map _ = 0
    rw [← Q.map_comp, kernel.condition, Q.map_zero]
  have hl : hT.lift _ hk ≫ Q.map (i.map S.f) = Q.map (kernel.ι (i.map S.g)) := hT.lift_f _ hk
  refine ⟨hT.lift _ hk, ?_, ?_⟩
  · rw [← cancel_mono (Q.map (i.map S.f)), Category.assoc, hl, ← Q.map_comp,
      coreflectionComparison_ι, Category.id_comp]
  · rw [← cancel_mono (Q.map (kernel.ι (i.map S.g))), Category.assoc, ← Q.map_comp,
      coreflectionComparison_ι, Category.id_comp, hl]

include adj hi in
/-- **The coherator inverts the comparison `i F₁ ⟶ Ker(i F₂ → i F₃)`** of a short exact sequence
of `𝒞`. -/
theorem isIso_map_coreflectionComparison {S : ShortComplex 𝒞} (hS : S.ShortExact) :
    IsIso (Q.map (coreflectionComparison (i := i) S)) :=
  have := hS.mono_f
  isIso_map_coreflectionComparison_of_exact adj L hi hS.exact

include adj hi adj' hi' hD hDQ in
/-- `Q' ∘ Dⁿ` inverts the comparison `i F₁ ⟶ Ker(i F₂ → i F₃)` of a short exact sequence of
`𝒞`, in every degree. -/
theorem isIso_map_map_coreflectionComparison {S : ShortComplex 𝒞} (hS : S.ShortExact) (n : ℕ) :
    IsIso (Q'.map ((D.functor n).map (coreflectionComparison (i := i) S))) :=
  have := isIso_map_coreflectionComparison adj L hi hS
  isIso_map_map_of_isIso_map adj L hi adj' L' hi' D hD hDQ _ (hi _)
    (L.prop_kernel _ (hi _) (hi _)) n

include adj hi adj' hi' hD hDQ in
/-- The connecting morphism of `n ↦ i ⋙ Dⁿ ⋙ Q'` at a short exact sequence of `𝒞`: the image
under `Q'` of the connecting morphism of `D` at `0 → Ker(i F₂ → i F₃) → i F₂ → i F₃ → 0`,
followed by the inverse of `Q' Dⁿ⁺¹` of the comparison `i F₁ ⟶ Ker(i F₂ → i F₃)`. -/
def coreflectionδ {S : ShortComplex 𝒞} (hS : S.ShortExact) (n : ℕ) :
    Q'.obj ((D.functor n).obj (i.obj S.X₃)) ⟶ Q'.obj ((D.functor (n + 1)).obj (i.obj S.X₁)) :=
  Q'.map (D.δ (shortExact_coreflectionKernelSequence adj hS) n) ≫
    inv (I := isIso_map_map_coreflectionComparison adj L hi adj' L' hi' D hD hDQ hS (n + 1))
      (Q'.map ((D.functor (n + 1)).map (coreflectionComparison (i := i) S)))

include adj hi adj' hi' hD hDQ in
/-- The connecting morphism `coreflectionδ` followed by the image under `Q' Dⁿ⁺¹` of the
comparison `i F₁ ⟶ Ker(i F₂ → i F₃)` is the image under `Q'` of the connecting morphism of `D`
at `0 → Ker(i F₂ → i F₃) → i F₂ → i F₃ → 0`. -/
@[reassoc]
theorem coreflectionδ_comp {S : ShortComplex 𝒞} (hS : S.ShortExact) (n : ℕ) :
    coreflectionδ adj L hi adj' L' hi' D hD hDQ hS n ≫
        Q'.map ((D.functor (n + 1)).map (coreflectionComparison (i := i) S)) =
      Q'.map (D.δ (shortExact_coreflectionKernelSequence adj hS) n) := by
  have := isIso_map_map_coreflectionComparison adj L hi adj' L' hi' D hD hDQ hS (n + 1)
  simp [coreflectionδ]

include adj hi adj' hi' hD hDQ in
/-- **The δ-functor `n ↦ i ⋙ Dⁿ ⋙ Q'`** (**Stacks 010Q**): a cohomological δ-functor
`D : 𝒜 ⥤ ℬ` carrying the weak Serre class `L` into `L'`, and objects of `L` killed by `Q` to
objects killed by `Q'`, induces one between the coreflective subcategories `𝒞` and `𝒟`.  Its
connecting morphism is `CategoryTheory.DeltaFunctor.coreflectionδ`. -/
def ofCoreflections : DeltaFunctor 𝒞 𝒟 where
  functor n := i ⋙ D.functor n ⋙ Q'
  additive _ := inferInstance
  δ hS n := coreflectionδ adj L hi adj' L' hi' D hD hDQ hS n
  map_g_δ {S} hS n := by
    dsimp only [Functor.comp_map]
    rw [coreflectionδ, ← Category.assoc, ← Q'.map_comp]
    exact (congrArg (· ≫ _) (congrArg Q'.map
      (D.map_g_δ (shortExact_coreflectionKernelSequence adj hS) n))).trans (by simp)
  δ_map_f {S} hS n := by
    dsimp only [Functor.comp_map]
    rw [← coreflectionComparison_ι, Functor.map_comp, Functor.map_comp, coreflectionδ_comp_assoc,
      ← Q'.map_comp]
    exact (congrArg Q'.map (D.δ_map_f (shortExact_coreflectionKernelSequence adj hS) n)).trans
      (Q'.map_zero _ _)
  mono_map_f {S} hS := by
    have := adj'.isRightAdjoint
    have := isIso_map_map_coreflectionComparison adj L hi adj' L' hi' D hD hDQ hS 0
    have := D.mono_map_f (shortExact_coreflectionKernelSequence adj hS)
    dsimp only [Functor.comp_map]
    rw [← coreflectionComparison_ι, Functor.map_comp, Functor.map_comp]
    exact mono_comp _ (Q'.map ((D.functor 0).map (kernel.ι (i.map S.g))))
  exact_map {S} hS n := by
    have := isIso_map_map_coreflectionComparison adj L hi adj' L' hi' D hD hDQ hS n
    have hT := shortExact_coreflectionKernelSequence adj hS
    have hK := L.prop_kernel (i.map S.g) (hi _) (hi _)
    refine ShortComplex.exact_of_iso (ShortComplex.isoMk
      (S₁ := ((coreflectionKernelSequence (i := i) S).map (D.functor n)).map Q')
      (asIso (Q'.map ((D.functor n).map (coreflectionComparison (i := i) S)))).symm
      (Iso.refl _) (Iso.refl _) ?_ ?_)
      (exact_map_of_prop adj' L' hi' (D.exact_map hT n) (hD _ hK n) (hD _ (hi _) n)
        (hD _ (hi _) n))
    · dsimp
      rw [IsIso.inv_comp_eq, Category.comp_id, ← Functor.map_comp, ← Functor.map_comp,
        coreflectionComparison_ι]
    · simp
  exact_δ₁ {S} hS n := by
    have := isIso_map_map_coreflectionComparison adj L hi adj' L' hi' D hD hDQ hS (n + 1)
    have hT := shortExact_coreflectionKernelSequence adj hS
    have hK := L.prop_kernel (i.map S.g) (hi _) (hi _)
    refine ShortComplex.exact_of_iso (ShortComplex.isoMk
      (S₁ := (ShortComplex.mk _ _ (D.map_g_δ hT n)).map Q') (Iso.refl _) (Iso.refl _)
      (asIso (Q'.map ((D.functor (n + 1)).map (coreflectionComparison (i := i) S)))).symm
      ?_ ?_)
      (exact_map_of_prop adj' L' hi' (D.exact_δ₁ hT n) (hD _ (hi _) n) (hD _ (hi _) n)
        (hD _ hK (n + 1)))
    · simp
    · dsimp
      rw [Category.id_comp, coreflectionδ]
  exact_δ₂ {S} hS n := by
    have := isIso_map_map_coreflectionComparison adj L hi adj' L' hi' D hD hDQ hS (n + 1)
    have hT := shortExact_coreflectionKernelSequence adj hS
    have hK := L.prop_kernel (i.map S.g) (hi _) (hi _)
    refine ShortComplex.exact_of_iso (ShortComplex.isoMk
      (S₁ := (ShortComplex.mk _ _ (D.δ_map_f hT n)).map Q') (Iso.refl _)
      (asIso (Q'.map ((D.functor (n + 1)).map (coreflectionComparison (i := i) S)))).symm
      (Iso.refl _) ?_ ?_)
      (exact_map_of_prop adj' L' hi' (D.exact_δ₂ hT n) (hD _ (hi _) n) (hD _ hK (n + 1))
        (hD _ (hi _) (n + 1)))
    · dsimp
      rw [Category.id_comp, coreflectionδ]
    · dsimp
      rw [IsIso.inv_comp_eq, Category.comp_id, ← Functor.map_comp, ← Functor.map_comp,
        coreflectionComparison_ι]
  δ_naturality {S T} hS hT φ n := by
    have := isIso_map_map_coreflectionComparison adj L hi adj' L' hi' D hD hDQ hT (n + 1)
    let κ : kernel (i.map S.g) ⟶ kernel (i.map T.g) :=
      kernel.map _ _ (i.map φ.τ₂) (i.map φ.τ₃) (by rw [← i.map_comp, ← i.map_comp, φ.comm₂₃])
    let ψ : coreflectionKernelSequence (i := i) S ⟶ coreflectionKernelSequence (i := i) T :=
      { τ₁ := κ
        τ₂ := i.map φ.τ₂
        τ₃ := i.map φ.τ₃
        comm₁₂ := kernel.lift_ι _ _ _
        comm₂₃ := by
          change i.map φ.τ₂ ≫ i.map T.g = i.map S.g ≫ i.map φ.τ₃
          rw [← i.map_comp, ← i.map_comp, φ.comm₂₃] }
    have hκ : coreflectionComparison (i := i) S ≫ κ =
        i.map φ.τ₁ ≫ coreflectionComparison (i := i) T := by
      rw [← cancel_mono (kernel.ι (i.map T.g)), Category.assoc, Category.assoc,
        coreflectionComparison_ι]
      change _ ≫ kernel.map _ _ _ _ _ ≫ _ = _
      rw [kernel.lift_ι, coreflectionComparison_ι_assoc, ← i.map_comp, ← i.map_comp, φ.comm₁₂]
    dsimp only [Functor.comp_map]
    have key : Q'.map ((D.functor (n + 1)).map (i.map φ.τ₁)) ≫
        Q'.map ((D.functor (n + 1)).map (coreflectionComparison (i := i) T)) =
        Q'.map ((D.functor (n + 1)).map (coreflectionComparison (i := i) S)) ≫
          Q'.map ((D.functor (n + 1)).map κ) := by
      simp only [← Q'.map_comp, ← Functor.map_comp, hκ]
    rw [← cancel_mono (Q'.map ((D.functor (n + 1)).map (coreflectionComparison (i := i) T))),
      Category.assoc, coreflectionδ_comp, Category.assoc, key, coreflectionδ_comp_assoc,
      ← Q'.map_comp, ← Q'.map_comp]
    exact congrArg Q'.map (D.δ_naturality (shortExact_coreflectionKernelSequence adj hS)
      (shortExact_coreflectionKernelSequence adj hT) ψ n)

/-- The `n`-th functor of `ofCoreflections` is `i ⋙ Dⁿ ⋙ Q'`. -/
@[simp]
theorem ofCoreflections_functor (n : ℕ) :
    (ofCoreflections adj L hi adj' L' hi' D hD hDQ).functor n = i ⋙ D.functor n ⋙ Q' :=
  rfl

end Construction

end CategoryTheory.DeltaFunctor
