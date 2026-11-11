module

public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import StacksFrontier.Cotangent.ConormalLowDegree
public import StacksFrontier.Cotangent.SimplicialModuleOverTensor
public import StacksFrontier.Cotangent.StandardResolutionExactness
public import StacksFrontier.Cotangent.TorTwoQuotientSelf

/-!
# The differential `H₂(C_{B/A}, 𝒥/𝒥²) → H₀(C_{B/A}, Tor₁^𝒪(𝒥, B̲))` (Stacks 09D5)

Let `A → B` be a ring map, and on `C_{B/A}` let `𝒥 = ker(𝒪 → B̲)` as in Remark 08R7. Remark 09D5
asserts that the differential

```
H₂(C_{B/A}, 𝒥/𝒥²) ⟶ H₀(C_{B/A}, Tor₁^𝒪(𝒥, B̲))
```

of the spectral sequence of Remark 08R7 is an isomorphism, and, combining with the isomorphism
`H₂(C_{B/A}, 𝒥/𝒥²) ≅ H₂(L_{B/A})` (registered in
`StacksFrontier/Cotangent/SurjectivePresentationHigherHomology.lean`), that
`H₂(L_{B/A}) = H₀(C_{B/A}, Tor₁^𝒪(𝒥, B̲))`. The spectral sequence of Remark 08R7 is not
constructed here: its differential `d₂` is modelled as the composite of two connecting maps
(see the implementation notes for why this composite is `d₂` up to the sign convention; that
identification is argued in prose, not proved in Lean). This file proves that the composite is an
isomorphism, and the resulting formula for `H₂(L_{B/A})`.

As in the other registrations of Tag 09D5, homology on `C_{B/A}` is read on the standard
resolution `P_• → B` (Tag 08PS): the homology `H_n(C_{B/A}, ℱ)` of a sheaf of `𝒪`-modules `ℱ`
is the homology of the Moore complex of the simplicial module `n ↦ ℱ(Pₙ → B)`. Every sheaf in
the argument is evaluated there: `𝒥` is `n ↦ Jₙ = ker(Pₙ → B)`
(`Stacks.Cotangent.augmentationIdealModule`), `𝒥²` is `n ↦ Jₙ²`, `𝒥 ⊗_𝒪 𝒥` is
`n ↦ Jₙ ⊗_{Pₙ} Jₙ`, `𝒥/𝒥²` is `Stacks.Cotangent.conormalSimplicialModule`, and
`Tor₁^𝒪(𝒥, B̲)` is `n ↦ Tor₁^{Pₙ}(Jₙ, B) = ker(Jₙ ⊗_{Pₙ} Jₙ → Jₙ²)`
(`Stacks.Cotangent.torOneSimplicial`; the identification with Mathlib's `Tor'` is
`Stacks.Cotangent.torOneSimplicialObjIsoTor`, from `torOneIdealIsoMulKernel` of Tag 09D6). On a
chaotic site sheaves are presheaves, `Tor_q^𝒪(𝒥, B̲)` is computed sectionwise, and so these are
the sheaves of the source.

## Main definitions

* `Stacks.Cotangent.torOneSimplicial` and `Stacks.Cotangent.torOneMooreComplex`:
  `Tor₁^𝒪(𝒥, B̲)` on the standard resolution and its Moore complex.
* `Stacks.Cotangent.conormalTorOneDifferential`: the differential
  `H₂(C_{B/A}, 𝒥/𝒥²) → H₀(C_{B/A}, Tor₁^𝒪(𝒥, B̲))`.
* `Stacks.Cotangent.cotangentComplexHomologyTwoIsoTorOne`:
  `H₂(L_{B/A}) ≅ H₀(C_{B/A}, Tor₁^𝒪(𝒥, B̲))` as `A`-modules; the `B`-linear form, which is the
  one registered for Tag 09D5, is in `StacksFrontier/Cotangent/ConormalTorDifferentialLinear.lean`.

## Main results

* `Stacks.Cotangent.isIso_conormalTorOneDifferential`: **Stacks 09D5**, the differential is an
  isomorphism.
* `Stacks.Cotangent.isZero_homology_augmentationIdeal`: `H_*(C_{B/A}, 𝒥) = 0`, the vanishing
  `Lπ_!(𝒥) = 0` of Remark 08R7, from the standard resolution being a resolution.
* `Stacks.Cotangent.isZero_homology_zero_idealTensorIdeal` and
  `Stacks.Cotangent.isZero_homology_one_idealTensorIdeal`: `H₀` and `H₁` of `𝒥 ⊗_𝒪 𝒥` vanish.

## Implementation notes

**The differential, and why it models the one of the spectral sequence.** The following is
an informal argument; the spectral sequence is not built in Lean, so the identification below is
not a formal theorem. The spectral sequence of
Remark 08R7 is the hyperhomology spectral sequence of `Lπ_!` for `K = 𝒥 ⊗^L_𝒪 B̲` and the
filtration of `K` by its canonical truncations, `E²_{p,q} = H_p(C_{B/A}, H_q(K))` with
`H_q(K) = Tor_q^𝒪(𝒥, B̲)`. For such a spectral sequence the differential
`d₂ : E²_{p,0} → E²_{p-2,1}` is the map that `H_p(C_{B/A}, -)` induces from the extension class
`H₀(K) → H₁(K)[2]` of the two-step truncation `τ_{≤ 1}K`, and on homology the action of an
extension class represented by a `2`-extension `0 → H₁ → X₁ → X₀ → H₀ → 0` is the composite of
the connecting maps of its two short exact pieces. Here `τ_{≤ 1}K` is represented by the
two-term complex `𝒥 ⊗_𝒪 𝒥 → 𝒥` (multiplication): `𝒪` is flat, so
`K = cone(𝒥 ⊗^L_𝒪 𝒥 → 𝒥)`, and replacing `𝒥 ⊗^L_𝒪 𝒥` by `𝒥 ⊗_𝒪 𝒥` changes neither `H₀` nor
`H₁` of the cone. Its `2`-extension is
`0 → Tor₁^𝒪(𝒥, B̲) → 𝒥 ⊗_𝒪 𝒥 → 𝒥 → 𝒥/𝒥² → 0`, whose short exact pieces are
`0 → 𝒥² → 𝒥 → 𝒥/𝒥² → 0` and `0 → Tor₁^𝒪(𝒥, B̲) → 𝒥 ⊗_𝒪 𝒥 → 𝒥² → 0`. So `d₂` (up to the sign
convention for the differentials) is the composite of the two connecting maps

```
H₂(C_{B/A}, 𝒥/𝒥²) ⟶ H₁(C_{B/A}, 𝒥²) ⟶ H₀(C_{B/A}, Tor₁^𝒪(𝒥, B̲)),
```

and this composite is `Stacks.Cotangent.conormalTorOneDifferential`. The source's argument —
the abutment vanishes, so nothing can survive in total degrees `1` and `2` — becomes the
vanishing that makes each connecting map an isomorphism: the first is one because
`H₂(C_{B/A}, 𝒥) = H₁(C_{B/A}, 𝒥) = 0`, the second because
`H₁(C_{B/A}, 𝒥 ⊗_𝒪 𝒥) = H₀(C_{B/A}, 𝒥 ⊗_𝒪 𝒥) = 0`.

**The vanishing for `𝒥 ⊗_𝒪 𝒥`.** `H₀` vanishes because `H₀(𝒥)` does: a pure tensor `x ⊗ y` of
degree `0` is the boundary of `u ⊗ σ₀ y` for any `u` bounding `x`. For `H₁`, `𝒥` is covered by
`𝒦 = P_• ⊗_A decRed(𝒥)`, where `decRed(𝒥)` is the reduced décalage of `𝒥`, which covers `𝒥`
because `H₀(𝒥) = 0` and is simplicially contractible. Then `𝒥 ⊗_𝒪 𝒦 = 𝒥 ⊗_A decRed(𝒥)` is
acyclic — a simplicial contraction survives the degreewise tensor product — and the kernel of
`𝒥 ⊗_𝒪 𝒦 → 𝒥 ⊗_𝒪 𝒥` is spanned by the tensors `y ⊗ w` with `w` in the kernel of `𝒦 → 𝒥`
(right exactness of `⊗`), each of which is the boundary of `u ⊗ σ₀ w`. So that kernel has
vanishing `H₀`, and the long exact sequence gives `H₁(𝒥 ⊗_𝒪 𝒥) = 0`. This is the input the
source takes from the convergence `H_*(C_{B/A}, 𝒥 ⊗^L_𝒪 B̲) = 0`; it is proved here directly,
with no flatness of `𝒥` over `𝒪`, which fails in general.

**Linearity.** Everything here is stated for simplicial `A`-modules, and the two homology groups
of `B`-modules are read as `A`-modules by restriction of scalars along `A → B`. Being an
isomorphism does not depend on the ring of scalars, so this is all the first clause needs; for
the formula, which is an identification of `B`-modules, the same argument is run over `P₀` in
`StacksFrontier/Cotangent/ConormalTorDifferentialLinear.lean`, which gives the `B`-linear
isomorphism.

## References

* [Stacks Project, Tag 09D5](https://stacks.math.columbia.edu/tag/09D5)
* [Stacks Project, Tag 08R7](https://stacks.math.columbia.edu/tag/08R7)
* [Stacks Project, Tag 08PS](https://stacks.math.columbia.edu/tag/08PS)
* [Stacks Project, Tag 015J](https://stacks.math.columbia.edu/tag/015J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite Simplicial AlgebraicTopology
open scoped TensorProduct

universe u v

namespace Stacks.Cotangent

open CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)

/-! ### The augmentation ideal as a simplicial module over the standard resolution -/

/-- A simplicial operator of the standard resolution preserves the augmentation ideal. -/
theorem map_mem_augmentationIdeal {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (x : (standardResolution A B).left.obj n) (hx : x ∈ augmentationIdeal A B n) :
    ((standardResolution A B).left.map f).hom x ∈ augmentationIdeal A B m := by
  rw [mem_augmentationIdeal_iff] at hx ⊢
  have h := ConcreteCategory.congr_hom ((standardResolution A B).hom.naturality f) x
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at h
  rwa [← hx]

/-- The augmentation ideal `𝒥 = ker(P_• → B)` of the standard resolution, as a simplicial module
over the standard resolution: in degree `n` it is `Jₙ = ker(Pₙ → B)`. -/
abbrev augmentationIdealModule : SimplicialModuleOver (standardResolution A B).left where
  obj n := augmentationIdeal A B n
  map f :=
    { toFun := fun x => ⟨((standardResolution A B).left.map f).hom x.1,
        map_mem_augmentationIdeal.{u, v} A B f x.1 x.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x.1 y.1) }
  map_smul f p x := Subtype.ext (map_mul _ p x.1)
  map_id n x := Subtype.ext (by simp)
  map_comp f g x := Subtype.ext (by simp)

/-- The simplicial operators of `𝒥` are those of the standard resolution. -/
@[simp]
theorem augmentationIdealModule_map_val {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (x : (augmentationIdealModule.{u, v} A B).obj n) :
    ((augmentationIdealModule.{u, v} A B).map f x).1 =
      ((standardResolution A B).left.map f).hom x.1 :=
  rfl

/-- The forgetful functor from commutative `A`-algebras to `A`-modules. -/
abbrev forgetToModule : CommAlgCat.{max u v} A ⥤ ModuleCat.{max u v} A :=
  forget₂ (CommAlgCat.{max u v} A) (AlgCat.{max u v} A) ⋙
    forget₂ (AlgCat.{max u v} A) (ModuleCat.{max u v} A)

/-- The short complex `𝒥 → P_• → B` of simplicial `A`-modules. -/
def augmentationIdealShortComplex : ShortComplex (SimplicialObject (ModuleCat.{max u v} A)) where
  X₁ := (augmentationIdealModule.{u, v} A B).toSimplicial
  X₂ := (standardResolution A B).left ⋙ forgetToModule.{u, v} A
  X₃ := (SimplicialObject.const _).obj (standardResolution A B).right ⋙ forgetToModule.{u, v} A
  f :=
    { app := fun n => ModuleCat.ofHom
        ((augmentationIdeal A B n).subtype.restrictScalars A)
      naturality := fun _ _ _ => rfl }
  g := Functor.whiskerRight (standardResolution A B).hom (forgetToModule.{u, v} A)
  zero := by
    refine NatTrans.ext (funext fun n => ?_)
    ext x
    exact x.2

/-- `0 → Jₙ → Pₙ → B → 0` is exact in every degree, the augmentation being surjective. -/
theorem augmentationIdealShortComplex_shortExact_app (n : SimplexCategoryᵒᵖ) :
    ((augmentationIdealShortComplex.{u, v} A B).map
      ((evaluation SimplexCategoryᵒᵖ (ModuleCat.{max u v} A)).obj n)).ShortExact where
  exact := (ShortComplex.moduleCat_exact_iff _).2 fun x hx =>
    ⟨(⟨x, hx⟩ : augmentationIdeal A B n), rfl⟩
  mono_f := (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
  epi_g := (ModuleCat.epi_iff_surjective _).2
    (surjective_standardResolutionAugmentationHom.{u, v} A B n)

attribute [local instance] Functor.preservesHomologyOfExact

/-- A morphism of simplicial `A`-modules induces a quasi-isomorphism of Moore complexes exactly
when it does so after forgetting to abelian groups. -/
private lemma quasiIso_alternatingFaceMapComplex_forget₂_iff
    {X Y : SimplicialObject (ModuleCat.{max u v} A)} (g : X ⟶ Y) :
    QuasiIso ((alternatingFaceMapComplex (ModuleCat.{max u v} A)).map g) ↔
      QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{max u v}).map
        (Functor.whiskerRight g (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v}))) := by
  have hiso := alternatingFaceMapComplexCompMapHomologicalComplexIso
    (C := ModuleCat.{max u v} A) (D := AddCommGrpCat.{max u v})
    (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v})
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    ((alternatingFaceMapComplex (ModuleCat.{max u v} A)).map g)
    (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v})]
  exact quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (hiso.app X) (hiso.app Y) (hiso.hom.naturality g).symm)

/-- The augmentation `P_• → B` is a quasi-isomorphism on Moore complexes of `A`-modules: the
standard resolution is a resolution. -/
theorem quasiIso_augmentationIdealShortComplex_g :
    QuasiIso ((augmentationIdealShortComplex.{u, v} A B).map
      (alternatingFaceMapComplex (ModuleCat.{max u v} A))).g := by
  have hsurj : ∀ m : SimplexCategoryᵒᵖ,
      Function.Surjective ((standardResolution A B).hom.app m).hom := by
    intro m
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = op ⦋k⦌ := ⟨m.unop.len, rfl⟩
    exact surjective_standardResolution_augmentation A B k
  have hquasi : QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{max u v}).map
      (Functor.whiskerRight (standardResolution A B).hom (forgetToAddCommGrp.{u, v} A))) :=
    ((isResolution_quasiIso_homotopyEquivalence_tfae A B (standardResolution A B).left
      (standardResolution A B).hom (standardResolution_obj_isPolynomialAlgebra A B)
      hsurj).out 1 2).mp (standardResolution_isResolution.{u, v} A B)
  exact (quasiIso_alternatingFaceMapComplex_forget₂_iff A _).2 hquasi

/-- The short complex `𝒥 → P_• → B` is short exact on Moore complexes. -/
theorem augmentationIdealShortComplex_moore_shortExact :
    ((augmentationIdealShortComplex.{u, v} A B).map
      (alternatingFaceMapComplex (ModuleCat.{max u v} A))).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i =>
    augmentationIdealShortComplex_shortExact_app.{u, v} A B (op ⦋i⦌)

/-- **`H_*(C_{B/A}, 𝒥) = 0`** (the vanishing `Lπ_!(𝒥) = 0` of Remark 08R7, read on the standard
resolution): the Moore complex of the augmentation ideal is acyclic. -/
theorem isZero_homology_augmentationIdeal (n : ℕ) :
    IsZero (((alternatingFaceMapComplex (ModuleCat.{max u v} A)).obj
      (augmentationIdealModule.{u, v} A B).toSimplicial).homology n) :=
  ((augmentationIdealShortComplex_moore_shortExact.{u, v} A B).acyclic_X₁
    (quasiIso_augmentationIdealShortComplex_g.{u, v} A B) n).isZero_homology

/-! ### A covering of `𝒥` which stays acyclic after tensoring with `𝒥` -/

/-- The augmentation ideal as a simplicial `A`-module. -/
abbrev augmentationIdealSimplicial : SimplicialObject (ModuleCat.{max u v} A) :=
  (augmentationIdealModule.{u, v} A B).toSimplicial

/-- The reduced décalage of the augmentation ideal, a simplicially contractible simplicial
`A`-module covering it. -/
abbrev augmentationIdealDecRed : SimplicialObject (ModuleCat.{max u v} A) :=
  StacksDraft.SimplicialTensor.decRed.{v, u} (augmentationIdealSimplicial.{u, v} A B)

/-- The covering map of the reduced décalage. -/
abbrev augmentationIdealDecRedδ₀ :
    augmentationIdealDecRed.{u, v} A B ⟶ augmentationIdealSimplicial.{u, v} A B :=
  StacksDraft.SimplicialTensor.decRedδ₀.{v, u} (augmentationIdealSimplicial.{u, v} A B)

/-- The reduced décalage of `𝒥` covers `𝒥`, because `H₀(𝒥) = 0`. -/
theorem surjective_augmentationIdealDecRedδ₀ (n : SimplexCategoryᵒᵖ) :
    Function.Surjective ((augmentationIdealDecRedδ₀.{u, v} A B).app n).hom := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = op ⦋k⦌ := ⟨n.unop.len, rfl⟩
  exact StacksDraft.SimplicialTensor.decRedδ₀_app_surjective.{v, u} _
    (isZero_homology_augmentationIdeal.{u, v} A B 0) k

/-- The simplicial module `𝒦 = P_• ⊗_A decRed(𝒥)` over the standard resolution. -/
abbrev coverModule : SimplicialModuleOver (standardResolution A B).left where
  obj n := (standardResolution A B).left.obj n ⊗[A] (augmentationIdealDecRed.{u, v} A B).obj n
  map f := (TensorProduct.map ((standardResolution A B).left.map f).hom.toLinearMap
    ((augmentationIdealDecRed.{u, v} A B).map f).hom).toAddMonoidHom
  map_smul f p t := by
    induction t using TensorProduct.inductionOn with
    | tmul q l =>
      simp only [LinearMap.toAddMonoidHom_coe, TensorProduct.smul_tmul', smul_eq_mul,
        TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_mul]
    | add s t hs ht => simp only [smul_add, map_add, hs, ht]
  map_id n t := by
    induction t using TensorProduct.inductionOn with
    | tmul q l => simp
    | add s t hs ht => simp only [map_add, hs, ht]
  map_comp f g t := by
    induction t using TensorProduct.inductionOn with
    | tmul q l => simp
    | add s t hs ht => simp only [map_add, hs, ht]

/-- The covering map of the reduced décalage, landing in the augmentation ideal. -/
def decRedToIdeal (n : SimplexCategoryᵒᵖ) :
    (augmentationIdealDecRed.{u, v} A B).obj n →ₗ[A] augmentationIdeal A B n :=
  ((augmentationIdealDecRedδ₀.{u, v} A B).app n).hom

/-- The covering by the reduced décalage commutes with the simplicial operators. -/
theorem decRedToIdeal_naturality {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (l : (augmentationIdealDecRed.{u, v} A B).obj n) :
    decRedToIdeal.{u, v} A B m (((augmentationIdealDecRed.{u, v} A B).map f).hom l) =
      (augmentationIdealModule.{u, v} A B).map f (decRedToIdeal.{u, v} A B n l) := by
  have h := congrArg (fun φ => ModuleCat.Hom.hom φ l)
    ((augmentationIdealDecRedδ₀.{u, v} A B).naturality f)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- The covering `𝒦 → 𝒥`, `p ⊗ ℓ ↦ p · δ₀ ℓ`, in one degree. -/
def coverHomApp (n : SimplexCategoryᵒᵖ) :
    (coverModule.{u, v} A B).obj n →ₗ[(standardResolution A B).left.obj n]
      augmentationIdeal A B n :=
  LinearMap.liftBaseChange ((standardResolution A B).left.obj n) (decRedToIdeal.{u, v} A B n)

/-- The covering `𝒦 → 𝒥` on a pure tensor. -/
theorem coverHomApp_tmul (n : SimplexCategoryᵒᵖ) (p : (standardResolution A B).left.obj n)
    (l : (augmentationIdealDecRed.{u, v} A B).obj n) :
    coverHomApp.{u, v} A B n (p ⊗ₜ l) = p • decRedToIdeal.{u, v} A B n l := rfl

/-- The covering `𝒦 → 𝒥`. -/
def coverHom : (coverModule.{u, v} A B).Hom (augmentationIdealModule.{u, v} A B) where
  app n := coverHomApp.{u, v} A B n
  naturality f t := by
    induction t using TensorProduct.inductionOn with
    | tmul q l =>
      change coverHomApp.{u, v} A B _ (((standardResolution A B).left.map f).hom q ⊗ₜ
          ((augmentationIdealDecRed.{u, v} A B).map f).hom l) = _
      rw [coverHomApp_tmul, coverHomApp_tmul, (augmentationIdealModule.{u, v} A B).map_smul,
        decRedToIdeal_naturality]
    | add s t hs ht => simp only [map_add, hs, ht]

/-- The covering `𝒦 → 𝒥` is surjective in every degree. -/
theorem surjective_coverHom_app (n : SimplexCategoryᵒᵖ) :
    Function.Surjective (coverHomApp.{u, v} A B n) := by
  intro x
  obtain ⟨l, hl⟩ := surjective_augmentationIdealDecRedδ₀.{u, v} A B n x
  exact ⟨1 ⊗ₜ l, by rwa [coverHomApp_tmul, one_smul]⟩

/-! ### `𝒥 ⊗_𝒪 𝒦` is acyclic -/

/-- `𝒥 ⊗_P 𝒦`. -/
abbrev idealTensorCover : SimplicialModuleOver (standardResolution A B).left :=
  (augmentationIdealModule.{u, v} A B).tensor (coverModule.{u, v} A B)

/-- `𝒥 ⊗_P 𝒥`. -/
abbrev idealTensorIdeal : SimplicialModuleOver (standardResolution A B).left :=
  (augmentationIdealModule.{u, v} A B).tensor (augmentationIdealModule.{u, v} A B)

/-- `Jₙ ⊗_{Pₙ} (Pₙ ⊗_A Lₙ) = Jₙ ⊗_A Lₙ`, in one degree. -/
def idealTensorCoverEquiv (n : SimplexCategoryᵒᵖ) :
    (idealTensorCover.{u, v} A B).obj n ≃ₗ[A]
      augmentationIdeal A B n ⊗[A] (augmentationIdealDecRed.{u, v} A B).obj n :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange A ((standardResolution A B).left.obj n)
    ((standardResolution A B).left.obj n) (augmentationIdeal A B n)
    ((augmentationIdealDecRed.{u, v} A B).obj n)).restrictScalars A

/-- The identification `Jₙ ⊗_{Pₙ} (Pₙ ⊗_A Lₙ) = Jₙ ⊗_A Lₙ` on pure tensors. -/
theorem idealTensorCoverEquiv_tmul_tmul (n : SimplexCategoryᵒᵖ)
    (y : augmentationIdeal A B n) (p : (standardResolution A B).left.obj n)
    (l : (augmentationIdealDecRed.{u, v} A B).obj n) :
    idealTensorCoverEquiv.{u, v} A B n (y ⊗ₜ (p ⊗ₜ l)) =
      ((p • y : augmentationIdeal A B n) ⊗ₜ l :
        augmentationIdeal A B n ⊗[A] (augmentationIdealDecRed.{u, v} A B).obj n) := rfl

/-- The identification `Jₙ ⊗_{Pₙ} (Pₙ ⊗_A Lₙ) = Jₙ ⊗_A Lₙ` commutes with the simplicial
operators. -/
theorem idealTensorCoverEquiv_naturality {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (t : (idealTensorCover.{u, v} A B).obj n) :
    idealTensorCoverEquiv.{u, v} A B m ((idealTensorCover.{u, v} A B).map f t) =
      TensorProduct.map ((augmentationIdealModule.{u, v} A B).mapLinear f)
        ((augmentationIdealDecRed.{u, v} A B).map f).hom
          (idealTensorCoverEquiv.{u, v} A B n t) := by
  induction t using TensorProduct.inductionOn with
  | tmul y k =>
    induction k using TensorProduct.inductionOn with
    | tmul p l =>
      change idealTensorCoverEquiv.{u, v} A B m ((augmentationIdealModule.{u, v} A B).map f y ⊗ₜ
        (((standardResolution A B).left.map f).hom p ⊗ₜ
          ((augmentationIdealDecRed.{u, v} A B).map f).hom l)) = _
      rw [idealTensorCoverEquiv_tmul_tmul, idealTensorCoverEquiv_tmul_tmul,
        TensorProduct.map_tmul]
      congr 1
      exact ((augmentationIdealModule.{u, v} A B).map_smul f p y).symm
    | add k k' hk hk' =>
      rw [TensorProduct.tmul_add, map_add, map_add, hk, hk', map_add, map_add]
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]

/-- `𝒥 ⊗_P 𝒦 ≅ 𝒥 ⊗_A decRed(𝒥)` as simplicial `A`-modules. -/
def idealTensorCoverIso : (idealTensorCover.{u, v} A B).toSimplicial ≅
    augmentationIdealSimplicial.{u, v} A B ⊗ augmentationIdealDecRed.{u, v} A B :=
  NatIso.ofComponents (fun n => (idealTensorCoverEquiv.{u, v} A B n).toModuleIso) fun f =>
    ModuleCat.hom_ext (LinearMap.ext (idealTensorCoverEquiv_naturality.{u, v} A B f))

/-- **`𝒥 ⊗_P 𝒦` is acyclic.** -/
theorem isZero_homology_idealTensorCover (n : ℕ) :
    IsZero (((alternatingFaceMapComplex (ModuleCat.{max u v} A)).obj
      (idealTensorCover.{u, v} A B).toSimplicial).homology n) :=
  (StacksDraft.SimplicialTensor.isZero_homology_tensor_decRed.{v, u}
    (augmentationIdealSimplicial.{u, v} A B) (augmentationIdealSimplicial.{u, v} A B) n).of_iso
    ((HomologicalComplex.homologyFunctor _ _ n).mapIso
      ((alternatingFaceMapComplex (ModuleCat.{max u v} A)).mapIso (idealTensorCoverIso.{u, v} A B)))

/-! ### `H₀` and `H₁` of `𝒥 ⊗_𝒪 𝒥` vanish -/

/-- Every `0`-simplex of `𝒥` is `δ₀ u - δ₁ u` for a `1`-simplex `u`: this is `H₀(𝒥) = 0`. -/
theorem augmentationIdeal_exists_δ_sub_δ (x : (augmentationIdealModule.{u, v} A B).obj (op ⦋0⦌)) :
    ∃ u : (augmentationIdealModule.{u, v} A B).obj (op ⦋0 + 1⦌),
      (augmentationIdealModule.{u, v} A B).map (SimplexCategory.δ (n := 0) 0).op u -
        (augmentationIdealModule.{u, v} A B).map (SimplexCategory.δ (n := 0) 1).op u = x :=
  (isZero_homology_zero_iff_exists_δ_sub_δ _).1 (isZero_homology_augmentationIdeal.{u, v} A B 0) x

/-- **`H₀(C_{B/A}, 𝒥 ⊗_𝒪 𝒥) = 0`.** -/
theorem isZero_homology_zero_idealTensorIdeal :
    IsZero (((alternatingFaceMapComplex (ModuleCat.{max u v} A)).obj
      (idealTensorIdeal.{u, v} A B).toSimplicial).homology 0) :=
  SimplicialModuleOver.isZero_homology_zero_tensor _ _
    (isZero_homology_augmentationIdeal.{u, v} A B 0)

/-- `𝒥 ⊗ 𝒦 → 𝒥 ⊗ 𝒥`, the covering tensored on the left with `𝒥`. -/
abbrev idealTensorCoverHom : (idealTensorCover.{u, v} A B).Hom (idealTensorIdeal.{u, v} A B) :=
  SimplicialModuleOver.Hom.lTensor (augmentationIdealModule.{u, v} A B) (coverModule.{u, v} A B)
    (coverHom.{u, v} A B)

/-- The kernel of `𝒥 ⊗ 𝒦 → 𝒥 ⊗ 𝒥`. -/
abbrev coverKernel : SimplicialObject (ModuleCat.{max u v} A) :=
  StacksDraft.SimplicialTensor.simpKer.{v, u} (idealTensorCoverHom.{u, v} A B).toSimplicial

/-- The short complex `ker → 𝒥 ⊗ 𝒦 → 𝒥 ⊗ 𝒥`. -/
abbrev coverKernelShortComplex : ShortComplex (SimplicialObject (ModuleCat.{max u v} A)) :=
  ShortComplex.mk (StacksDraft.SimplicialTensor.simpKerι.{v, u} _)
    (idealTensorCoverHom.{u, v} A B).toSimplicial
    (StacksDraft.SimplicialTensor.simpKerι_comp.{v, u} _)

/-- The degreewise kernel sequence `0 → ker g → X → Y → 0` is exact when `g` is surjective. -/
private theorem simpKer_shortExact_app {X Y : SimplicialObject (ModuleCat.{max u v} A)}
    (g : X ⟶ Y) (n : SimplexCategoryᵒᵖ) (hg : Function.Surjective (g.app n).hom) :
    ((ShortComplex.mk (StacksDraft.SimplicialTensor.simpKerι.{v, u} g) g
      (StacksDraft.SimplicialTensor.simpKerι_comp.{v, u} g)).map
        ((evaluation SimplexCategoryᵒᵖ (ModuleCat.{max u v} A)).obj n)).ShortExact where
  exact := (ShortComplex.moduleCat_exact_iff _).2 fun x hx => ⟨⟨x, hx⟩, rfl⟩
  mono_f := (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
  epi_g := (ModuleCat.epi_iff_surjective _).2 hg

/-- `0 → ker → Jₙ ⊗ Kₙ → Jₙ ⊗ Jₙ → 0` is exact in every degree, by right exactness of `⊗`. -/
theorem coverKernelShortComplex_shortExact_app (n : SimplexCategoryᵒᵖ) :
    ((coverKernelShortComplex.{u, v} A B).map
      ((evaluation SimplexCategoryᵒᵖ (ModuleCat.{max u v} A)).obj n)).ShortExact :=
  simpKer_shortExact_app.{u, v} A _ n
    (LinearMap.lTensor_surjective _ (surjective_coverHom_app.{u, v} A B n))

/-- The Moore complexes of `0 → ker → 𝒥 ⊗ 𝒦 → 𝒥 ⊗ 𝒥 → 0` are short exact. -/
theorem coverKernelShortComplex_moore_shortExact :
    ((coverKernelShortComplex.{u, v} A B).map
      (alternatingFaceMapComplex (ModuleCat.{max u v} A))).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i =>
    coverKernelShortComplex_shortExact_app.{u, v} A B (op ⦋i⦌)

/-- The lifting step: an element `y ⊗ w` of `J₀ ⊗ ker(K₀ → J₀)` is the boundary of
`u ⊗ σ₀ w`, which lies in the kernel, for any `u` with `δ₀ u - δ₁ u = y`. -/
theorem exists_coverKernel_lift
    (z : augmentationIdeal A B (op ⦋0⦌) ⊗[(standardResolution A B).left.obj (op ⦋0⦌)]
      LinearMap.ker (coverHomApp.{u, v} A B (op ⦋0⦌))) :
    ∃ w : augmentationIdeal A B (op ⦋0 + 1⦌) ⊗[(standardResolution A B).left.obj (op ⦋0 + 1⦌)]
        ((standardResolution A B).left.obj (op ⦋0 + 1⦌) ⊗[A]
          (augmentationIdealDecRed.{u, v} A B).obj (op ⦋0 + 1⦌)),
      LinearMap.lTensor _ (coverHomApp.{u, v} A B (op ⦋0 + 1⦌)) w = 0 ∧
      SimplicialModuleOver.tensorMap (augmentationIdealModule.{u, v} A B) (coverModule.{u, v} A B)
          (SimplexCategory.δ (n := 0) 0).op w -
        SimplicialModuleOver.tensorMap (augmentationIdealModule.{u, v} A B)
          (coverModule.{u, v} A B) (SimplexCategory.δ (n := 0) 1).op w =
        LinearMap.lTensor _ (LinearMap.ker (coverHomApp.{u, v} A B (op ⦋0⦌))).subtype z := by
  induction z using TensorProduct.inductionOn with
  | tmul y k =>
    obtain ⟨u, hu⟩ := augmentationIdeal_exists_δ_sub_δ.{u, v} A B y
    refine ⟨u ⊗ₜ (coverModule.{u, v} A B).map (SimplexCategory.σ (0 : Fin 1)).op k.1, ?_, ?_⟩
    · rw [LinearMap.lTensor_tmul]
      have hk : coverHomApp.{u, v} A B (op ⦋0 + 1⦌)
          ((coverModule.{u, v} A B).map (SimplexCategory.σ (0 : Fin 1)).op k.1) = 0 := by
        have h := (coverHom.{u, v} A B).naturality (SimplexCategory.σ (0 : Fin 1)).op k.1
        change coverHomApp.{u, v} A B _ _ = _ at h
        rw [h, show (coverHom.{u, v} A B).app (op ⦋0⦌) k.1 = 0 from k.2, map_zero]
      rw [hk, TensorProduct.tmul_zero]
    · rw [SimplicialModuleOver.tensorMap_tmul, SimplicialModuleOver.tensorMap_tmul,
        SimplicialModuleOver.map_δ_map_σ_zero, SimplicialModuleOver.map_δ_map_σ_zero,
        ← TensorProduct.sub_tmul, hu, LinearMap.lTensor_tmul]
      rfl
  | add s t hs ht =>
    obtain ⟨w, hw0, hw⟩ := hs
    obtain ⟨w', hw0', hw'⟩ := ht
    refine ⟨w + w', by rw [map_add, hw0, hw0', add_zero], ?_⟩
    rw [map_add, map_add, map_add, ← hw, ← hw']
    abel

/-- `H₀` of the kernel of `𝒥 ⊗ 𝒦 → 𝒥 ⊗ 𝒥` vanishes. -/
theorem isZero_homology_zero_coverKernel :
    IsZero (((alternatingFaceMapComplex (ModuleCat.{max u v} A)).obj
      (coverKernel.{u, v} A B)).homology 0) := by
  rw [isZero_homology_zero_iff_exists_δ_sub_δ]
  intro x
  have hex := lTensor_exact (augmentationIdeal A B (op ⦋0⦌))
    (LinearMap.exact_subtype_ker_map (coverHomApp.{u, v} A B (op ⦋0⦌)))
    (surjective_coverHom_app.{u, v} A B (op ⦋0⦌))
  obtain ⟨z, hz⟩ := (hex x.1).1 (LinearMap.mem_ker.1 x.2)
  obtain ⟨w, hw0, hw⟩ := exists_coverKernel_lift.{u, v} A B z
  exact ⟨⟨w, hw0⟩, Subtype.ext (hw.trans hz)⟩

/-- **`H₁(C_{B/A}, 𝒥 ⊗_𝒪 𝒥) = 0`.** -/
theorem isZero_homology_one_idealTensorIdeal :
    IsZero (((alternatingFaceMapComplex (ModuleCat.{max u v} A)).obj
      (idealTensorIdeal.{u, v} A B).toSimplicial).homology 1) := by
  have hS := coverKernelShortComplex_moore_shortExact.{u, v} A B
  have := hS.mono_δ 1 0 rfl (isZero_homology_idealTensorCover.{u, v} A B 1)
  exact IsZero.of_mono (hS.δ 1 0 rfl) (isZero_homology_zero_coverKernel.{u, v} A B)

/-! ### `𝒥²`, the multiplication `𝒥 ⊗_𝒪 𝒥 → 𝒥²`, and `Tor₁^𝒪(𝒥, B̲)` -/

/-- A simplicial operator of the standard resolution preserves the square of the augmentation
ideal. -/
theorem map_mem_augmentationIdeal_mul {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (x : (standardResolution A B).left.obj n)
    (hx : x ∈ augmentationIdeal A B n * augmentationIdeal A B n) :
    ((standardResolution A B).left.map f).hom x ∈
      augmentationIdeal A B m * augmentationIdeal A B m := by
  have hle : Ideal.map ((standardResolution A B).left.map f).hom (augmentationIdeal A B n) ≤
      augmentationIdeal A B m :=
    Ideal.map_le_iff_le_comap.2 fun y hy => map_mem_augmentationIdeal.{u, v} A B f y hy
  have h := Ideal.mem_map_of_mem ((standardResolution A B).left.map f).hom hx
  rw [Ideal.map_mul] at h
  exact Ideal.mul_mono hle hle h

/-- `𝒥² = 𝒥 · 𝒥` as a simplicial module over the standard resolution. -/
abbrev augmentationIdealSqModule : SimplicialModuleOver (standardResolution A B).left where
  obj n := ↥(augmentationIdeal A B n * augmentationIdeal A B n)
  map f :=
    { toFun := fun x => ⟨((standardResolution A B).left.map f).hom x.1,
        map_mem_augmentationIdeal_mul.{u, v} A B f x.1 x.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x.1 y.1) }
  map_smul f p x := Subtype.ext (map_mul _ p x.1)
  map_id n x := Subtype.ext (by simp)
  map_comp f g x := Subtype.ext (by simp)

/-- The multiplication `𝒥 ⊗_𝒪 𝒥 → 𝒥²`, degreewise `Submodule.mulMap'`. -/
def idealMulHom : (idealTensorIdeal.{u, v} A B).Hom (augmentationIdealSqModule.{u, v} A B) where
  app n := Submodule.mulMap' (augmentationIdeal A B n) (augmentationIdeal A B n)
  naturality f t := by
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      apply Subtype.ext
      change ((standardResolution A B).left.map f).hom x.1 *
          ((standardResolution A B).left.map f).hom y.1 =
        ((standardResolution A B).left.map f).hom (x.1 * y.1)
      rw [map_mul]
    | add s t hs ht => simp only [map_add, hs, ht]

/-- The inclusion `𝒥² ⊂ 𝒥`. -/
def idealSqInclusion :
    (augmentationIdealSqModule.{u, v} A B).Hom (augmentationIdealModule.{u, v} A B) where
  app _ := Submodule.inclusion Ideal.mul_le_left
  naturality _ _ := rfl

/-- **`Tor₁^𝒪(𝒥, B̲)` on the standard resolution.** In degree `n` it is the kernel of the
multiplication `Jₙ ⊗_{Pₙ} Jₙ → Jₙ²`, which is `Tor₁^{Pₙ}(Jₙ, B)`
(`Stacks.Cotangent.torOneSimplicialObjIsoTor`). -/
abbrev torOneSimplicial : SimplicialObject (ModuleCat.{max u v} A) :=
  StacksDraft.SimplicialTensor.simpKer.{v, u} (idealMulHom.{u, v} A B).toSimplicial

/-- The kernel of `Jₙ ⊗_{Pₙ} Jₙ → Jₙ²` over `Pₙ`, with its scalars restricted to `A`, is the
term of `Tor₁^𝒪(𝒥, B̲)` in degree `n`. -/
def mulMapKerRestrictIso (n : SimplexCategoryᵒᵖ) :
    (ModuleCat.restrictScalars (algebraMap A ((standardResolution A B).left.obj n))).obj
        (ModuleCat.of ((standardResolution A B).left.obj n)
          ↥(LinearMap.ker (Submodule.mulMap' (augmentationIdeal A B n)
            (augmentationIdeal A B n)))) ≅
      (torOneSimplicial.{u, v} A B).obj n :=
  letI : Module A ↥(LinearMap.ker (Submodule.mulMap' (augmentationIdeal A B n)
      (augmentationIdeal A B n))) :=
    Module.compHom _ (algebraMap A ((standardResolution A B).left.obj n))
  LinearEquiv.toModuleIso
    (show ↥(LinearMap.ker (Submodule.mulMap' (augmentationIdeal A B n)
        (augmentationIdeal A B n))) ≃ₗ[A]
        ↥(LinearMap.ker (((idealMulHom.{u, v} A B).toSimplicial.app n).hom)) from
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun a x => Subtype.ext
        (algebraMap_smul ((standardResolution A B).left.obj n) a
          (x.1 : augmentationIdeal A B n ⊗[(standardResolution A B).left.obj n]
            augmentationIdeal A B n))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl })

/-- **`Tor₁^𝒪(𝒥, B̲)` on the standard resolution is degreewise `Tor₁`:** its term in degree `n`
is `Tor₁^{Pₙ}(Jₙ, B)` — Mathlib's `Tor'`, for the `Pₙ`-algebra structure of `B` given by the
augmentation — read as an `A`-module. This is `torOneIdealIsoMulKernel` of Tag 09D6 for the
surjection `Pₙ → B`. -/
def torOneSimplicialObjIsoTor (n : SimplexCategoryᵒᵖ) :
    letI := (standardResolutionAugmentationHom A B n).toAlgebra
    (ModuleCat.restrictScalars (algebraMap A ((standardResolution A B).left.obj n))).obj
        (((Tor' (ModuleCat.{max u v} ((standardResolution A B).left.obj n)) 1).obj
          (ModuleCat.of _ (RingHom.ker (algebraMap ((standardResolution A B).left.obj n)
            (B : Type (max u v)))))).obj (ModuleCat.of _ (B : Type (max u v)))) ≅
      (torOneSimplicial.{u, v} A B).obj n :=
  letI := (standardResolutionAugmentationHom A B n).toAlgebra
  (ModuleCat.restrictScalars (algebraMap A ((standardResolution A B).left.obj n))).mapIso
      (torOneIdealIsoMulKernel (surjective_standardResolutionAugmentationHom.{u, v} A B n)) ≪≫
    mulMapKerRestrictIso.{u, v} A B n

/-- The Moore complex of `Tor₁^𝒪(𝒥, B̲)`, whose homology is `H_*(C_{B/A}, Tor₁^𝒪(𝒥, B̲))`. -/
abbrev torOneMooreComplex : ChainComplex (ModuleCat.{max u v} A) ℕ :=
  (alternatingFaceMapComplex (ModuleCat.{max u v} A)).obj (torOneSimplicial.{u, v} A B)

/-- The short complex `Tor₁^𝒪(𝒥, B̲) → 𝒥 ⊗_𝒪 𝒥 → 𝒥²`. -/
abbrev torOneShortComplex : ShortComplex (SimplicialObject (ModuleCat.{max u v} A)) :=
  ShortComplex.mk (StacksDraft.SimplicialTensor.simpKerι.{v, u} _)
    (idealMulHom.{u, v} A B).toSimplicial
    (StacksDraft.SimplicialTensor.simpKerι_comp.{v, u} _)

/-- `0 → Tor₁ → Jₙ ⊗ Jₙ → Jₙ² → 0` is exact in every degree. -/
theorem torOneShortComplex_shortExact_app (n : SimplexCategoryᵒᵖ) :
    ((torOneShortComplex.{u, v} A B).map
      ((evaluation SimplexCategoryᵒᵖ (ModuleCat.{max u v} A)).obj n)).ShortExact :=
  simpKer_shortExact_app.{u, v} A _ n (Submodule.mulMap'_surjective _ _)

/-- The Moore complexes of `0 → Tor₁^𝒪(𝒥, B̲) → 𝒥 ⊗_𝒪 𝒥 → 𝒥² → 0` are short exact. -/
theorem torOneShortComplex_moore_shortExact :
    ((torOneShortComplex.{u, v} A B).map
      (alternatingFaceMapComplex (ModuleCat.{max u v} A))).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i =>
    torOneShortComplex_shortExact_app.{u, v} A B (op ⦋i⦌)

/-! ### The short exact sequence `0 → 𝒥² → 𝒥 → 𝒥/𝒥² → 0` -/

/-- The conormal simplicial module `𝒥/𝒥²`, read as a simplicial `A`-module. -/
abbrev conormalSimplicialRestrict : SimplicialObject (ModuleCat.{max u v} A) :=
  conormalSimplicialModule.{u, v} A B ⋙ ModuleCat.restrictScalars (algebraMap A B)

/-- The class map `Jₙ → Jₙ/Jₙ²`, as an `A`-linear map. -/
def idealToConormalApp (n : SimplexCategoryᵒᵖ) :
    augmentationIdeal A B n →ₗ[A] (conormalExtension.{u, v} A B n).Cotangent where
  toFun x := Algebra.Extension.Cotangent.mk (P := conormalExtension.{u, v} A B n) x
  map_add' x y := map_add _ x y
  map_smul' a x :=
    ((Algebra.Extension.Cotangent.mk (P := conormalExtension.{u, v} A B n)).restrictScalars
      A).map_smul a x

/-- The class map `𝒥 → 𝒥/𝒥²`. -/
def idealToConormal :
    augmentationIdealSimplicial.{u, v} A B ⟶ conormalSimplicialRestrict.{u, v} A B where
  app n := ModuleCat.ofHom (X := augmentationIdeal A B n)
    (Y := (conormalExtension.{u, v} A B n).Cotangent) (idealToConormalApp.{u, v} A B n)
  naturality n m f := by
    ext x
    exact (conormalSimplicialModule_map_mk.{u, v} A B f x
      ((augmentationIdealModule.{u, v} A B).map f x) rfl).symm

/-- The short complex `𝒥² → 𝒥 → 𝒥/𝒥²`. -/
abbrev conormalShortComplexRestrict : ShortComplex (SimplicialObject (ModuleCat.{max u v} A)) where
  X₁ := (augmentationIdealSqModule.{u, v} A B).toSimplicial
  X₂ := augmentationIdealSimplicial.{u, v} A B
  X₃ := conormalSimplicialRestrict.{u, v} A B
  f := (idealSqInclusion.{u, v} A B).toSimplicial
  g := idealToConormal.{u, v} A B
  zero := by
    refine NatTrans.ext (funext fun n => ?_)
    ext x
    exact (Algebra.Extension.Cotangent.mk_eq_zero_iff (P := conormalExtension.{u, v} A B n)
      ⟨x.1, Ideal.mul_le_left x.2⟩).2 (by rw [sq]; exact x.2)

/-- `0 → Jₙ² → Jₙ → Jₙ/Jₙ² → 0` is exact in every degree. -/
theorem conormalShortComplexRestrict_shortExact_app (n : SimplexCategoryᵒᵖ) :
    ((conormalShortComplexRestrict.{u, v} A B).map
      ((evaluation SimplexCategoryᵒᵖ (ModuleCat.{max u v} A)).obj n)).ShortExact where
  exact := by
    refine (ShortComplex.moduleCat_exact_iff _).2 ?_
    intro x hx
    let y : (conormalExtension.{u, v} A B n).ker := x
    have hx' := (Algebra.Extension.Cotangent.mk_eq_zero_iff y).1 hx
    rw [sq] at hx'
    exact ⟨(⟨y.1, hx'⟩ : ↥(augmentationIdeal A B n * augmentationIdeal A B n)), rfl⟩
  mono_f := (ModuleCat.mono_iff_injective _).2 fun x y h =>
    Subtype.ext (by have h' := congrArg Subtype.val h; exact h')
  epi_g := (ModuleCat.epi_iff_surjective _).2 Algebra.Extension.Cotangent.mk_surjective

/-- The Moore complexes of `0 → 𝒥² → 𝒥 → 𝒥/𝒥² → 0` are short exact. -/
theorem conormalShortComplexRestrict_moore_shortExact :
    ((conormalShortComplexRestrict.{u, v} A B).map
      (alternatingFaceMapComplex (ModuleCat.{max u v} A))).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i =>
    conormalShortComplexRestrict_shortExact_app.{u, v} A B (op ⦋i⦌)

/-! ### The differential and the formula for `H₂(L_{B/A})` -/

/-- The connecting map `H₂(C_{B/A}, 𝒥/𝒥²) → H₁(C_{B/A}, 𝒥²)` of `0 → 𝒥² → 𝒥 → 𝒥/𝒥² → 0`. -/
abbrev conormalToSqδ :
    ((alternatingFaceMapComplex (ModuleCat.{max u v} A)).obj
        (conormalSimplicialRestrict.{u, v} A B)).homology 2 ⟶
      ((alternatingFaceMapComplex (ModuleCat.{max u v} A)).obj
        (augmentationIdealSqModule.{u, v} A B).toSimplicial).homology 1 :=
  (conormalShortComplexRestrict_moore_shortExact.{u, v} A B).δ 2 1 rfl

/-- The connecting map `H₁(C_{B/A}, 𝒥²) → H₀(C_{B/A}, Tor₁^𝒪(𝒥, B̲))` of
`0 → Tor₁^𝒪(𝒥, B̲) → 𝒥 ⊗_𝒪 𝒥 → 𝒥² → 0`. -/
abbrev sqToTorOneδ :
    ((alternatingFaceMapComplex (ModuleCat.{max u v} A)).obj
        (augmentationIdealSqModule.{u, v} A B).toSimplicial).homology 1 ⟶
      (torOneMooreComplex.{u, v} A B).homology 0 :=
  (torOneShortComplex_moore_shortExact.{u, v} A B).δ 1 0 rfl

/-- `H_*(C_{B/A}, 𝒥) = 0` in degrees `1` and `2` makes the first connecting map invertible. -/
instance isIso_conormalToSqδ : IsIso (conormalToSqδ.{u, v} A B) :=
  (conormalShortComplexRestrict_moore_shortExact.{u, v} A B).isIso_δ 2 1 rfl
    (isZero_homology_augmentationIdeal.{u, v} A B 2)
    (isZero_homology_augmentationIdeal.{u, v} A B 1)

/-- `H₁` and `H₀` of `𝒥 ⊗_𝒪 𝒥` vanish, which makes the second connecting map invertible. -/
instance isIso_sqToTorOneδ : IsIso (sqToTorOneδ.{u, v} A B) :=
  (torOneShortComplex_moore_shortExact.{u, v} A B).isIso_δ 1 0 rfl
    (isZero_homology_one_idealTensorIdeal.{u, v} A B)
    (isZero_homology_zero_idealTensorIdeal.{u, v} A B)

/-- The homology of the conormal Moore complex, read as an `A`-module, is the homology of the
conormal simplicial module read as a simplicial `A`-module. -/
def conormalHomologyRestrictIso (n : ℕ) :
    (ModuleCat.restrictScalars (algebraMap A B)).obj
        ((conormalMooreComplex.{u, v} A B).homology n) ≅
      ((alternatingFaceMapComplex (ModuleCat.{max u v} A)).obj
        (conormalSimplicialRestrict.{u, v} A B)).homology n :=
  (((conormalMooreComplex.{u, v} A B).sc n).mapHomologyIso
      (ModuleCat.restrictScalars (algebraMap A B))).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso
        (ModuleCat.restrictScalars.{max u v} (algebraMap A B))).app
          (conormalSimplicialModule.{u, v} A B))

/-- **The differential `H₂(C_{B/A}, 𝒥/𝒥²) → H₀(C_{B/A}, Tor₁^𝒪(𝒥, B̲))` of Stacks 09D5**: the
composite of the connecting maps of `0 → 𝒥² → 𝒥 → 𝒥/𝒥² → 0` and
`0 → Tor₁^𝒪(𝒥, B̲) → 𝒥 ⊗_𝒪 𝒥 → 𝒥² → 0`. This composite models the differential `d₂` of the
spectral sequence of Remark 08R7, up to the sign convention; the spectral sequence is not built in
Lean and that identification is the informal argument of the module docstring, not a theorem. -/
def conormalTorOneDifferential :
    (ModuleCat.restrictScalars (algebraMap A B)).obj
        ((conormalMooreComplex.{u, v} A B).homology 2) ⟶
      (torOneMooreComplex.{u, v} A B).homology 0 :=
  (conormalHomologyRestrictIso.{u, v} A B 2).hom ≫ conormalToSqδ.{u, v} A B ≫
    sqToTorOneδ.{u, v} A B

/-- **Stacks 09D5: the differential `H₂(C_{B/A}, 𝒥/𝒥²) → H₀(C_{B/A}, Tor₁^𝒪(𝒥, B̲))` of the
spectral sequence of Remark 08R7 is an isomorphism.** The differential is modelled as the
composite of the two connecting maps, which is `d₂` of that spectral sequence up to sign by the
informal argument of the module docstring (the spectral sequence is not built in Lean, so this
identification is not proved); each connecting map is an isomorphism because `H₁` and `H₂` of
`𝒥`, and `H₀` and `H₁` of `𝒥 ⊗_𝒪 𝒥`, vanish. -/
@[stacks 09D5 "the differential H₂(C_{B/A}, 𝒥/𝒥²) → H₀(C_{B/A}, Tor₁^𝒪(𝒥, B̲)) is an \
  isomorphism, read on the standard resolution; the differential is modelled as the composite of \
  the two connecting maps, which is d₂ of the spectral sequence of Remark 08R7 up to sign (not \
  proved, the spectral sequence is not built)"]
theorem isIso_conormalTorOneDifferential : IsIso (conormalTorOneDifferential.{u, v} A B) := by
  unfold conormalTorOneDifferential
  infer_instance

/-- `H₂(L_{B/A}) ≅ H₂(C_{B/A}, 𝒥/𝒥²)`: the case `n = 2` of the registered isomorphism in degrees
`≥ 2`, followed by the reindexing of the conormal complex. -/
def cotangentComplexHomologyTwoIsoConormal :
    (cotangentComplex A B).homology (-2) ≅ (conormalMooreComplex.{u, v} A B).homology 2 :=
  haveI : IsIso (HomologicalComplex.homologyMap (conormalToCotangentComplex.{u, v} A B) (-2)) :=
    isIso_homologyMap_conormalToCotangentComplex.{u, v} A B 2 le_rfl
  (asIso (HomologicalComplex.homologyMap (conormalToCotangentComplex.{u, v} A B) (-2))).symm ≪≫
    (conormalMooreComplex.{u, v} A B).extendHomologyIso (ComplexShape.embeddingUpIntLE 0)
      (by simp)

/-- **`H₂(L_{B/A}) = H₀(C_{B/A}, Tor₁^𝒪(𝒥, B̲))`, read as `A`-modules.** The isomorphism of
`B`-modules of Stacks 09D5 is `Stacks.Cotangent.cotangentComplexHomologyTwoLinearIsoTorOne` of
`StacksFrontier/Cotangent/ConormalTorDifferentialLinear.lean`; this is its `A`-linear shadow.
`H₂(L_{B/A})` is
the homology in cohomological degree `-2` of the cotangent complex of Tag 08PN, and the right-hand
side is `H₀` of the Moore complex of `n ↦ Tor₁^{Pₙ}(Jₙ, B)` on the standard resolution. The
isomorphism is `H₂(L_{B/A}) ≅ H₂(C_{B/A}, 𝒥/𝒥²)` followed by the differential. -/
def cotangentComplexHomologyTwoIsoTorOne :
    (ModuleCat.restrictScalars (algebraMap A B)).obj ((cotangentComplex A B).homology (-2)) ≅
      (torOneMooreComplex.{u, v} A B).homology 0 :=
  haveI := isIso_conormalTorOneDifferential.{u, v} A B
  (ModuleCat.restrictScalars (algebraMap A B)).mapIso
      (cotangentComplexHomologyTwoIsoConormal.{u, v} A B) ≪≫
    asIso (conormalTorOneDifferential.{u, v} A B)

end Stacks.Cotangent
