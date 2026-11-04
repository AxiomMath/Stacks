module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.InverseSections
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.InversePairingLinear
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover

/-!
# The multiplication clause of Tag 0CDX

Let `X` be a quasi-compact, quasi-separated scheme over a ring `A`, let `φ : A →+* B` be
faithfully flat, and let `L` be an invertible `𝒪_X`-module whose pullback to `X_B` is trivial.
[Stacks, Tag 0CDX] asserts three things: that `Γ(X, L)` and `Γ(X, L^{⊗ -1})` are invertible
`Γ(X, 𝒪_X)`-modules, and that the multiplication map

`Γ(X, L) ⊗_{Γ(X, 𝒪_X)} Γ(X, L^{⊗ -1}) ⟶ Γ(X, 𝒪_X)`

is an isomorphism.  The two invertibility clauses are proved in
`StacksFrontier/AlgebraicGeometry/PicardBaseChange/Sections.lean` and
`StacksFrontier/AlgebraicGeometry/PicardBaseChange/InverseSections.lean`.  This file proves the multiplication clause.

The proof is the source's: the multiplication is surjective after pulling back to `X_B`,
because there `L` is trivial, and surjectivity descends along the faithfully flat ring map
`Γ(X, 𝒪_X) → Γ(X_B, 𝒪_{X_B})`.  Formally it has three independent parts, in the three sections
below:

* an algebraic transfer lemma, which turns surjectivity of a pairing over the base change into
  surjectivity of the original pairing after tensoring;
* two facts about sections of a sheaf tensor product — that the sheafification unit is natural,
  and that the left unit constraint sends `1 ⊗ m` to `m` — from which: over a scheme on which
  `A` is trivial, *every* section of `A ⊗ B` is a product of a section of `A` and a section of
  `B`;
* the identification of the pulled-back multiplication, which is the Tag 01CD comparison
  together with `Stacks.RingedSpace.comparison_pullbackUnit_tmul`.

## Main definitions

* `Stacks.SheafOfModules.Invertible.mulNegOneIso`: the multiplication `L ⊗ L^{⊗ -1} ≅ 𝒪`, with
  the first factor read as `L` itself rather than as its first tensor power.
* `Stacks.AlgebraicGeometry.PicardBaseChange.pullbackMulNegOneIso`: its pullback along a
  morphism of schemes, `p^* L ⊗ p^*(L^{⊗ -1}) ≅ 𝒪_Y`.
* `Stacks.AlgebraicGeometry.PicardBaseChange.pullbackMulNegOne` and
  `pullbackMulNegOneLinear`: the resulting product of global sections on `Y`, as a function of
  two sections and as a linear map out of their tensor product.

## Main results

* `Module.surjective_lTensor_of_pairing`: the algebraic transfer lemma.
* `Stacks.SheafOfModules.Invertible.exists_toSheafify_tmul_eq`: if `A` is trivial then every
  section of `A ⊗ B` is a product of a section of `A` and a section of `B`.
* `Stacks.AlgebraicGeometry.PicardBaseChange.pullbackMulNegOneIso_pullbackUnitSections`: the
  pullback of a product is the product of the pullbacks, on global sections.
* `Stacks.AlgebraicGeometry.PicardBaseChange.surjective_lTensor_globalSectionsMulNegOneLinear`:
  the multiplication becomes surjective after a trivializing base change.
* `Stacks.AlgebraicGeometry.PicardBaseChange`
  `.exists_mulEquiv_globalSections_of_faithfullyFlat_trivialization`: **the multiplication
  clause of Tag 0CDX.**

## Implementation notes

**Where the tag sits.** The multiplication below is
`Stacks.SheafOfModules.Invertible.globalSectionsMulNegOne`
(`StacksFrontier/AlgebraicGeometry/PicardBaseChange/InversePairing.lean`), built from the braiding, `tensorPowerOneIso` and
one step of the defining integer iteration of Tag 01CU.  That composite **is** Tag 01CU's
coherent multiplication `mulIso 1 (-1)`:
`Stacks.SheafOfModules.Invertible.tensorPowerCoherence_mulIso_one_negOne`
(`StacksFrontier/AlgebraicGeometry/TensorPowerCoherence/NegOne.lean`) proves the equality, the `TensorPowerCoherence`
structure of Tag 01CU now being part of the development.  The `@[stacks 0CDX]` attribute for
this clause is therefore carried by the transcription written with the coherent multiplication,
`StacksFrontier/AlgebraicGeometry/PicardBaseChange/CoherentMul.lean`, which follows from the theorem below by that
equality; no attribute is attached here only so that the clause has one site.

**The pairing is bundled as a linear map, not as a bilinear function.** The scalars of the
tensor product of two modules of sections are spelled
`(Y.presheaf ⋙ forget₂ CommRingCat RingCat).obj (op ⊤)`, where a `TensorProduct` lemma's
pattern wants a bare `CommSemiring`, so `rw [TensorProduct.add_tmul]` does not fire on a goal
about the product of two sections.  Assembling the product as a composition of two linear maps
ascribed at the `Γ(Y, ⊤)` spelling — the discipline of
`StacksFrontier/AlgebraicGeometry/PicardBaseChange/InversePairingLinear.lean` — makes bilinearity a consequence of the
construction, and the transfer lemma then takes the bundled map.

**Equations between morphisms of sheaves are read on sections in term mode.** The ringed-space
spellings of the pullback functor, of the tensor product and of the structure sheaf are
definitionally but not syntactically the scheme-level ones, so `rw` at reducible transparency
does not match a ringed-space lemma against a scheme-level goal.  Every such step below
is `PresheafOfModules.hom_congr_apply` or `congrArg` with its arguments supplied, which
typechecks up to definitional equality.  No transparency lever and no `erw` is used.

## References

* [Stacks Project, Tag 0CDX](https://stacks.math.columbia.edu/tag/0CDX)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 058S](https://stacks.math.columbia.edu/tag/058S)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CategoryTheory.Limits Opposite TensorProduct
open PresheafOfModules TopologicalSpace AlgebraicGeometry
open Stacks.SheafOfModules (unitOne)
open Stacks.SheafOfModules.Invertible
open Stacks.AlgebraicGeometry.ModuleLimits (pullbackTensorIso)
open AlgebraicGeometry.Scheme.Modules (pullbackUnitIso)
open Stacks.AlgebraicGeometry.SectionsBaseChange
open Stacks.AlgebraicGeometry.PicardBaseChange
open AlgebraicGeometry.SheafOfModules (IsInvertible IsTrivial)

universe v u w w₁ w₂ w₃ w₄

/-! ### The algebraic transfer lemma -/

/-- **A pairing that hits `1` after a base change becomes surjective after tensoring.** Let
`R → S` be a ring map, let `μ : M ⊗_R N → R` be a pairing, and let `M'` and `N'` be the base
changes of `M` and `N` to `S`.  If a pairing `ν : M' ⊗_S N' → S` agrees with `μ` on the images
of `M` and `N` and takes the value `1` on some pure tensor, then `μ ⊗_R S` is surjective.

Surjectivity of `μ ⊗_R S` is the hypothesis of
`Module.Invertible.exists_mulEquiv_of_lTensor_surjective`, and this is how the geometry
supplies it: the base changes are the sections of the pullbacks, `ν` is the pulled-back
multiplication, and the value `1` comes from the triviality of the pullback of `L`. -/
theorem Module.surjective_lTensor_of_pairing
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    {M : Type w₁} [AddCommGroup M] [Module R M]
    {N : Type w₂} [AddCommGroup N] [Module R N]
    {M' : Type w₃} [AddCommGroup M'] [Module R M'] [Module S M'] [IsScalarTower R S M']
    {N' : Type w₄} [AddCommGroup N'] [Module R N'] [Module S N'] [IsScalarTower R S N']
    (μ : M ⊗[R] N →ₗ[R] R)
    {ρM : M →ₗ[R] M'} (hM : IsBaseChange S ρM)
    {ρN : N →ₗ[R] N'} (hN : IsBaseChange S ρN)
    (ν : M' ⊗[S] N' →ₗ[S] S)
    (hcompat : ∀ s t, ν (ρM s ⊗ₜ[S] ρN t) = algebraMap R S (μ (s ⊗ₜ[R] t)))
    (m₀ : M') (n₀ : N') (hone : ν (m₀ ⊗ₜ[S] n₀) = 1) :
    Function.Surjective (μ.lTensor S) := by
  classical
  set I : Submodule S S :=
    Submodule.span S (Set.range fun q : M × N => algebraMap R S (μ (q.1 ⊗ₜ[R] q.2))) with hI
  have hgen : ∀ s t, ν (ρM s ⊗ₜ[S] ρN t) ∈ I := by
    intro s t
    rw [hcompat]
    exact Submodule.subset_span ⟨(s, t), rfl⟩
  have hright : ∀ (s : M) (n : N'), ν (ρM s ⊗ₜ[S] n) ∈ I := fun s n =>
    hN.inductionOn n _ (by simp) (fun t => hgen s t)
      (fun a n h => by rw [TensorProduct.tmul_smul, map_smul]; exact I.smul_mem _ h)
      (fun n₁ n₂ h₁ h₂ => by rw [TensorProduct.tmul_add, map_add]; exact I.add_mem h₁ h₂)
  have hall : ∀ (m : M') (n : N'), ν (m ⊗ₜ[S] n) ∈ I := fun m n =>
    hM.inductionOn m _ (by simp) (fun s => hright s n)
      (fun a m h => by rw [← TensorProduct.smul_tmul', map_smul]; exact I.smul_mem _ h)
      (fun m₁ m₂ h₁ h₂ => by rw [TensorProduct.add_tmul, map_add]; exact I.add_mem h₁ h₂)
  have hone' : (1 : S) ∈ I := hone ▸ hall m₀ n₀
  set K : Submodule R S :=
    LinearMap.range ((TensorProduct.rid R S).toLinearMap ∘ₗ μ.lTensor S) with hK
  have hmul : ∀ x ∈ I, ∀ a : S, a * x ∈ K := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨q, rfl⟩ := hy
        intro a
        refine ⟨a ⊗ₜ[R] (q.1 ⊗ₜ[R] q.2), ?_⟩
        simp [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Algebra.smul_def, mul_comm]
    | zero => intro a; simp
    | add y z _ _ hy hz => intro a; rw [mul_add]; exact K.add_mem (hy a) (hz a)
    | smul c y _ hy => intro a; rw [smul_eq_mul, ← mul_assoc]; exact hy (a * c)
  intro y
  obtain ⟨x, hx⟩ := hmul 1 hone' (TensorProduct.rid R S y)
  refine ⟨x, ?_⟩
  rw [mul_one] at hx
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply] at hx
  exact (TensorProduct.rid R S).injective hx

/-! ### Sections of a sheaf tensor product -/

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- An isomorphism of sheaves of modules undoes its inverse on sections. -/
theorem isoValApp_hom_inv {R : Sheaf J RingCat.{w}} {A B : SheafOfModules.{w} R} (e : A ≅ B)
    (U : Cᵒᵖ) (x : B.val.obj U) : Hom.app e.hom.val U (Hom.app e.inv.val U x) = x :=
  PresheafOfModules.hom_congr_apply (congrArg (fun g : B ⟶ B => g.val) e.inv_hom_id) U x

/-- The inverse of an isomorphism of sheaves of modules undoes it on sections. -/
theorem isoValApp_inv_hom {R : Sheaf J RingCat.{w}} {A B : SheafOfModules.{w} R} (e : A ≅ B)
    (U : Cᵒᵖ) (x : A.val.obj U) : Hom.app e.inv.val U (Hom.app e.hom.val U x) = x :=
  PresheafOfModules.hom_congr_apply (congrArg (fun g : A ⟶ A => g.val) e.hom_inv_id) U x

/-- An isomorphism of sheaves of modules is injective on sections. -/
theorem isoValApp_injective {R : Sheaf J RingCat.{w}} {A B : SheafOfModules.{w} R} (e : A ≅ B)
    (U : Cᵒᵖ) : Function.Injective (fun x : A.val.obj U => Hom.app e.hom.val U x) := by
  intro s t h
  rw [← isoValApp_inv_hom e U s, ← isoValApp_inv_hom e U t]
  exact congrArg _ h

end Stacks.SheafOfModules

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

/-- The sheafification unit of the tensor presheaf is natural in both arguments: the product of
two sections is carried to the product of their images. -/
theorem toSheafify_tensorProductIso
    {A A' B B' : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)}
    (e : A ≅ A') (f : B ≅ B') (U : Cᵒᵖ) (x : A.val.obj U) (y : B.val.obj U) :
    Hom.app (tensorProductIso O hO e f).hom.val U
        (Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO
          ((PresheafOfModules.tensorObj (O := O) (A.val) (B.val)))) U
          (x ⊗ₜ y)) =
      Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO
        ((PresheafOfModules.tensorObj (O := O) (A'.val) (B'.val)))) U
        (Hom.app e.hom.val U x ⊗ₜ Hom.app f.hom.val U y) :=
  (PresheafOfModules.hom_congr_apply ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction
    O hO).unit.naturality
    (e.hom.val ⊗ₘ f.hom.val)) U (x ⊗ₜ y)).symm

/-- **The left unit constraint of the sheaf tensor product, on sections**: it sends the product
of the unit section with a section `m` to `m`. -/
theorem toSheafify_tensorProductLeftUnitor
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) (U :
      Cᵒᵖ) (m : M.val.obj U) :
    Hom.app (tensorProductLeftUnitor O hO M).hom.val U
        (Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO
          ((PresheafOfModules.tensorObj (O := O)
            ((SheafOfModules.unit
              (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).val)
            (M.val)))) U
          (unitOne U ⊗ₜ m)) = m := by
  have leftUnitorApp : ∀ {R : CommRingCat.{w}} (N : ModuleCat.{w} R) (z : N),
      ConcreteCategory.hom (MonoidalCategory.leftUnitor N).hom ((1 : R) ⊗ₜ[R] z) = z :=
    fun N z => (ModuleCat.MonoidalCategory.leftUnitor_hom_apply 1 z).trans (one_smul _ z)
  have key : Stacks.SheafOfModules.TensorSheafification.toSheafify O hO
        ((PresheafOfModules.tensorObj (O := O)
          ((SheafOfModules.unit
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).val)
          (M.val))) ≫
        (tensorProductLeftUnitor O hO M).hom.val = (λ_ M.val).hom :=
    ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).unit_comp_map_eq_iff
      (tensorProductLeftUnitor O hO M).hom (λ_ M.val).hom).mpr rfl
  exact (PresheafOfModules.hom_congr_apply key U (unitOne U ⊗ₜ m)).trans (leftUnitorApp _ m)

/-- **If `A` is trivial then every section of `A ⊗ B` is a product** of a section of `A` and a
section of `B`.  Over a general `A` the sheafification unit is far from surjective on sections;
here the left unit constraint provides the inverse. -/
theorem exists_toSheafify_tmul_eq
    {A B : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
    (eA : A ≅ SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      (U : Cᵒᵖ)
    (z : ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (A)).obj (B))).val.obj U) :
    ∃ (m : A.val.obj U) (n : B.val.obj U),
      Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO
        ((PresheafOfModules.tensorObj (O := O) (A.val) (B.val)))) U
        (m ⊗ₜ n) = z := by
  set ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (A)).obj (B)) ≅ B :=
    tensorProductIso O hO eA (Iso.refl B) ≪≫ tensorProductLeftUnitor O hO B with hψ
  refine ⟨Hom.app eA.inv.val U (unitOne U), Hom.app ψ.hom.val U z,
    Stacks.SheafOfModules.isoValApp_injective ψ U ?_⟩
  show Hom.app ψ.hom.val U _ = Hom.app ψ.hom.val U z
  rw [hψ]
  show Hom.app (tensorProductLeftUnitor O hO B).hom.val U
      (Hom.app (tensorProductIso O hO eA (Iso.refl B)).hom.val U _) = _
  rw [toSheafify_tensorProductIso O hO eA (Iso.refl B) U (Hom.app eA.inv.val U (unitOne U))]
  have h1 : Hom.app eA.hom.val U (Hom.app eA.inv.val U (unitOne U)) = unitOne U :=
    Stacks.SheafOfModules.isoValApp_hom_inv eA U (unitOne U)
  rw [h1]
  exact toSheafify_tensorProductLeftUnitor O hO B U _

/-- **The multiplication `L ⊗ L^{⊗ -1} ≅ 𝒪`**, with the first factor read as `L` itself rather
than as its first tensor power.  This is
`Stacks.SheafOfModules.Invertible.tensorPowerMulIsoNegOne` precomposed with the identification
`L ≅ L^{⊗ 1}`, so it is the multiplication that
`Stacks.SheafOfModules.Invertible.sectionMulNegOne` evaluates. -/
def mulNegOneIso (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
  O hO))
    [_root_.AlgebraicGeometry.SheafOfModules.IsInvertible O hO L] :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (L)).obj ((tensorPower O hO L (-1)))) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) :=
  tensorProductIso O hO (tensorPowerOneIso O hO L).symm (Iso.refl _) ≪≫
    tensorPowerMulIsoNegOne O hO L

/-- On the product of two sections, `mulNegOneIso` is `sectionMulNegOne`. -/
theorem mulNegOneIso_toSheafify (L : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [_root_.AlgebraicGeometry.SheafOfModules.IsInvertible O hO L] (U : Cᵒᵖ) (s : L.val.obj U)
    (t : (tensorPower O hO L (-1)).val.obj U) :
    Hom.app (mulNegOneIso O hO L).hom.val U
        (Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO
          ((PresheafOfModules.tensorObj (O := O) (L.val) ((tensorPower O hO L
            (-1)).val)))) U (s ⊗ₜ t)) =
      sectionMulNegOne O hO L U s t :=
  congrArg (fun z => Hom.app (tensorPowerMulIsoNegOne O hO L).hom.val U z)
    (toSheafify_tensorProductIso O hO (tensorPowerOneIso O hO L).symm
      (Iso.refl (tensorPower O hO L (-1))) U s t)

end Stacks.SheafOfModules.Invertible

/-! ### The pulled-back multiplication -/

namespace Stacks.AlgebraicGeometry.PicardBaseChange

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

/-- The unit of the pullback adjunction, read on sections of the structure sheaf and composed
with `p^* 𝒪_X ≅ 𝒪_Y`, is the ring map `Γ(X, 𝒪_X) → Γ(Y, 𝒪_Y)`. -/
theorem pullbackUnitIso_hom_pullbackUnitSections (r : Γ(X, ⊤)) :
    Hom.app (pullbackUnitIso p).hom.val (op ⊤)
        (pullbackUnitSections p (SheafOfModules.unit X.ringCatSheaf) ⊤ r) =
      (p.app ⊤).hom r := by
  have : (SheafOfModules.pushforward.{u} p.toRingCatSheafHom).IsRightAdjoint := by
    show (Scheme.Modules.pushforward p).IsRightAdjoint
    infer_instance
  have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    (φ := p.toRingCatSheafHom)
  rw [Adjunction.homEquiv_unit] at h
  exact PresheafOfModules.hom_congr_apply
    (congrArg (fun m : SheafOfModules.unit X.ringCatSheaf ⟶
      (SheafOfModules.pushforward.{u} p.toRingCatSheafHom).obj
        (SheafOfModules.unit Y.ringCatSheaf) => m.val) h) (op ⊤) r

variable (L : X.Modules) [IsInvertible X.presheaf X.ringCatSheaf.property L]

/-- **The pullback of the multiplication `L ⊗ L^{⊗ -1} ≅ 𝒪_X`**, as an isomorphism
`p^* L ⊗ p^*(L^{⊗ -1}) ≅ 𝒪_Y`.  Each of the three factors is an isomorphism: the Tag 01CD
comparison, the pullback of `Stacks.SheafOfModules.Invertible.mulNegOneIso`, and
`p^* 𝒪_X ≅ 𝒪_Y`. -/
def pullbackMulNegOneIso :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (Y.presheaf) (forget₂ CommRingCat RingCat)
        (Y.ringCatSheaf.property)⟩).obj (((Scheme.Modules.pullback p).obj L))).obj
          (((Scheme.Modules.pullback p).obj (tensorPowerModule L (-1))))) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  (pullbackTensorIso p L (tensorPowerModule L (-1))).symm ≪≫
    (Scheme.Modules.pullback p).mapIso
      (mulNegOneIso X.presheaf X.ringCatSheaf.property L) ≪≫ pullbackUnitIso p

/-- **The pullback of a product is the product of the pullbacks**, on global sections. -/
theorem pullbackMulNegOneIso_pullbackUnitSections (s : Γ(L, ⊤))
    (t : Γ(tensorPowerModule L (-1), ⊤)) :
    Hom.app (pullbackMulNegOneIso p L).hom.val (op ⊤)
        (Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify Y.presheaf
          Y.ringCatSheaf.property
          ((PresheafOfModules.tensorObj (O := Y.presheaf)
            (((Scheme.Modules.pullback p).obj L).val)
            (((Scheme.Modules.pullback p).obj (tensorPowerModule L (-1))).val)))) (op ⊤)
          (pullbackUnitSections p L ⊤ s ⊗ₜ
            pullbackUnitSections p (tensorPowerModule L (-1)) ⊤ t)) =
      (p.app ⊤).hom (globalSectionsMulNegOne L s t) := by
  have h1 := (Stacks.RingedSpace.comparison_pullbackUnit_tmul p.toLRSHom.toShHom L
    (tensorPowerModule L (-1)) (op ⊤) s t).symm
  refine Eq.trans (congrArg (fun z => Hom.app (pullbackMulNegOneIso p L).hom.val (op ⊤) z) h1) ?_
  refine Eq.trans (congrArg (fun z => Hom.app (pullbackUnitIso p).hom.val (op ⊤)
      (Hom.app ((Scheme.Modules.pullback p).map
        (mulNegOneIso X.presheaf X.ringCatSheaf.property L).hom).val (op ⊤) z))
    (Stacks.SheafOfModules.isoValApp_inv_hom
      (pullbackTensorIso p L (tensorPowerModule L (-1))) (op ⊤) _)) ?_
  refine Eq.trans (congrArg (fun z => Hom.app (pullbackUnitIso p).hom.val (op ⊤) z)
    (pullbackUnitSections_naturality_module p
      (mulNegOneIso X.presheaf X.ringCatSheaf.property L).hom ⊤
      (Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf
        X.ringCatSheaf.property
        ((PresheafOfModules.tensorObj (O := X.presheaf) (L.val)
          ((tensorPowerModule L (-1)).val)))) (op ⊤)
        (s ⊗ₜ t)))) ?_
  refine Eq.trans (congrArg (fun z => Hom.app (pullbackUnitIso p).hom.val (op ⊤)
    (pullbackUnitSections p (SheafOfModules.unit X.ringCatSheaf) ⊤ z))
    (mulNegOneIso_toSheafify X.presheaf X.ringCatSheaf.property L (op ⊤) s t)) ?_
  exact pullbackUnitIso_hom_pullbackUnitSections p (globalSectionsMulNegOne L s t)

/-- The product of a global section of `p^* L` and a global section of `p^*(L^{⊗ -1})`. -/
def pullbackMulNegOne (m : Γ((Scheme.Modules.pullback p).obj L, ⊤))
    (n : Γ((Scheme.Modules.pullback p).obj (tensorPowerModule L (-1)), ⊤)) : Γ(Y, ⊤) :=
  Hom.app (pullbackMulNegOneIso p L).hom.val (op ⊤)
    (Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify Y.presheaf
      Y.ringCatSheaf.property
      ((PresheafOfModules.tensorObj (O := Y.presheaf)
        (((Scheme.Modules.pullback p).obj L).val)
        (((Scheme.Modules.pullback p).obj (tensorPowerModule L (-1))).val)))) (op ⊤) (m ⊗ₜ n))

/-- The same product as a linear map out of the tensor product of the two modules of global
sections.  Being a composition of linear maps, it needs no bilinearity verification. -/
def pullbackMulNegOneLinear :
    Γ((Scheme.Modules.pullback p).obj L, ⊤) ⊗[Γ(Y, ⊤)]
        Γ((Scheme.Modules.pullback p).obj (tensorPowerModule L (-1)), ⊤) →ₗ[Γ(Y, ⊤)] Γ(Y, ⊤) :=
  let T : Y.Modules :=
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (Y.presheaf) (forget₂ CommRingCat RingCat)
        (Y.ringCatSheaf.property)⟩).obj (((Scheme.Modules.pullback p).obj L))).obj
          (((Scheme.Modules.pullback p).obj (tensorPowerModule L (-1)))))
  let Θ : Γ(T, ⊤) →ₗ[Γ(Y, ⊤)] Γ(Y, ⊤) :=
    ((pullbackMulNegOneIso p L).hom.val.app (op ⊤)).hom
  let B : Γ((Scheme.Modules.pullback p).obj L, ⊤) ⊗[Γ(Y, ⊤)]
      Γ((Scheme.Modules.pullback p).obj (tensorPowerModule L (-1)), ⊤) →ₗ[Γ(Y, ⊤)] Γ(T, ⊤) :=
    ((Stacks.SheafOfModules.TensorSheafification.toSheafify Y.presheaf Y.ringCatSheaf.property
      ((PresheafOfModules.tensorObj (O := Y.presheaf)
        (((Scheme.Modules.pullback p).obj L).val)
        (((Scheme.Modules.pullback p).obj (tensorPowerModule L (-1))).val)))).app (op ⊤)).hom
  Θ.comp B

/-- On a pure tensor, `pullbackMulNegOneLinear` is `pullbackMulNegOne`. -/
@[simp]
theorem pullbackMulNegOneLinear_tmul (m : Γ((Scheme.Modules.pullback p).obj L, ⊤))
    (n : Γ((Scheme.Modules.pullback p).obj (tensorPowerModule L (-1)), ⊤)) :
    pullbackMulNegOneLinear p L (m ⊗ₜ[Γ(Y, ⊤)] n) = pullbackMulNegOne p L m n := rfl

/-- **If the pullback of `L` is trivial then the pulled-back multiplication takes the value
`1`.** -/
theorem exists_pullbackMulNegOne_eq_one
    (hL : IsTrivial Y.presheaf Y.ringCatSheaf.property ((Scheme.Modules.pullback p).obj L)) :
    ∃ (m : Γ((Scheme.Modules.pullback p).obj L, ⊤))
      (n : Γ((Scheme.Modules.pullback p).obj (tensorPowerModule L (-1)), ⊤)),
      pullbackMulNegOne p L m n = 1 := by
  obtain ⟨eA⟩ := hL
  obtain ⟨m, n, hmn⟩ := exists_toSheafify_tmul_eq Y.presheaf Y.ringCatSheaf.property eA (op ⊤)
    (Hom.app (pullbackMulNegOneIso p L).inv.val (op ⊤) (unitOne (op ⊤)))
  refine ⟨m, n, ?_⟩
  refine Eq.trans (congrArg
    (fun z => Hom.app (pullbackMulNegOneIso p L).hom.val (op ⊤) z) hmn) ?_
  exact Stacks.SheafOfModules.isoValApp_hom_inv (pullbackMulNegOneIso p L) (op ⊤) _

/-- **The multiplication becomes surjective after a trivializing base change**, for an
arbitrary cartesian square with affine bases.  This is the one goal to which
`Module.Invertible.exists_mulEquiv_of_lTensor_surjective` reduces the multiplication clause of
Tag 0CDX. -/
theorem surjective_lTensor_globalSectionsMulNegOneLinear
    {S T : Scheme.{u}} {q : T ⟶ S} {iX : X ⟶ S} {k : Y ⟶ T}
    (H : IsPullback p k iX q) [IsAffine S] [IsAffine T] [Flat q]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [Algebra Γ(X, ⊤) Γ(Y, ⊤)]
    (halg : ∀ r, algebraMap Γ(X, ⊤) Γ(Y, ⊤) r = (p.appLE ⊤ ⊤ (le_preimage_top p ⊤)).hom r)
    (hL : IsTrivial Y.presheaf Y.ringCatSheaf.property ((Scheme.Modules.pullback p).obj L)) :
    Function.Surjective ((globalSectionsMulNegOneLinear L).lTensor Γ(Y, ⊤)) := by
  have hLinv : IsInvertible X.sheaf.obj X.ringCatSheaf.property L := ‹_›
  have hLqc : L.IsQuasicoherent := AlgebraicGeometry.isQuasicoherent_of_isInvertible L
  have hNinv : IsInvertible X.presheaf X.ringCatSheaf.property (tensorPowerModule L (-1)) :=
    tensorPower_isInvertible X.presheaf X.ringCatSheaf.property L (-1)
  have hNinv' : IsInvertible X.sheaf.obj X.ringCatSheaf.property (tensorPowerModule L (-1)) :=
    hNinv
  have hNqc : (tensorPowerModule L (-1)).IsQuasicoherent :=
    AlgebraicGeometry.isQuasicoherent_of_isInvertible (tensorPowerModule L (-1))
  let modM : Module Γ(X, ⊤) Γ((Scheme.Modules.pullback p).obj L, ⊤) :=
    baseModule p ((Scheme.Modules.pullback p).obj L) ⊤
  let modN : Module Γ(X, ⊤)
      Γ((Scheme.Modules.pullback p).obj (tensorPowerModule L (-1)), ⊤) :=
    baseModule p ((Scheme.Modules.pullback p).obj (tensorPowerModule L (-1))) ⊤
  have towerM : IsScalarTower Γ(X, ⊤) Γ(Y, ⊤) Γ((Scheme.Modules.pullback p).obj L, ⊤) :=
    Stacks.FlatSectionsDescent.isScalarTower_of_smul_eq (RingHom.id _) (fun _ _ => rfl)
      ((p.appLE ⊤ ⊤ (le_preimage_top p ⊤)).hom) (fun _ _ => rfl) (fun a => (halg a).symm)
  have towerN : IsScalarTower Γ(X, ⊤) Γ(Y, ⊤)
      Γ((Scheme.Modules.pullback p).obj (tensorPowerModule L (-1)), ⊤) :=
    Stacks.FlatSectionsDescent.isScalarTower_of_smul_eq (RingHom.id _) (fun _ _ => rfl)
      ((p.appLE ⊤ ⊤ (le_preimage_top p ⊤)).hom) (fun _ _ => rfl) (fun a => (halg a).symm)
  have hbcM : IsBaseChange Γ(Y, ⊤) (pullbackAppTopLinear p L) :=
    isBaseChange_appTop_pullbackSections H L halg _ (fun _ => rfl)
  have hbcN : IsBaseChange Γ(Y, ⊤) (pullbackAppTopLinear p (tensorPowerModule L (-1))) :=
    isBaseChange_appTop_pullbackSections H (tensorPowerModule L (-1)) halg _ (fun _ => rfl)
  obtain ⟨m₀, n₀, hone⟩ := exists_pullbackMulNegOne_eq_one p L hL
  refine Module.surjective_lTensor_of_pairing (globalSectionsMulNegOneLinear L) hbcM hbcN
    (pullbackMulNegOneLinear p L) (fun s t => ?_) m₀ n₀ hone
  rw [pullbackMulNegOneLinear_tmul, globalSectionsMulNegOneLinear_tmul, halg, appLE_top_top]
  rw [show (pullbackAppTopLinear p L) s = pullbackUnitSections p L ⊤ s from
      pullbackSectionsHom_top p L s,
    show (pullbackAppTopLinear p (tensorPowerModule L (-1))) t =
        pullbackUnitSections p (tensorPowerModule L (-1)) ⊤ t from
      pullbackSectionsHom_top p (tensorPowerModule L (-1)) t]
  exact pullbackMulNegOneIso_pullbackUnitSections p L s t

/-- **Stacks Project, Tag 0CDX, the clause about the multiplication.** For a quasi-compact,
quasi-separated scheme `X` over `A`, a faithfully flat ring map `φ : A →+* B` and an invertible
`𝒪_X`-module `L` whose pullback to `X_B` is trivial, the multiplication

`Γ(X, L) ⊗_{Γ(X, 𝒪_X)} Γ(X, L^{⊗ -1}) ⟶ Γ(X, 𝒪_X)`

is an isomorphism.  The multiplication is `globalSectionsMulNegOne`, which is Tag 01CU's
coherent multiplication in degrees `(1, -1)` by
`Stacks.SheafOfModules.Invertible.tensorPowerCoherence_mulIso_one_negOne`; the `@[stacks 0CDX]`
attribute for this clause is on the transcription in
`StacksFrontier/AlgebraicGeometry/PicardBaseChange/CoherentMul.lean`, which this theorem proves. -/
theorem exists_mulEquiv_globalSections_of_faithfullyFlat_trivialization
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (hφ : φ.FaithfullyFlat)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules) [IsInvertible X.presheaf X.ringCatSheaf.property L]
    (hL : IsTrivial
      (Limits.pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf
      (Limits.pullback f (Spec.map (CommRingCat.ofHom φ))).ringCatSheaf.property
      ((Scheme.Modules.pullback
        (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).obj L)) :
    ∃ e : Γ(L, ⊤) ⊗[Γ(X, ⊤)] Γ(tensorPowerModule L (-1), ⊤) ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤),
      ∀ s t, e (s ⊗ₜ[Γ(X, ⊤)] t) = globalSectionsMulNegOne L s t := by
  have hq : Flat (Spec.map (CommRingCat.ofHom φ)) := Flat.SpecMap_iff.mpr hφ.flat
  let algXY : Algebra Γ(X, ⊤) Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom φ)), ⊤) :=
    (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom φ))).appTop.hom.toAlgebra
  have halg : ∀ r, algebraMap Γ(X, ⊤)
      Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom φ)), ⊤) r =
      ((Limits.pullback.fst f (Spec.map (CommRingCat.ofHom φ))).appLE ⊤ ⊤
        (le_preimage_top _ ⊤)).hom r := by
    intro r
    rw [appLE_top_top]
    rfl
  have hff : Module.FaithfullyFlat Γ(X, ⊤)
      Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom φ)), ⊤) :=
    faithfullyFlat_appTop_pullback_fst hφ f
  have hinvM : Module.Invertible Γ(X, ⊤) Γ(L, ⊤) :=
    invertible_globalSections_of_faithfullyFlat_trivialization φ hφ f L hL
  have hinvN : Module.Invertible Γ(X, ⊤) Γ(tensorPowerModule L (-1), ⊤) :=
    invertible_globalSections_tensorInverse_of_faithfullyFlat_trivialization φ hφ f L hL
  have hsurj := surjective_lTensor_globalSectionsMulNegOneLinear
    (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom φ))) L
    (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom φ))) halg hL
  obtain ⟨e, he⟩ := Module.Invertible.exists_mulEquiv_of_lTensor_surjective
    Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom φ)), ⊤)
    (globalSectionsMulNegOneLinear L) hsurj
  exact ⟨e, fun s t => (he s t).trans (globalSectionsMulNegOneLinear_tmul L s t)⟩

end Stacks.AlgebraicGeometry.PicardBaseChange

end
