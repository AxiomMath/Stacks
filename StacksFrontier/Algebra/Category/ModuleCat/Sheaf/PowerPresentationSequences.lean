module

public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksCore.Tactic.StacksAttribute

/-!
# Presenting symmetric and exterior powers of a sheaf of modules

Let `O` be a sheaf of commutative rings on a site and let `M₂ ⟶ M₁ ⟶ M ⟶ 0` be a presentation
of a sheaf of `O`-modules. Stacks Tag 01CJ asserts that in every degree `n ≥ 1` there are exact
sequences

* `M₂ ⊗ Sym^{n-1}(M₁) ⟶ Symⁿ(M₁) ⟶ Symⁿ(M) ⟶ 0`,
* `M₂ ⊗ ⋀^{n-1}(M₁) ⟶ ⋀ⁿ(M₁) ⟶ ⋀ⁿ(M) ⟶ 0`.

This file builds the two maps of those sequences and shows that they compose to zero. The
symmetric and exterior algebras enter as a sheaf of graded algebras together with a degree-one
generator satisfying the universal property `SheafOfModules.GradedAlgebra.IsUniversal`, which
determines them up to a unique isomorphism of graded algebras (`IsUniversal.pieceIso`,
`IsUniversal.descIsIso`). Both sequences are instances of one construction, differing only in
the property `P` of the universal property: `SquareZero` for exterior powers,
`PairwiseCommutes` for symmetric ones. Exactness at the middle term and epimorphy of the second
map are not proved here.

## Main definitions

* `PresheafOfModules.tensorSheafUnit`: the unit of `PresheafOfModules.sheafificationAdjunction`
  at the objectwise tensor product of two sheaves of modules.
* `PresheafOfModules.tensorSheafDesc`: a morphism out of the objectwise tensor product of two
  presheaves of modules descended to the tensor product of the two sheaves.
* `SheafOfModules.GradedAlgebra.IsUniversal.descComp`: the homomorphism of graded algebras
  induced by a morphism `p : M₁ ⟶ M` of sheaves of modules, the unique unital homomorphism out
  of a universal graded algebra on `M₁` extending `p` followed by a generator of a graded
  algebra on `M`.
* `SheafOfModules.GradedAlgebra.generatorMulPresheaf` and
  `SheafOfModules.GradedAlgebra.generatorMul`: multiplication by a degree-one generator,
  `M ⊗ A_k ⟶ A_{1+k}`, `s ⊗ y ↦ ι s · y`, on objectwise tensor products and on the tensor
  product of sheaves.
* `SheafOfModules.GradedAlgebra.presentationShortComplex`: the resulting three-term complex,
  with `exteriorPresentationShortComplex` and `symmetricPresentationShortComplex` its two
  instances.

## Main results

* `SheafOfModules.GradedAlgebra.squareZero_comp` and
  `SheafOfModules.GradedAlgebra.pairwiseCommutes_comp`: both conditions on a degree-one
  generator are inherited by its composite with a morphism of sheaves of modules.
* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.comp_iso`: an exterior algebra of `N` is an
  exterior algebra of every sheaf of modules isomorphic to `N`.
* `PresheafOfModules.tensorSheafDesc_unit` computes the descended morphism on the image of a
  pure tensor, and `PresheafOfModules.tensorSheaf_hom_ext` says that those images determine a
  morphism out of a tensor product of sheaves.
* `SheafOfModules.GradedAlgebra.generatorMul_unit`: the pure-tensor formula for the first map
  of the sequence.
* `SheafOfModules.GradedAlgebra.IsUniversal.epi_descComp_app_one`: in degree one, the second
  map is an epimorphism when `p` followed by the generator is.
* `SheafOfModules.GradedAlgebra.generatorMul_comp_descComp_eq_zero`: the two maps compose to
  zero as soon as `M₂ ⟶ M₁ ⟶ M` does.
* `SheafOfModules.GradedAlgebra.presentationShortComplex_X₁`, `_X₂`, `_X₃`, `_g` and
  `_f_unit` identify the terms and the two maps of the complex.
* `SheafOfModules.zero_val_app_apply` and `SheafOfModules.comp_val_app_apply` evaluate the zero
  morphism and a composite of morphisms of sheaves of modules on a local section.

## Implementation notes

The site universes `u`, `v`, the universe `w` of the sheaf of rings and the universe `a` of the
homogeneous pieces are independent.

`A.mul 1 k` lands in `A.piece (1 + k)`, while indexing by natural numbers gives
`A.piece ((k + 1 : ℕ) : ℤ)`; these are equal but not definitionally so.
`presentationShortComplex` therefore takes the target degree `n` and a proof `1 + k = n`, and
transports along `eqToHom`.

The source of the component of the unit of `PresheafOfModules.sheafificationAdjunction` is
`(𝟭 _).obj (tensorObj F.val G.val)`; `tensorSheafUnit` spells it as `tensorObj F.val G.val`, so
that a pure tensor typechecks against it at the transparency `rw` uses.

## References

* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 00DO](https://stacks.math.columbia.edu/tag/00DO)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Sheaf PresheafOfModules

open scoped TensorProduct

universe v u w t a

namespace SheafOfModules

/-! ### Values of the zero morphism and of a composite on a local section -/

section Sections

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {M N P : SheafOfModules.{a} R}

/-- The zero morphism of sheaves of modules sends every local section to zero. -/
theorem zero_val_app_apply (U : Cᵒᵖ) (x : M.val.obj U) : (0 : M ⟶ N).val.app U x = 0 := rfl

/-- A composite of morphisms of sheaves of modules acts on local sections by composition. -/
theorem comp_val_app_apply (φ : M ⟶ N) (ψ : N ⟶ P) (U : Cᵒᵖ) (x : M.val.obj U) :
    (φ ≫ ψ).val.app U x = ψ.val.app U (φ.val.app U x) := rfl

end Sections

end SheafOfModules

namespace PresheafOfModules

/-! ### Morphisms out of the tensor product of two sheaves of modules

The tensor product of two sheaves of modules is the sheafification of the objectwise tensor
product of the underlying presheaves, so a morphism out of it is the same thing as a morphism
out of that presheaf, and is determined by its values on the images of pure tensors. -/

section TensorDesc

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]
  {F G Q : SheafOfModules.{a} (toRingCat J Osharp)}

/-- The morphism from the objectwise tensor product of two sheaves of modules to their tensor
product, exhibiting the latter as the sheafification of the former. -/
noncomputable abbrev tensorSheafUnit (F G : SheafOfModules.{a} (toRingCat J Osharp)) :
    tensorObj F.val G.val ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj F).obj G).val :=
  (PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj F.val G.val)

/-- A morphism out of the tensor product of two sheaves of modules, obtained from a morphism out
of the objectwise tensor product of the underlying presheaves. -/
noncomputable def tensorSheafDesc (φ : tensorObj F.val G.val ⟶ Q.val) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj F).obj G ⟶ Q :=
  (sheafificationHomEquiv (𝟙 (toRingCat J Osharp).obj)).symm φ

/-- The sheafification bijection for the objectwise tensor product is restriction along
`tensorSheafUnit`. -/
theorem tensorSheafificationHomEquiv_app_apply
    (f : ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj F).obj G ⟶ Q) (U : Cᵒᵖ)
    (z : (tensorObj F.val G.val).obj U) :
    Hom.app (sheafificationHomEquiv (𝟙 (toRingCat J Osharp).obj) f) U z =
      f.val.app U ((tensorSheafUnit F G).app U z) :=
  rfl

/-- The descended morphism `tensorSheafDesc φ` agrees with `φ` on the image of a pure tensor. -/
@[simp]
theorem tensorSheafDesc_unit (φ : tensorObj F.val G.val ⟶ Q.val) (U : Cᵒᵖ) (x : F.val.obj U)
    (y : G.val.obj U) :
    (tensorSheafDesc φ).val.app U ((tensorSheafUnit F G).app U (x ⊗ₜ y)) = Hom.app φ U (x ⊗ₜ y) :=
  (tensorSheafificationHomEquiv_app_apply (tensorSheafDesc φ) U (x ⊗ₜ y)).symm.trans
    (congrArg (fun h : tensorObj F.val G.val ⟶ Q.val => Hom.app h U (x ⊗ₜ y))
      ((sheafificationHomEquiv (𝟙 (toRingCat J Osharp).obj)).apply_symm_apply φ))

/-- Two morphisms out of the tensor product of two sheaves of modules which agree on the images
of pure tensors of local sections are equal. -/
theorem tensorSheaf_hom_ext {φ ψ : ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj F).obj G ⟶
    Q}
    (h : ∀ (U : Cᵒᵖ) (x : F.val.obj U) (y : G.val.obj U),
      φ.val.app U ((tensorSheafUnit F G).app U (x ⊗ₜ y)) =
        ψ.val.app U ((tensorSheafUnit F G).app U (x ⊗ₜ y))) :
    φ = ψ := by
  refine (sheafificationHomEquiv (𝟙 (toRingCat J Osharp).obj)).injective
    (tensorObj_hom_ext fun U x y => ?_)
  exact (tensorSheafificationHomEquiv_app_apply φ U _).trans
    ((h U x y).trans (tensorSheafificationHomEquiv_app_apply ψ U _).symm)

end TensorDesc

end PresheafOfModules

namespace SheafOfModules.GradedAlgebra

/-! ### Transporting a degree-one generator along a morphism of sheaves of modules -/

section Generators

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {M N : SheafOfModules.{a} R} {B : GradedAlgebra.{t, a} R}

/-- A square-zero degree-one generator stays square-zero after composition with a morphism of
sheaves of modules. -/
theorem squareZero_comp (p : M ⟶ N) {κ : N ⟶ B.piece 1} (hκ : SquareZero κ) :
    SquareZero (p ≫ κ) := fun U s => hκ U (p.val.app U s)

/-- A degree-one generator with pairwise commuting image stays so after composition with a
morphism of sheaves of modules. -/
theorem pairwiseCommutes_comp (p : M ⟶ N) {κ : N ⟶ B.piece 1} (hκ : PairwiseCommutes κ) :
    PairwiseCommutes (p ≫ κ) := fun U s u => hκ U (p.val.app U s) (p.val.app U u)

/-- If `B` is an exterior algebra of `N` with degree-one generator `κ` and `c : M ⟶ N` is an
isomorphism, then `B` is an exterior algebra of `M` with degree-one generator `c ≫ κ`. -/
theorem IsExteriorAlgebra.comp_iso {κ : N ⟶ B.piece 1} (hB : IsExteriorAlgebra B κ)
    (c : M ⟶ N) (hc : IsIso c) : IsExteriorAlgebra B (c ≫ κ) := by
  have := hc
  refine ⟨squareZero_comp c hB.1, fun D lam hlam => ?_⟩
  obtain ⟨g, hg, hu⟩ := hB.2 D (inv c ≫ lam) (squareZero_comp (inv c) hlam)
  refine ⟨g, ?_, fun h hh => hu h ?_⟩
  · change (c ≫ κ) ≫ g.app 1 = lam
    simp [hg]
  · change κ ≫ h.app 1 = inv c ≫ lam
    simp [← show (c ≫ κ) ≫ h.app 1 = lam from hh]

end Generators

namespace IsUniversal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {M N : SheafOfModules.{a} R} {A B : GradedAlgebra.{t, a} R}
  {P : ∀ B : GradedAlgebra.{t, a} R, (M ⟶ B.piece 1) → Prop} {ι : M ⟶ A.piece 1}

/-- The homomorphism of graded algebras induced by a morphism `p : M ⟶ N` of sheaves of modules:
the unique unital homomorphism out of a graded algebra universal for `P` on `M` whose
restriction to the generator is `p` followed by a generator of a graded algebra on `N`. -/
noncomputable def descComp (hA : IsUniversal P A ι) (p : M ⟶ N) (κ : N ⟶ B.piece 1)
    (hP : P B (p ≫ κ)) : UnitalHom A B :=
  hA.desc B (p ≫ κ) hP

/-- The comparison homomorphism restricts on the generator to `p` followed by `κ`. -/
theorem descComp_extends (hA : IsUniversal P A ι) (p : M ⟶ N) (κ : N ⟶ B.piece 1)
    (hP : P B (p ≫ κ)) : ι ≫ (hA.descComp p κ hP).app 1 = p ≫ κ :=
  hA.desc_extends B (p ≫ κ) hP

/-- A unital homomorphism restricting on the generator to `p` followed by `κ` is the comparison
homomorphism. -/
theorem descComp_unique (hA : IsUniversal P A ι) (p : M ⟶ N) (κ : N ⟶ B.piece 1)
    (hP : P B (p ≫ κ)) {g : UnitalHom A B} (hg : ι ≫ g.app 1 = p ≫ κ) :
    g = hA.descComp p κ hP :=
  hA.desc_unique B (p ≫ κ) hP hg

/-- In degree one the comparison homomorphism is an epimorphism as soon as `p` followed by the
generator of `B` is. -/
theorem epi_descComp_app_one (hA : IsUniversal P A ι) (p : M ⟶ N) (κ : N ⟶ B.piece 1)
    (hP : P B (p ≫ κ)) [Epi (p ≫ κ)] : Epi ((hA.descComp p κ hP).app 1) :=
  epi_of_epi_fac (hA.descComp_extends p κ hP)

end IsUniversal

/-! ### Multiplication by a degree-one generator -/

section Tensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  {M : SheafOfModules.{a} (toRingCat J Osharp)}
  {A : GradedAlgebra.{w, a} (toRingCat J Osharp)}

/-- Multiplication by a degree-one generator, `s ⊗ y ↦ ι s · y`, as a morphism out of the
objectwise tensor product of the underlying presheaves. -/
noncomputable def generatorMulPresheaf (ι : M ⟶ A.piece 1) (k : ℤ) :
    tensorObj M.val (A.piece k).val ⟶ (A.piece (1 + k)).val :=
  tensorMk (fun U s y => (A.mul 1 k).app U (ι.val.app U s) y)
    (fun U s s' y => by rw [map_add, map_add, AddMonoidHom.add_apply])
    (fun U r s y => by rw [map_smul, (A.mul 1 k).map_smul_left])
    (fun U s y y' => by rw [map_add])
    (fun U r s y => by rw [(A.mul 1 k).map_smul_right])
    (fun {U V} f s y => by
      rw [restrictₛₗ_naturality_apply ι.val f s]
      exact (A.mul 1 k).naturality f (ι.val.app U s) y)

/-- `generatorMulPresheaf ι k` sends `s ⊗ y` to `ι s · y`. -/
@[simp]
theorem generatorMulPresheaf_tmul (ι : M ⟶ A.piece 1) (k : ℤ) (U : Cᵒᵖ) (s : M.val.obj U)
    (y : (A.piece k).val.obj U) :
    PresheafOfModules.Hom.app (generatorMulPresheaf ι k) U (s ⊗ₜ y) =
      (A.mul 1 k).app U (ι.val.app U s) y :=
  tensorMk_tmul _ _ _ _ _ _ _ _ _

variable [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]

/-- Multiplication by a degree-one generator, `M ⊗ A_k ⟶ A_{1+k}`, `s ⊗ y ↦ ι s · y`, as a
morphism of sheaves of modules. -/
noncomputable def generatorMul (ι : M ⟶ A.piece 1) (k : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj M).obj (A.piece k) ⟶ A.piece (1 + k) :=
  tensorSheafDesc (generatorMulPresheaf ι k)

/-- `generatorMul ι k` sends the image of `s ⊗ y` to `ι s · y`. -/
@[simp]
theorem generatorMul_unit (ι : M ⟶ A.piece 1) (k : ℤ) (U : Cᵒᵖ) (s : M.val.obj U)
    (y : (A.piece k).val.obj U) :
    (generatorMul ι k).val.app U ((tensorSheafUnit M (A.piece k)).app U (s ⊗ₜ y)) =
      (A.mul 1 k).app U (ι.val.app U s) y :=
  (tensorSheafDesc_unit (generatorMulPresheaf ι k) U s y).trans
    (generatorMulPresheaf_tmul ι k U s y)

/-- A morphism out of `A_{1+k}` applied to the image of `s ⊗ y` under `generatorMul ι k`. -/
private theorem generatorMul_comp_unit {X : SheafOfModules.{a} (toRingCat J Osharp)}
    (ι : M ⟶ A.piece 1) (k : ℤ) (g : A.piece (1 + k) ⟶ X) (U : Cᵒᵖ) (s : M.val.obj U)
    (y : (A.piece k).val.obj U) :
    (generatorMul ι k ≫ g).val.app U ((tensorSheafUnit M (A.piece k)).app U (s ⊗ₜ y)) =
      g.val.app U ((A.mul 1 k).app U (ι.val.app U s) y) :=
  (comp_val_app_apply (R := Stacks.SheafOfModules.Tensor.ringSheaf Osharp) _ _ U _).trans
    (congrArg (g.val.app U) (generatorMul_unit ι k U s y))

end Tensor

/-! ### The complex of Tag 01CJ -/

section Presentation

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]
  {M₂ M₁ M : SheafOfModules.{a} (toRingCat J Osharp)}
  {A B : GradedAlgebra.{w, a} (toRingCat J Osharp)}
  {Pr : ∀ B' : GradedAlgebra.{w, a} (toRingCat J Osharp), (M₁ ⟶ B'.piece 1) → Prop}
  {ι : M₁ ⟶ A.piece 1} {κ : M ⟶ B.piece 1}

/-- Multiplication by the degree-one image of `M₂`, followed by the comparison homomorphism, is
zero when the composite `M₂ ⟶ M₁ ⟶ M` is zero. -/
theorem generatorMul_comp_descComp_eq_zero (hA : IsUniversal Pr A ι) (q : M₂ ⟶ M₁) (p : M₁ ⟶ M)
    (hPr : Pr B (p ≫ κ)) (hqp : q ≫ p = 0) (k : ℤ) :
    generatorMul (q ≫ ι) k ≫ (hA.descComp p κ hPr).app (1 + k) =
      (CategoryTheory.Limits.HasZeroMorphisms.zero
        (C := SheafOfModules.{a} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} Osharp))
        _ _).zero := by
  have hz : q ≫ ι ≫ (hA.descComp p κ hPr).app 1 = 0 := by
    rw [hA.descComp_extends, ← Category.assoc, hqp, CategoryTheory.Limits.zero_comp]
  have hz0 : ∀ (U : Cᵒᵖ) (s : M₂.val.obj U),
      ((hA.descComp p κ hPr).app 1).val.app U ((q ≫ ι).val.app U s) = 0 := fun U s =>
    congrArg (fun m : M₂ ⟶ B.piece 1 => m.val.app U s) hz
  refine tensorSheaf_hom_ext fun U s y => ?_
  rw [generatorMul_comp_unit, (hA.descComp p κ hPr).map_mul 1 k U, hz0 U s, map_zero,
    AddMonoidHom.zero_apply]
  rfl

/-- The three-term complex of Tag 01CJ in degree `n = 1 + k`:
`M₂ ⊗ A_k ⟶ A_n ⟶ B_n`, where `A` is a graded algebra universal for `Pr` on `M₁` and `B` carries
a generator `κ` of `M`. -/
noncomputable def presentationShortComplex (hA : IsUniversal Pr A ι) (q : M₂ ⟶ M₁) (p : M₁ ⟶ M)
    (hPr : Pr B (p ≫ κ)) (hqp : q ≫ p = 0) (k n : ℤ) (hn : 1 + k = n) :
    ShortComplex (SheafOfModules.{a} (toRingCat J Osharp)) where
  X₁ := ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj M₂).obj (A.piece k)
  X₂ := A.piece n
  X₃ := B.piece n
  f := generatorMul (q ≫ ι) k ≫ eqToHom (congrArg A.piece hn)
  g := (hA.descComp p κ hPr).app n
  zero := by
    subst hn
    exact (congrArg
      (fun morphism : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, a, a} Osharp).obj
          M₂).obj (A.piece k) ⟶ A.piece (1 + k) =>
        morphism ≫ (hA.descComp p κ hPr).app (1 + k))
      (Category.comp_id (generatorMul (q ≫ ι) k))).trans
      (generatorMul_comp_descComp_eq_zero hA q p hPr hqp k)

/-- The first term of `presentationShortComplex` is `M₂ ⊗ A_k`. -/
@[simp]
theorem presentationShortComplex_X₁ (hA : IsUniversal Pr A ι) (q : M₂ ⟶ M₁) (p : M₁ ⟶ M)
    (hPr : Pr B (p ≫ κ)) (hqp : q ≫ p = 0) (k n : ℤ) (hn : 1 + k = n) :
    (presentationShortComplex hA q p hPr hqp k n hn).X₁ =
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj M₂).obj (A.piece k) := rfl

/-- The second term of `presentationShortComplex` is `A_n`. -/
@[simp]
theorem presentationShortComplex_X₂ (hA : IsUniversal Pr A ι) (q : M₂ ⟶ M₁) (p : M₁ ⟶ M)
    (hPr : Pr B (p ≫ κ)) (hqp : q ≫ p = 0) (k n : ℤ) (hn : 1 + k = n) :
    (presentationShortComplex hA q p hPr hqp k n hn).X₂ = A.piece n := rfl

/-- The third term of `presentationShortComplex` is `B_n`. -/
@[simp]
theorem presentationShortComplex_X₃ (hA : IsUniversal Pr A ι) (q : M₂ ⟶ M₁) (p : M₁ ⟶ M)
    (hPr : Pr B (p ≫ κ)) (hqp : q ≫ p = 0) (k n : ℤ) (hn : 1 + k = n) :
    (presentationShortComplex hA q p hPr hqp k n hn).X₃ = B.piece n := rfl

/-- The second map of `presentationShortComplex` is the comparison homomorphism in degree `n`. -/
@[simp]
theorem presentationShortComplex_g (hA : IsUniversal Pr A ι) (q : M₂ ⟶ M₁) (p : M₁ ⟶ M)
    (hPr : Pr B (p ≫ κ)) (hqp : q ≫ p = 0) (k n : ℤ) (hn : 1 + k = n) :
    (presentationShortComplex hA q p hPr hqp k n hn).g = (hA.descComp p κ hPr).app n := rfl

/-- The first map of the complex of Tag 01CJ on the image of a pure tensor: `s ⊗ y` goes to the
product of the degree-one image of `s` with `y`, reindexed from degree `1 + k` to degree `n`. -/
theorem presentationShortComplex_f_unit (hA : IsUniversal Pr A ι) (q : M₂ ⟶ M₁) (p : M₁ ⟶ M)
    (hPr : Pr B (p ≫ κ)) (hqp : q ≫ p = 0) (k n : ℤ) (hn : 1 + k = n) (U : Cᵒᵖ)
    (s : M₂.val.obj U) (y : (A.piece k).val.obj U) :
    (presentationShortComplex hA q p hPr hqp k n hn).f.val.app U
        ((tensorSheafUnit M₂ (A.piece k)).app U (s ⊗ₜ y)) =
      (eqToHom (congrArg A.piece hn)).val.app U
        ((A.mul 1 k).app U (ι.val.app U (q.val.app U s)) y) :=
  generatorMul_comp_unit (q ≫ ι) k (eqToHom (congrArg A.piece hn)) U s y

/-- The exterior half of the complex of Tag 01CJ:
`M₂ ⊗ ⋀^k(M₁) ⟶ ⋀ⁿ(M₁) ⟶ ⋀ⁿ(M)` for `n = 1 + k`. -/
noncomputable abbrev exteriorPresentationShortComplex (hA : IsExteriorAlgebra A ι)
    (hκ : SquareZero κ) (q : M₂ ⟶ M₁) (p : M₁ ⟶ M) (hqp : q ≫ p = 0) (k n : ℤ)
    (hn : 1 + k = n) : ShortComplex (SheafOfModules.{a} (toRingCat J Osharp)) :=
  presentationShortComplex hA.isUniversal q p (squareZero_comp p hκ) hqp k n hn

/-- The symmetric half of the complex of Tag 01CJ:
`M₂ ⊗ Sym^k(M₁) ⟶ Symⁿ(M₁) ⟶ Symⁿ(M)` for `n = 1 + k`. -/
noncomputable abbrev symmetricPresentationShortComplex (hA : IsSymmetricAlgebra A ι)
    (hκ : PairwiseCommutes κ) (q : M₂ ⟶ M₁) (p : M₁ ⟶ M) (hqp : q ≫ p = 0) (k n : ℤ)
    (hn : 1 + k = n) : ShortComplex (SheafOfModules.{a} (toRingCat J Osharp)) :=
  presentationShortComplex hA.isUniversal q p (pairwiseCommutes_comp p hκ) hqp k n hn

end Presentation

end SheafOfModules.GradedAlgebra
