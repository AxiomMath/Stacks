module

public import StacksFrontier.CategoryTheory.Abelian.Projective.Horseshoe
public import StacksFrontier.CategoryTheory.Limits.FunctorCategory.ShortExactColimit
public import StacksFrontier.Cotangent.SurjectionSiteAugmentationGraded
public import StacksFrontier.Cotangent.SurjectionSiteStructureResolution
public import StacksFrontier.Homology.Tor.CrossProduct

/-!
# `H_*(C_{B/A}, Ō) = Tor^A_*(B, B)`, and the first edge map of Remark 08RG

Let `A → B` be a ring map, let `κ = CommAlgCat.standardResolutionVarCardinal A B` and let
`C_{B/A}` be the polynomial site of [Stacks, Tag 08PR] in the small model
`CommAlgCat.smallBoundedPolynomialSite A B κ`, carrying the chaotic topology. Write
`H_i(C_{B/A}, -)` for the `i`-th left derived functor of the colimit over the opposite of that
model, at linear coefficients, which is [Stacks, Tag 08PF]'s definition of the homology of a
category. Let `Ō = 𝒪 ⊗_A B̲` be the presheaf of `CommAlgCat.smallPolynomialQuotientModule`, let
`𝒦 ⊆ Ō` be its augmentation ideal and `B̲` the constant presheaf on `B`. This file supplies
three things.

* The homology of `C_{B/A}` with **constant** coefficients: `H_0(C_{B/A}, B̲) = B` and
  `H_i(C_{B/A}, B̲) = 0` for `i > 0`.
* The identification of the **abutment** of Quillen's spectral sequence:
  `H_i(C_{B/A}, Ō) = Tor^A_i(B, B)` for every `i`.
* The **augmentation sequence** `0 → 𝒦 → Ō → B̲ → 0` of presheaves of `B`-modules, the
  resulting isomorphism `H_i(C_{B/A}, 𝒦) ≅ H_i(C_{B/A}, Ō)` for `i ≥ 1`, and the **first edge
  map family** of [Stacks, Remark 08RG],
  `Tor^A_i(B, B) ⟶ H_i(C_{B/A}, 𝒦/𝒦²)` for `i > 0`.

Nothing here needs `A → B` to be surjective.

## Main definitions

* `Stacks.algebraBaseChange`: base change of modules along the structure map of an algebra,
  `M ↦ S ⊗_R M`.
* `Stacks.extendScalarsNatIso`: Mathlib's `ModuleCat.extendScalars` along `algebraMap R S` is
  that base change.
* `Stacks.ChaoticSite.leftDerivedColimZeroConstIso`: `H_0(C, M̲) = M` for a constant diagram.
* `CommAlgCat.smallPolynomialQuotientModuleAug`: the augmentation `Ō ⟶ B̲` of presheaves of
  `B`-modules.
* `CommAlgCat.smallPolynomialAugmentationShortComplex`: the augmentation sequence
  `0 → 𝒦 → Ō → B̲ → 0`.
* `CommAlgCat.leftDerivedColimZeroConstPolynomialSiteIso`: `H_0(C_{B/A}, B̲) = B`.
* `CommAlgCat.leftDerivedColimSuccAugmentationIdealIso` and
  `CommAlgCat.leftDerivedColimAugmentationIdealIsoOfPos`:
  `H_i(C_{B/A}, 𝒦) ≅ H_i(C_{B/A}, Ō)` for `i ≥ 1`.
* `CommAlgCat.smallPolynomialStructureModuleProjectiveResolution`: `𝒪(U_•)` as a projective
  resolution of `B` over `A`.
* `CommAlgCat.smallPolynomialQuotientModuleMooreBaseChangeIso`: `Ō(U_•) = B ⊗_A 𝒪(U_•)`.
* `CommAlgCat.leftDerivedColimQuotientTorIso`: **`H_i(C_{B/A}, Ō) ≅ Tor^A_i(B, B)`.**
* `CommAlgCat.torToCotangentHomologyEdgeSucc` and `CommAlgCat.torToCotangentHomologyEdge`:
  **the first edge map family of Remark 08RG.**

## Main results

* `Stacks.ChaoticSite.isZero_leftDerivedColimSucc_const` and
  `CommAlgCat.isZero_leftDerivedColimSucc_constPolynomialSite`: `H_{i+1}(C, M̲) = 0`.
* `CommAlgCat.shortExact_smallPolynomialAugmentationShortComplex`: the augmentation sequence is
  short exact.
* `CommAlgCat.isIso_leftDerivedColimSucc_map_smallPolynomialAugmentationIdealPowι`: the
  inclusion `𝒦 ⊆ Ō` is invertible on `H_i(C_{B/A}, -)` for `i ≥ 1`.

## Implementation notes

**Constant coefficients.** The module half of [Stacks, Tag 08Q9]
(`Stacks.ChaoticSite.ModuleValued.moduleLeftDerivedColimitNatIso`) turns `H_i(C, -)` into the
homology of the Moore complex of the evaluation on a point resolution `U_•`; the evaluation of a
constant diagram is the constant simplicial object, whose Moore complex is Mathlib's
`ChainComplex.alternatingConst` by `Stacks.ChaoticSite.mooreComplexConstIso`. That complex has
homology `M` in degree zero and zero above.

**The abutment.** `Tor^A_i(B, B)` is read in the spelling the rest of this development uses for
the abutment, `RingTheory.TorProducts.torBaseChange`, which is the `i`-th left derived functor of
`ModuleCat.extendScalars (algebraMap A B)`. The Moore complex of `𝒪(U_•)` is a complex of free
`A`-modules (`CommAlgCat.module_free_smallPolynomialStructureModuleMooreComplex_X`) which
resolves `B` (`StacksFrontier.Cotangent.SurjectionSiteStructureResolution`), so it is a projective
resolution and its base change computes `Tor`; and `Ō(U_•)` is that base change, because
extension of scalars is additive and so commutes with the formation of the alternating face map
complex.

*Why the comparison `Stacks.extendScalarsNatIso` is needed.* Mathlib's
`ModuleCat.extendScalars f` forms `S ⊗_R M` using the `R`-module structure `Module.compHom S f`
on `S`, whereas `Ō` is built from `Algebra.TensorProduct`, which uses the `R`-module structure
carried by the algebra. Those two structures are equal but not definitionally so, so the two
tensor products are not the same term. They are reconciled at the level of the *instances*
rather than of elements: `ModuleCat.extendScalars f` is base change for the algebra structure
`f.toAlgebra` on the nose, and `toAlgebra_algebraMap` identifies `(algebraMap R S).toAlgebra`
with the ambient algebra structure. The resulting comparison is an equality of functors, not
merely an isomorphism.

**The edge map.** The long exact sequence of the left derived functors of the colimit is
`CategoryTheory.Functor.leftDerivedδ` and its companions. The presheaf category
`Cᵒᵖ ⥤ ModuleCat B` has enough projectives by
`Stacks.CategoryHomology.moduleDiagramsEnoughProjectives`, which is what makes those available.
Short exactness of the augmentation sequence is checked objectwise, by
`CategoryTheory.ShortComplex.shortExact_of_app`.

The target of the edge map is kept as `H_i(C_{B/A}, 𝒦/𝒦²)`; the identification of `𝒦ⁿ/𝒦ⁿ⁺¹`
with `Sym^n(Ω)`, which would rewrite it as `H^{-i}(L_{B/A})`, is not made here.

## References

* [Stacks Project, Tag 08RG](https://stacks.math.columbia.edu/tag/08RG)
* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

open scoped TensorProduct ChangeOfRings

universe u

namespace Stacks

/-! ### Extension of scalars along the structure map of an algebra -/

section ExtendScalars

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- **Base change of modules along the structure map of an `R`-algebra `S`**: `M ↦ S ⊗_R M`,
formed with the `R`-module structure on `S` coming from the algebra structure. Mathlib's
`ModuleCat.extendScalars` is the same construction formed instead with the `R`-module structure
`Module.compHom S (algebraMap R S)` on `S`, and `Stacks.extendScalarsNatIso` identifies the
two. -/
def algebraBaseChange : ModuleCat.{u} R ⥤ ModuleCat.{u} S where
  obj M := ModuleCat.of S (S ⊗[R] (M : Type u))
  map f := ModuleCat.ofHom (LinearMap.baseChange S f.hom)
  map_id M := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    induction x using TensorProduct.inductionOn with
    | tmul s m => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  map_comp f g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    induction x using TensorProduct.inductionOn with
    | tmul s m => simp
    | add x y hx hy => simp only [map_add, hx, hy]

/-- A morphism out of a base change `S ⊗_R M` is determined by its values on the elements
`s ⊗ m`. -/
theorem algebraBaseChange_hom_ext {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    {f g : (algebraBaseChange R S).obj M ⟶ N}
    (h : ∀ (s : S) (m : (M : Type u)), f.hom (s ⊗ₜ[R] m) = g.hom (s ⊗ₜ[R] m)) : f = g :=
  ModuleCat.hom_ext (LinearMap.ext fun z =>
    TensorProduct.inductionOn z h
      (fun x y ihx ihy =>
        (map_add f.hom x y).trans
          (((congrArg (· + f.hom y) ihx).trans (congrArg (g.hom x + ·) ihy)).trans
            (map_add g.hom x y).symm)))

omit [Algebra R S] in
/-- **Mathlib's extension of scalars along a ring map `f : R → S` is base change for the algebra
structure `f.toAlgebra`.** The two constructions are literally the same: the `R`-module structure
`Module.compHom S f` that `ModuleCat.extendScalars` puts on `S` is the one that `f.toAlgebra`
carries. -/
lemma extendScalars_eq_algebraBaseChange_toAlgebra (f : R →+* S) :
    ModuleCat.extendScalars f = @algebraBaseChange R S _ _ f.toAlgebra :=
  rfl

/-- **Mathlib's extension of scalars along the structure map of an algebra is base change.**
The two constructions use the two `R`-module structures on `S` —
`Module.compHom S (algebraMap R S)` and the one carried by the algebra — which agree, by
`toAlgebra_algebraMap`. -/
lemma extendScalars_eq_algebraBaseChange :
    ModuleCat.extendScalars (algebraMap R S) = algebraBaseChange R S :=
  (extendScalars_eq_algebraBaseChange_toAlgebra R S (algebraMap R S)).trans
    (congrArg (fun i : Algebra R S => @algebraBaseChange R S _ _ i) toAlgebra_algebraMap)

/-- **Mathlib's extension of scalars along the structure map of an algebra is base change**, as
an isomorphism of functors. -/
def extendScalarsNatIso : ModuleCat.extendScalars (algebraMap R S) ≅ algebraBaseChange R S :=
  eqToIso (extendScalars_eq_algebraBaseChange R S)

end ExtendScalars

/-! ### The homology of a category with constant linear coefficients -/

namespace ChaoticSite

section ConstCoefficients

variable {C : Type u} [SmallCategory C] (B : Type u) [Ring B] (U : CosimplicialObject C)

/-- **`H_0(C, M̲) = M`** for the constant diagram on a module `M`. -/
def leftDerivedColimZeroConstIso (hU : IsPointResolution U) (M : ModuleCat.{u} B) :
    ((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived 0).obj
        ((Functor.const Cᵒᵖ).obj M) ≅ M :=
  (ModuleValued.moduleLeftDerivedColimitNatIso U hU 0).app ((Functor.const Cᵒᵖ).obj M) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (ComplexShape.down ℕ) 0).mapIso
      (mooreComplexConstIso U M) ≪≫
    ChainComplex.alternatingConstHomologyZero M

/-- **`H_i(C, M̲) = 0` for `i > 0`** and the constant diagram on a module `M`. -/
theorem isZero_leftDerivedColimSucc_const (hU : IsPointResolution U) (M : ModuleCat.{u} B)
    (i : ℕ) :
    IsZero (((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived (i + 1)).obj
      ((Functor.const Cᵒᵖ).obj M)) := by
  refine IsZero.of_iso ?_
    ((ModuleValued.moduleLeftDerivedColimitNatIso U hU (i + 1)).app
        ((Functor.const Cᵒᵖ).obj M) ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (ComplexShape.down ℕ)
        (i + 1)).mapIso (mooreComplexConstIso U M))
  exact (ChainComplex.alternatingConst_exactAt M (i + 1) (Nat.succ_ne_zero i)).isZero_homology

end ConstCoefficients

end ChaoticSite

end Stacks

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (κ : Cardinal.{u})

/-! ### The augmentation `Ō ⟶ B̲` as a morphism of presheaves of `B`-modules -/

/-- **The augmentation `Ō ⟶ B̲`** of presheaves of `B`-modules on the small model of the
polynomial site, assembled from the pointwise `B`-algebra maps
`CommAlgCat.smallPolynomialQuotientAug`. -/
def smallPolynomialQuotientModuleAug :
    smallPolynomialQuotientModule A B κ ⟶
      (Functor.const (smallBoundedPolynomialSite A B κ)ᵒᵖ).obj
        (ModuleCat.of (B : Type u) (B : Type u)) where
  app X := ModuleCat.ofHom (smallPolynomialQuotientAug A B κ X).toLinearMap
  naturality _ _ f :=
    ModuleCat.hom_ext (LinearMap.ext fun x => smallPolynomialQuotientAug_map A B κ f x)

/-- The augmentation `Ō ⟶ B̲` acts on a section by the `B`-algebra map
`CommAlgCat.smallPolynomialQuotientAug`. -/
@[simp]
lemma smallPolynomialQuotientModuleAug_app_apply
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (x : ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u)) :
    ((smallPolynomialQuotientModuleAug A B κ).app X).hom x =
      smallPolynomialQuotientAug A B κ X x :=
  rfl

/-- **The augmentation is surjective over every object**: the section `b ⊗ 1` of `Ō` is sent to
`b`. No hypothesis on `A → B` is needed. -/
theorem surjective_smallPolynomialQuotientAug (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    Function.Surjective (smallPolynomialQuotientAug A B κ X) := fun b =>
  ⟨b ⊗ₜ[A] 1, by rw [smallPolynomialQuotientAug_tmul, map_one, smul_eq_mul, mul_one]⟩

/-- Membership in the first step of the augmentation filtration is the vanishing of the
augmentation: `𝒦 = ker(Ō → B̲)`, by the definition of `𝒦` and `pow_one`. -/
theorem mem_smallPolynomialAugmentationIdealPowSubmodule_one
    {X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)}
    (x : ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u)) :
    x ∈ smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X ↔
      smallPolynomialQuotientAug A B κ X x = 0 := by
  change x ∈ smallPolynomialAugmentationIdeal A B κ X ^ 1 ↔ _
  rw [pow_one]
  exact mem_smallPolynomialAugmentationIdeal A B κ x

/-- The composite `𝒦 ⟶ Ō ⟶ B̲` vanishes: a section of `𝒦` is by definition killed by the
augmentation. -/
theorem smallPolynomialAugmentationIdealPowι_comp_aug :
    smallPolynomialAugmentationIdealPowι A B κ 1 ≫ smallPolynomialQuotientModuleAug A B κ = 0 := by
  refine NatTrans.ext (funext fun X => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  change smallPolynomialQuotientAug A B κ X x.1 = 0
  exact (mem_smallPolynomialAugmentationIdealPowSubmodule_one A B κ _).1 x.2

/-- **The augmentation sequence `0 → 𝒦 → Ō → B̲ → 0`** of presheaves of `B`-modules on the small
model of the polynomial site, as a short complex. It is short exact by
`CommAlgCat.shortExact_smallPolynomialAugmentationShortComplex`. -/
def smallPolynomialAugmentationShortComplex :
    ShortComplex ((smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ ModuleCat.{u} (B : Type u)) :=
  ShortComplex.mk (smallPolynomialAugmentationIdealPowι A B κ 1)
    (smallPolynomialQuotientModuleAug A B κ)
    (smallPolynomialAugmentationIdealPowι_comp_aug A B κ)

/-- **The augmentation sequence is short exact over every object of the site.** The inclusion of
`𝒦(X)` into `Ō(X)` is injective with image the kernel of the augmentation, which is `𝒦(X)` by
definition, and the augmentation `Ō(X) = B ⊗_A P → B` is surjective because it hits `b ⊗ 1`. -/
theorem shortExact_smallPolynomialAugmentationShortComplex_map_evaluation
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    ((smallPolynomialAugmentationShortComplex A B κ).map
      ((evaluation ((smallBoundedPolynomialSite A B κ)ᵒᵖ)
        (ModuleCat.{u} (B : Type u))).obj X)).ShortExact := by
  refine ModuleCat.shortComplex_shortExact _ (fun y => ?_) (fun x y h => Subtype.ext h)
    (surjective_smallPolynomialQuotientAug A B κ X)
  refine ⟨fun hy => ⟨⟨y, ?_⟩, rfl⟩, ?_⟩
  · exact (mem_smallPolynomialAugmentationIdealPowSubmodule_one A B κ y).2 hy
  · rintro ⟨x, rfl⟩
    exact (mem_smallPolynomialAugmentationIdealPowSubmodule_one A B κ _).1 x.2

/-- **The augmentation sequence `0 → 𝒦 → Ō → B̲ → 0` is short exact** as a sequence of
presheaves of `B`-modules: exactness of a sequence of presheaves of modules is objectwise, and
over each object of the site it is
`CommAlgCat.shortExact_smallPolynomialAugmentationShortComplex_map_evaluation`. -/
theorem shortExact_smallPolynomialAugmentationShortComplex :
    (smallPolynomialAugmentationShortComplex A B κ).ShortExact :=
  ShortComplex.shortExact_of_app _
    (shortExact_smallPolynomialAugmentationShortComplex_map_evaluation A B κ)

/-! ### The homology of `C_{B/A}` with constant coefficients -/

/-- **`H_0(C_{B/A}, B̲) = B`.** Proved for every ring map `A → B`. -/
def leftDerivedColimZeroConstPolynomialSiteIso :
    ((colim :
          ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
            ModuleCat.{u} (B : Type u)) ⥤ ModuleCat.{u} (B : Type u)).leftDerived 0).obj
        ((Functor.const
            ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ)).obj
          (ModuleCat.of (B : Type u) (B : Type u))) ≅
      ModuleCat.of (B : Type u) (B : Type u) :=
  Stacks.ChaoticSite.leftDerivedColimZeroConstIso (B : Type u)
    (standardResolutionSmallCosimplicialObject A B)
    (isPointResolution_standardResolutionSmallCosimplicialObject A B) _

/-- **`H_{i+1}(C_{B/A}, B̲) = 0`.** Proved for every ring map `A → B`. -/
theorem isZero_leftDerivedColimSucc_constPolynomialSite (i : ℕ) :
    IsZero (((colim :
          ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
            ModuleCat.{u} (B : Type u)) ⥤ ModuleCat.{u} (B : Type u)).leftDerived (i + 1)).obj
      ((Functor.const
          ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ)).obj
        (ModuleCat.of (B : Type u) (B : Type u)))) :=
  Stacks.ChaoticSite.isZero_leftDerivedColimSucc_const (B : Type u)
    (standardResolutionSmallCosimplicialObject A B)
    (isPointResolution_standardResolutionSmallCosimplicialObject A B) _ i

/-! ### The inclusion `𝒦 ⊆ Ō` on homology in positive degrees -/

/-- **For every `i ≥ 1` the inclusion `𝒦 ⟶ Ō` is invertible on `H_i(C_{B/A}, -)`.** The long
exact sequence of the augmentation sequence `0 → 𝒦 → Ō → B̲ → 0` has `H_{i+2}(C,B̲) = 0` before
`H_{i+1}(C,𝒦)` and `H_{i+1}(C,B̲) = 0` after `H_{i+1}(C,Ō)`, both by
`CommAlgCat.isZero_leftDerivedColimSucc_constPolynomialSite`. -/
theorem isIso_leftDerivedColimSucc_map_smallPolynomialAugmentationIdealPowι (i : ℕ) :
    IsIso (((colim :
          ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
            ModuleCat.{u} (B : Type u)) ⥤
            ModuleCat.{u} (B : Type u)).leftDerived (i + 1)).map
      (smallPolynomialAugmentationIdealPowι A B (standardResolutionVarCardinal A B) 1)) := by
  have hS := shortExact_smallPolynomialAugmentationShortComplex A B
    (standardResolutionVarCardinal A B)
  have : Mono (((colim :
      ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
        ModuleCat.{u} (B : Type u)) ⥤
        ModuleCat.{u} (B : Type u)).leftDerived (i + 1)).map
    (smallPolynomialAugmentationIdealPowι A B (standardResolutionVarCardinal A B) 1)) :=
    (Functor.leftDerived_exact_δ₂ (colim :
        ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
          ModuleCat.{u} (B : Type u)) ⥤ ModuleCat.{u} (B : Type u)) hS (i + 1)).mono_g
      ((isZero_leftDerivedColimSucc_constPolynomialSite A B (i + 1)).eq_of_src _ _)
  have : Epi (((colim :
      ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
        ModuleCat.{u} (B : Type u)) ⥤
        ModuleCat.{u} (B : Type u)).leftDerived (i + 1)).map
    (smallPolynomialAugmentationIdealPowι A B (standardResolutionVarCardinal A B) 1)) :=
    (Functor.leftDerived_exact (colim :
        ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
          ModuleCat.{u} (B : Type u)) ⥤ ModuleCat.{u} (B : Type u)) hS (i + 1)).epi_f
      ((isZero_leftDerivedColimSucc_constPolynomialSite A B i).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- **`H_{i+1}(C_{B/A}, 𝒦) ≅ H_{i+1}(C_{B/A}, Ō)`**, induced by the inclusion `𝒦 ⊆ Ō`. This is
`CommAlgCat.isIso_leftDerivedColimSucc_map_smallPolynomialAugmentationIdealPowι` read as an
isomorphism. -/
def leftDerivedColimSuccAugmentationIdealIso (i : ℕ) :
    ((colim :
          ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
            ModuleCat.{u} (B : Type u)) ⥤
            ModuleCat.{u} (B : Type u)).leftDerived (i + 1)).obj
        (smallPolynomialAugmentationIdealPow A B (standardResolutionVarCardinal A B) 1) ≅
      ((colim :
          ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
            ModuleCat.{u} (B : Type u)) ⥤
            ModuleCat.{u} (B : Type u)).leftDerived (i + 1)).obj
        (smallPolynomialQuotientModule A B (standardResolutionVarCardinal A B)) :=
  haveI := isIso_leftDerivedColimSucc_map_smallPolynomialAugmentationIdealPowι A B i
  asIso (((colim :
      ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
        ModuleCat.{u} (B : Type u)) ⥤ ModuleCat.{u} (B : Type u)).leftDerived (i + 1)).map
    (smallPolynomialAugmentationIdealPowι A B (standardResolutionVarCardinal A B) 1))

/-- The isomorphism `H_{i+1}(C_{B/A}, 𝒦) ≅ H_{i+1}(C_{B/A}, Ō)` is the map induced by the
inclusion. -/
@[simp]
lemma leftDerivedColimSuccAugmentationIdealIso_hom (i : ℕ) :
    (leftDerivedColimSuccAugmentationIdealIso A B i).hom =
      ((colim :
        ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
          ModuleCat.{u} (B : Type u)) ⥤ ModuleCat.{u} (B : Type u)).leftDerived (i + 1)).map
        (smallPolynomialAugmentationIdealPowι A B (standardResolutionVarCardinal A B) 1) :=
  rfl

/-- **`H_i(C_{B/A}, 𝒦) ≅ H_i(C_{B/A}, Ō)` for every `i > 0`**, induced by the inclusion
`𝒦 ⊆ Ō`. -/
def leftDerivedColimAugmentationIdealIsoOfPos (i : ℕ) (hi : 0 < i) :
    ((colim :
          ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
            ModuleCat.{u} (B : Type u)) ⥤
            ModuleCat.{u} (B : Type u)).leftDerived i).obj
        (smallPolynomialAugmentationIdealPow A B (standardResolutionVarCardinal A B) 1) ≅
      ((colim :
          ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
            ModuleCat.{u} (B : Type u)) ⥤
            ModuleCat.{u} (B : Type u)).leftDerived i).obj
        (smallPolynomialQuotientModule A B (standardResolutionVarCardinal A B)) :=
  match i, hi with
  | 0, h => absurd h (lt_irrefl 0)
  | (j + 1), _ => leftDerivedColimSuccAugmentationIdealIso A B j

/-! ### `𝒪(U_•)` as a projective resolution of `B` over `A` -/

/-- **The augmentation `𝒪(U_•) ⟶ B[0]`** of chain complexes of `A`-modules: the augmentation
`𝒪 ⟶ B̲` on Moore complexes, followed by the identification of the Moore complex of the constant
diagram with the alternating constant complex, followed by the homotopy equivalence of the
latter with `B` placed in degree zero. -/
def smallPolynomialStructureModuleMooreπ :
    smallPolynomialStructureModuleMooreComplex A B ⟶
      (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A (B : Type u)) :=
  (Stacks.ChaoticSite.ModuleValued.moduleCosimplicialMooreComplex
        (standardResolutionSmallCosimplicialObject A B)).map
      (smallPolynomialModuleAugmentation A B (standardResolutionVarCardinal A B)) ≫
    (Stacks.ChaoticSite.mooreComplexConstIso (standardResolutionSmallCosimplicialObject A B)
      (ModuleCat.of A (B : Type u))).hom ≫
    (ChainComplex.alternatingConstHomotopyEquiv (ModuleCat.of A (B : Type u))).hom

/-- **The augmentation `𝒪(U_•) ⟶ B[0]` is a quasi-isomorphism**: the augmentation of Moore
complexes is one by
`CommAlgCat.quasiIso_smallPolynomialStructureModuleMooreComplex_augmentation`, the middle map is
an isomorphism, and the last map is a homotopy equivalence. -/
instance quasiIso_smallPolynomialStructureModuleMooreπ :
    QuasiIso (smallPolynomialStructureModuleMooreπ A B) := by
  have := quasiIso_smallPolynomialStructureModuleMooreComplex_augmentation A B
  change QuasiIso (_ ≫ _ ≫ _)
  infer_instance

/-- **`𝒪(U_•)` is a projective resolution of `B` over `A`.** Its terms are free `A`-modules,
hence projective, and the augmentation to `B` placed in degree zero is a quasi-isomorphism. This
is the resolution that computes `Tor^A_*(B, B)`. -/
def smallPolynomialStructureModuleProjectiveResolution :
    ProjectiveResolution (ModuleCat.of A (B : Type u)) where
  complex := smallPolynomialStructureModuleMooreComplex A B
  projective n := by
    have := module_free_smallPolynomialStructureModuleMooreComplex_X A B n
    exact ModuleCat.projective_of_free
      (Module.Free.chooseBasis A ((smallPolynomialStructureModuleMooreComplex A B).X n : Type u))
  π := smallPolynomialStructureModuleMooreπ A B

/-! ### `Ō` is the base change of `𝒪` along `A → B` -/

/-- The transition maps of `Ō` are the base change of the transition maps of `𝒪`: both send
`b ⊗ p` to `b ⊗ f(p)`. -/
lemma algebraBaseChange_map_smallPolynomialStructureModulePresheaf_map
    {X Y : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)} (f : X ⟶ Y) :
    (Stacks.algebraBaseChange A (B : Type u)).map
        ((smallPolynomialStructureModulePresheaf A B κ).map f) =
      (smallPolynomialQuotientModule A B κ).map f :=
  Stacks.algebraBaseChange_hom_ext A (B : Type u) fun b p => by
    change LinearMap.baseChange (B : Type u)
        ((smallPolynomialStructureModulePresheaf A B κ).map f).hom (b ⊗ₜ[A] p) =
      ((smallPolynomialQuotientModule A B κ).map f).hom (b ⊗ₜ[A] p)
    rw [LinearMap.baseChange_tmul]
    rfl

/-- **`Ō` is the base change of `𝒪` along `A → B`**, in the spelling `Stacks.algebraBaseChange`:
the two presheaves of `B`-modules are equal, both sending an object `(P, α)` of the site to
`B ⊗_A P`. -/
lemma smallPolynomialStructureModulePresheaf_comp_algebraBaseChange :
    smallPolynomialStructureModulePresheaf A B κ ⋙ Stacks.algebraBaseChange A (B : Type u) =
      smallPolynomialQuotientModule A B κ :=
  CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ f =>
    heq_of_eq (algebraBaseChange_map_smallPolynomialStructureModulePresheaf_map A B κ f))

/-- **`Ō = 𝒪 ⊗_A B̲`**: the base change of the structure presheaf `𝒪` along `A → B`, in the
spelling `ModuleCat.extendScalars` that Tor is defined by, is the presheaf `Ō`. -/
lemma smallPolynomialStructureModulePresheaf_comp_extendScalars :
    smallPolynomialStructureModulePresheaf A B κ ⋙
        ModuleCat.extendScalars (algebraMap A (B : Type u)) =
      smallPolynomialQuotientModule A B κ :=
  (congrArg (fun F : ModuleCat.{u} A ⥤ ModuleCat.{u} (B : Type u) =>
        smallPolynomialStructureModulePresheaf A B κ ⋙ F)
      (Stacks.extendScalars_eq_algebraBaseChange A (B : Type u))).trans
    (smallPolynomialStructureModulePresheaf_comp_algebraBaseChange A B κ)

/-- **`Ō = 𝒪 ⊗_A B̲`**, as an isomorphism of presheaves of `B`-modules. -/
def smallPolynomialQuotientModuleExtendScalarsIso :
    smallPolynomialStructureModulePresheaf A B κ ⋙
        ModuleCat.extendScalars (algebraMap A (B : Type u)) ≅
      smallPolynomialQuotientModule A B κ :=
  eqToIso (smallPolynomialStructureModulePresheaf_comp_extendScalars A B κ)

/-- The Moore complex of the evaluation of `Ō` on the standard point resolution. -/
abbrev smallPolynomialQuotientModuleMooreComplex :
    ChainComplex (ModuleCat.{u} (B : Type u)) ℕ :=
  (Stacks.ChaoticSite.ModuleValued.moduleCosimplicialMooreComplex
      (standardResolutionSmallCosimplicialObject A B)).obj
    (smallPolynomialQuotientModule A B (standardResolutionVarCardinal A B))

/-- **`Ō(U_•) = B ⊗_A 𝒪(U_•)`**: the base change of the Moore complex of `𝒪(U_•)` along `A → B`
is the Moore complex of `Ō(U_•)`. Extension of scalars is additive, so it commutes with the
formation of the alternating face map complex, and on the diagrams it is
`CommAlgCat.smallPolynomialQuotientModuleExtendScalarsIso`. -/
def smallPolynomialQuotientModuleMooreBaseChangeIso :
    ((ModuleCat.extendScalars (algebraMap A (B : Type u))).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj (smallPolynomialStructureModuleMooreComplex A B) ≅
      smallPolynomialQuotientModuleMooreComplex A B :=
  (alternatingFaceMapComplexCompMapHomologicalComplexIso
      (ModuleCat.extendScalars (algebraMap A (B : Type u)))).app _ ≪≫
    (alternatingFaceMapComplex (ModuleCat.{u} (B : Type u))).mapIso
      (Functor.isoWhiskerLeft (standardResolutionSmallCosimplicialObject A B).op
        (smallPolynomialQuotientModuleExtendScalarsIso A B
          (standardResolutionVarCardinal A B)))

/-! ### The identification of the abutment -/

/-- **`H_i(C_{B/A}, Ō) ≅ Tor^A_i(B, B)`.** By the module half of [Stacks, Tag 08Q9] the left
hand side is the homology of the Moore complex of `Ō(U_•)`, which is the base change along
`A → B` of the Moore complex of `𝒪(U_•)`; the latter is a resolution of `B` by free
`A`-modules, so its base change computes `Tor^A_*(B, B)`. Proved for every ring map `A → B`. -/
def leftDerivedColimQuotientTorIso (i : ℕ) :
    ((colim :
          ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
            ModuleCat.{u} (B : Type u)) ⥤ ModuleCat.{u} (B : Type u)).leftDerived i).obj
        (smallPolynomialQuotientModule A B (standardResolutionVarCardinal A B)) ≅
      (RingTheory.TorProducts.torBaseChange.{u, u, u} A (B : Type u) i).obj
        (ModuleCat.of A (B : Type u)) :=
  (Stacks.ChaoticSite.ModuleValued.moduleLeftDerivedColimitNatIso
        (standardResolutionSmallCosimplicialObject A B)
        (isPointResolution_standardResolutionSmallCosimplicialObject A B) i).app
      (smallPolynomialQuotientModule A B (standardResolutionVarCardinal A B)) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} (B : Type u))
        (ComplexShape.down ℕ) i).mapIso
      (smallPolynomialQuotientModuleMooreBaseChangeIso A B).symm ≪≫
    ((smallPolynomialStructureModuleProjectiveResolution A B).isoLeftDerivedObj
      (ModuleCat.extendScalars (algebraMap A (B : Type u))) i).symm

/-! ### The first edge map family of Remark 08RG -/

/-- **The first edge map of Stacks Remark 08RG, in degree `i + 1`**: the composite
`Tor^A_{i+1}(B,B) ≅ H_{i+1}(C,Ō) ≅ H_{i+1}(C,𝒦) ⟶ H_{i+1}(C, 𝒦/𝒦²)`, the first two arrows
being `CommAlgCat.leftDerivedColimQuotientTorIso` and
`CommAlgCat.leftDerivedColimSuccAugmentationIdealIso` and the last the map induced by the
projection onto the graded piece. -/
def torToCotangentHomologyEdgeSucc (i : ℕ) :
    (RingTheory.TorProducts.torBaseChange.{u, u, u} A (B : Type u) (i + 1)).obj
        (ModuleCat.of A (B : Type u)) ⟶
      ((colim :
          ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
            ModuleCat.{u} (B : Type u)) ⥤
            ModuleCat.{u} (B : Type u)).leftDerived (i + 1)).obj
        (smallPolynomialAugmentationGraded A B (standardResolutionVarCardinal A B) 1) :=
  (leftDerivedColimQuotientTorIso A B (i + 1)).inv ≫
    (leftDerivedColimSuccAugmentationIdealIso A B i).inv ≫
    ((colim :
      ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
        ModuleCat.{u} (B : Type u)) ⥤ ModuleCat.{u} (B : Type u)).leftDerived (i + 1)).map
      (smallPolynomialAugmentationGradedπ A B (standardResolutionVarCardinal A B) 1)

/-- **The first edge map family of Stacks Remark 08RG**: for every `i > 0` the composite
`Tor^A_i(B,B) ≅ H_i(C_{B/A},Ō) ≅ H_i(C_{B/A},𝒦) ⟶ H_i(C_{B/A}, 𝒦/𝒦²)`. Proved for every ring
map `A → B`; the remark states it for a surjective one. -/
def torToCotangentHomologyEdge (i : ℕ) (hi : 0 < i) :
    (RingTheory.TorProducts.torBaseChange.{u, u, u} A (B : Type u) i).obj
        (ModuleCat.of A (B : Type u)) ⟶
      ((colim :
          ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
            ModuleCat.{u} (B : Type u)) ⥤
            ModuleCat.{u} (B : Type u)).leftDerived i).obj
        (smallPolynomialAugmentationGraded A B (standardResolutionVarCardinal A B) 1) :=
  match i, hi with
  | 0, h => absurd h (lt_irrefl 0)
  | (j + 1), _ => torToCotangentHomologyEdgeSucc A B j

/-- The edge map in degree `i + 1` is `CommAlgCat.torToCotangentHomologyEdgeSucc`. -/
lemma torToCotangentHomologyEdge_succ (i : ℕ) :
    torToCotangentHomologyEdge A B (i + 1) i.succ_pos =
      torToCotangentHomologyEdgeSucc A B i :=
  rfl

/-- The edge map in degree `i + 1`, written out as the composite of the two identifications and
the map induced by the projection `𝒦 ⟶ 𝒦/𝒦²`. -/
lemma torToCotangentHomologyEdgeSucc_eq (i : ℕ) :
    torToCotangentHomologyEdgeSucc A B i =
      (leftDerivedColimQuotientTorIso A B (i + 1)).inv ≫
        (leftDerivedColimSuccAugmentationIdealIso A B i).inv ≫
        ((colim :
          ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
            ModuleCat.{u} (B : Type u)) ⥤ ModuleCat.{u} (B : Type u)).leftDerived (i + 1)).map
          (smallPolynomialAugmentationGradedπ A B (standardResolutionVarCardinal A B) 1) :=
  rfl

/-- The edge map determines, and is determined by, the map induced by the projection onto the
graded piece: composing the identification `H_{i+1}(C,𝒦) ≅ H_{i+1}(C,Ō) ≅ Tor^A_{i+1}(B,B)`
with the edge map gives `H_{i+1}(C, 𝒦) ⟶ H_{i+1}(C, 𝒦/𝒦²)`. -/
lemma leftDerivedColimSuccAugmentationIdealIso_comp_torToCotangentHomologyEdgeSucc (i : ℕ) :
    (leftDerivedColimSuccAugmentationIdealIso A B i).hom ≫
        (leftDerivedColimQuotientTorIso A B (i + 1)).hom ≫
        torToCotangentHomologyEdgeSucc A B i =
      ((colim :
        ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
          ModuleCat.{u} (B : Type u)) ⥤ ModuleCat.{u} (B : Type u)).leftDerived (i + 1)).map
        (smallPolynomialAugmentationGradedπ A B (standardResolutionVarCardinal A B) 1) := by
  rw [torToCotangentHomologyEdgeSucc_eq, Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc]

end CommAlgCat

end
