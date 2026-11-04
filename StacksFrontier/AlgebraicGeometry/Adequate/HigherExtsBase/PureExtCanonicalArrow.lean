module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AdequateExtComparison
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsBase.AssociatedPureInjective

/-!
# The canonical arrow `Pext^i_A(M, N) ⟶ Ext^i_{Mod(𝒪)}(M^a, N^a)`

Let `U = Spec A` be affine. [Stacks, Tag 0709] asserts that for all `i` there is a canonical
isomorphism `Ext^i_{Mod(𝒪)}(M^a, N^a) = Pext^i_A(M, N)`, functorial in `M` and `N`. The source
constructs the arrow from right to left: for a pure injective resolution `N ⟶ Iᐧ`, the complex
`N^a ⟶ (Iᐧ)^a` is an exact complex of adequate modules, so a cocycle `f : M → Iⁱ` gives a map
`M^a ⟶ N^a[i]` in the derived category of `𝒪`-modules.

This module constructs that arrow, in every degree and with no hypothesis, and proves it natural
in both variables. It factors as

`Pext^i_A(M, N) ≅ Ext^i_{Adeq(𝒪)}(M^a, N^a) ⟶ Ext^i_{Mod(𝒪)}(M^a, N^a)`,

where the first map is the isomorphism `Stacks.Adequate.pureExtAddEquivExtAdequate` — the
resolution `(Iᐧ)^a` is an *injective* resolution of `N^a` in `Adeq(𝒪)`, by
`Stacks.Adequate.injective_associatedAdequate_obj` — and the second is the map on `Ext` of the
exact inclusion `Adeq(𝒪) ⥤ Mod(𝒪)`. On the class of a cocycle `f` it is the class of the
cocycle `f^a` of the resolution `(Iᐧ)^a`, read in `Mod(𝒪)`: exactly the source's arrow.

## Main definitions

* `Stacks.Adequate.pureExtToExt` — the canonical arrow, in every degree.

## Main results

* `Stacks.Adequate.pureExtToExt_naturality_left`, `Stacks.Adequate.pureExtToExt_naturality_right`
  — naturality in `M` and in `N`.
* `Stacks.Adequate.bijective_pureExtToExt_iff` — the canonical arrow is bijective in degree `n`
  exactly when the comparison of Tag 06ZW is bijective at `(M^a, N^a)` in degree `n`.
* `Stacks.Adequate.bijective_pureExtToExt_zero`, `Stacks.Adequate.bijective_pureExtToExt_one` —
  the canonical arrow is bijective in degrees `0` and `1`, where Tag 06ZW is proved.

## References

* [Stacks Project, Tag 0709](https://stacks.math.columbia.edu/tag/0709)
* [Stacks Project, Tag 06ZW](https://stacks.math.columbia.edu/tag/06ZW)
* [Stacks Project, Tag 0708](https://stacks.math.columbia.edu/tag/0708)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

-- The import of Tag 06ZW's module brings these instances into scope; they would replace the
-- abelian structure of the sheaves of modules used by every statement below.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-- **The canonical arrow of [Stacks, Tag 0709]**, `Pext^n_A(M, N) ⟶ Ext^n_{Mod(𝒪)}(M^a, N^a)`,
for every `n`: the class of a cocycle `f : M → Iⁿ` of a pure injective resolution `N ⟶ Iᐧ` goes to
the class of the cocycle `f^a` of the exact complex `N^a ⟶ (Iᐧ)^a`. It is the isomorphism
`Pext^n_A(M, N) ≅ Ext^n_{Adeq(𝒪)}(M^a, N^a)` followed by the map on `Ext` of the inclusion of the
adequate modules.

The `letI` preamble is not a list of hypotheses: it is the abelian structure of `Adeq(𝒪)`
(Tag 06VQ (1)), the exactness of its inclusion (Tag 06VQ (2)) and the standard derived-category
and `Ext` choices, spelled out exactly as in the registrations of Tag 06ZW so that the two share
one spelling of each object. -/
public def pureExtToExt (M N : ModuleCat.{u} A) (n : ℕ) :
    letI : HasDerivedCategory.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      HasDerivedCategory.standard _
    letI : HasExt.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      hasExt_of_hasDerivedCategory _
    Module.pureExt (A := A) M N n →+
      Ext ((associatedTilde B).obj M) ((associatedTilde B).obj N) n :=
  letI := adequate_isClosedUnderKernels.{u, u} B
  letI := adequate_isClosedUnderCokernels.{u, u} B
  letI := adequate_isClosedUnderFiniteProducts.{u, u} B
  letI : Abelian (adequate.{u, u} B).FullSubcategory := abelian_adequate B
  letI : PreservesFiniteLimits (adequate.{u, u} B).ι := (exact_ι_adequate B).1
  letI : PreservesFiniteColimits (adequate.{u, u} B).ι := (exact_ι_adequate B).2
  letI : HasDerivedCategory.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
    HasDerivedCategory.standard _
  letI : HasDerivedCategory.{u + 1} (adequate.{u, u} B).FullSubcategory :=
    HasDerivedCategory.standard _
  letI : HasExt.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
    hasExt_of_hasDerivedCategory _
  letI : HasExt.{u + 1} (adequate.{u, u} B).FullSubcategory :=
    hasExt_of_hasDerivedCategory _
  ((adequate.{u, u} B).ι.mapExtAddHom.{u + 1, u + 1} ((associatedAdequate B).obj M)
      ((associatedAdequate B).obj N) n).comp
    (pureExtAddEquivExtAdequate B M N n).toAddMonoidHom

-- The `letI` preamble of the statements below, as private instances, so that the proofs need not
-- repeat it.
private instance : (associatedAdequate B).Additive := additive_associatedAdequate B
private instance : ObjectProperty.IsClosedUnderKernels (adequate.{u, u} B) :=
  adequate_isClosedUnderKernels.{u, u} B
private instance : ObjectProperty.IsClosedUnderCokernels (adequate.{u, u} B) :=
  adequate_isClosedUnderCokernels.{u, u} B
private instance : ObjectProperty.IsClosedUnderFiniteProducts (adequate.{u, u} B) :=
  adequate_isClosedUnderFiniteProducts.{u, u} B
private instance : Abelian (adequate.{u, u} B).FullSubcategory := abelian_adequate B
private instance : PreservesFiniteLimits (adequate.{u, u} B).ι := (exact_ι_adequate B).1
private instance : PreservesFiniteColimits (adequate.{u, u} B).ι := (exact_ι_adequate B).2
private instance : HasDerivedCategory.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
  HasDerivedCategory.standard _
private instance : HasDerivedCategory.{u + 1} (adequate.{u, u} B).FullSubcategory :=
  HasDerivedCategory.standard _
private instance : HasExt.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
  hasExt_of_hasDerivedCategory _
private instance : HasExt.{u + 1} (adequate.{u, u} B).FullSubcategory :=
  hasExt_of_hasDerivedCategory _

/-- **The canonical arrow on the class of a cocycle.** For a cocycle `f : M → Iⁿ` of the chosen
pure injective resolution `N ⟶ Iᐧ`, the canonical arrow sends its class to the image in
`Ext^n_{Mod(𝒪)}` of the class of the cocycle `f^a` of the injective resolution `(Iᐧ)^a` of `N^a`
in `Adeq(𝒪)`. -/
public lemma pureExtToExt_cocycleClass (M N : ModuleCat.{u} A) (n : ℕ)
    (f : LinearMap.ker ((Module.homComplex M (Module.pureExtResolution (A := A) N)).d n
      (n + 1)).hom) :
    letI : (associatedAdequate B).Additive := additive_associatedAdequate B
    letI := adequate_isClosedUnderKernels.{u, u} B
    letI := adequate_isClosedUnderCokernels.{u, u} B
    letI := adequate_isClosedUnderFiniteProducts.{u, u} B
    letI : Abelian (adequate.{u, u} B).FullSubcategory := abelian_adequate B
    letI : PreservesFiniteLimits (adequate.{u, u} B).ι := (exact_ι_adequate B).1
    letI : PreservesFiniteColimits (adequate.{u, u} B).ι := (exact_ι_adequate B).2
    letI : HasDerivedCategory.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory.{u + 1} (adequate.{u, u} B).FullSubcategory :=
      HasDerivedCategory.standard _
    letI : HasExt.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      hasExt_of_hasDerivedCategory _
    letI : HasExt.{u + 1} (adequate.{u, u} B).FullSubcategory :=
      hasExt_of_hasDerivedCategory _
    pureExtToExt B M N n
        ((Module.cocycleClass M (Module.pureExtResolution (A := A) N) n).hom f) =
      (adequate.{u, u} B).ι.mapExtAddHom.{u + 1, u + 1} ((associatedAdequate B).obj M)
        ((associatedAdequate B).obj N) n
        (Module.cyclesToExt (associatedAdequate B) (injective_associatedAdequate_obj B)
          (fun φ hφ => mono_associatedAdequate_map B φ hφ)
          (fun f g w hfg hQ => exact_associatedAdequate_map B f g w hfg hQ)
          (Module.isPureInjectiveResolution_pureExtResolution N) n f) :=
  have := additive_associatedAdequate B
  congrArg ((adequate.{u, u} B).ι.mapExtAddHom.{u + 1, u + 1} ((associatedAdequate B).obj M)
    ((associatedAdequate B).obj N) n)
    (Module.pureExtAddEquivExt_cocycleClass _ _ _ _ (fullyFaithfulAssociatedAdequate B) M N n f)

/-- **The canonical arrow is natural in `M`.** The action of `g : M' ⟶ M` on `Pext^n_A(-, N)`,
precomposition on `Hom_A(-, Iᐧ)`, corresponds to composition with the degree-zero class of
`g^a`. -/
public lemma pureExtToExt_naturality_left {M M' : ModuleCat.{u} A} (N : ModuleCat.{u} A)
    (g : M' ⟶ M) (n : ℕ) (x : Module.pureExt (A := A) M N n) :
    letI := adequate_isClosedUnderKernels.{u, u} B
    letI := adequate_isClosedUnderCokernels.{u, u} B
    letI := adequate_isClosedUnderFiniteProducts.{u, u} B
    letI : Abelian (adequate.{u, u} B).FullSubcategory := abelian_adequate B
    letI : PreservesFiniteLimits (adequate.{u, u} B).ι := (exact_ι_adequate B).1
    letI : PreservesFiniteColimits (adequate.{u, u} B).ι := (exact_ι_adequate B).2
    letI : HasDerivedCategory.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory.{u + 1} (adequate.{u, u} B).FullSubcategory :=
      HasDerivedCategory.standard _
    letI : HasExt.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      hasExt_of_hasDerivedCategory _
    letI : HasExt.{u + 1} (adequate.{u, u} B).FullSubcategory :=
      hasExt_of_hasDerivedCategory _
    pureExtToExt B M' N n
        ((HomologicalComplex.homologyMap
          (Module.homComplexPrecomp g.hom (Module.pureExtResolution (A := A) N)) n).hom x) =
      (Ext.mk₀ ((associatedTilde B).map g)).comp (pureExtToExt B M N n x) (zero_add n) := by
  have := additive_associatedAdequate B
  show (adequate.{u, u} B).ι.mapExtAddHom _ _ n (Module.pureExtAddEquivExt _ _ _ _
      (fullyFaithfulAssociatedAdequate B) M' N n _) = _
  rw [Module.pureExtAddEquivExt_naturality_left, Functor.mapExtAddHom_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, ι_map_associatedAdequate]
  rfl

/-- **The canonical arrow is natural in `N`.** The action of `g : N ⟶ N'` on `Pext^n_A(M, -)` is
postcomposition with a map `F` of the chosen pure injective resolutions lying over `g` (one exists,
`Module.exists_pureExtResolution_hom`, and any two are homotopic by [Stacks, Tag 0704]); for every
such `F` it corresponds to composition with the degree-zero class of `g^a`. -/
public lemma pureExtToExt_naturality_right (M : ModuleCat.{u} A) {N N' : ModuleCat.{u} A}
    (g : N ⟶ N')
    (F : Module.pureExtResolution (A := A) N ⟶ Module.pureExtResolution (A := A) N')
    (hF : (F.f 0).hom.comp (Module.pureExtAugmentation N) =
      (Module.pureExtAugmentation N').comp g.hom)
    (n : ℕ) (x : Module.pureExt (A := A) M N n) :
    letI := adequate_isClosedUnderKernels.{u, u} B
    letI := adequate_isClosedUnderCokernels.{u, u} B
    letI := adequate_isClosedUnderFiniteProducts.{u, u} B
    letI : Abelian (adequate.{u, u} B).FullSubcategory := abelian_adequate B
    letI : PreservesFiniteLimits (adequate.{u, u} B).ι := (exact_ι_adequate B).1
    letI : PreservesFiniteColimits (adequate.{u, u} B).ι := (exact_ι_adequate B).2
    letI : HasDerivedCategory.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory.{u + 1} (adequate.{u, u} B).FullSubcategory :=
      HasDerivedCategory.standard _
    letI : HasExt.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      hasExt_of_hasDerivedCategory _
    letI : HasExt.{u + 1} (adequate.{u, u} B).FullSubcategory :=
      hasExt_of_hasDerivedCategory _
    pureExtToExt B M N' n
        ((HomologicalComplex.homologyMap (Module.homComplexPostcomp M F) n).hom x) =
      (pureExtToExt B M N n x).comp (Ext.mk₀ ((associatedTilde B).map g)) (add_zero n) := by
  have := additive_associatedAdequate B
  show (adequate.{u, u} B).ι.mapExtAddHom _ _ n (Module.pureExtAddEquivExt _ _ _ _
      (fullyFaithfulAssociatedAdequate B) M N' n _) = _
  rw [Module.pureExtAddEquivExt_naturality_right _ _ _ _ _ M g F hF, Functor.mapExtAddHom_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, ι_map_associatedAdequate]
  rfl

/-- **The canonical arrow is bijective in degree `n` exactly when Tag 06ZW holds at
`(M^a, N^a)` in degree `n`**: it is an isomorphism followed by the comparison of Tag 06ZW. -/
public lemma bijective_pureExtToExt_iff (M N : ModuleCat.{u} A) (n : ℕ) :
    letI := adequate_isClosedUnderKernels.{u, u} B
    letI := adequate_isClosedUnderCokernels.{u, u} B
    letI := adequate_isClosedUnderFiniteProducts.{u, u} B
    letI : Abelian (adequate.{u, u} B).FullSubcategory := abelian_adequate B
    letI : PreservesFiniteLimits (adequate.{u, u} B).ι := (exact_ι_adequate B).1
    letI : PreservesFiniteColimits (adequate.{u, u} B).ι := (exact_ι_adequate B).2
    letI : HasDerivedCategory.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory.{u + 1} (adequate.{u, u} B).FullSubcategory :=
      HasDerivedCategory.standard _
    letI : HasExt.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      hasExt_of_hasDerivedCategory _
    letI : HasExt.{u + 1} (adequate.{u, u} B).FullSubcategory :=
      hasExt_of_hasDerivedCategory _
    Function.Bijective (pureExtToExt B M N n) ↔
      Function.Bijective ((adequate.{u, u} B).ι.mapExtAddHom.{u + 1, u + 1}
        ((associatedAdequate B).obj M) ((associatedAdequate B).obj N) n) := by
  show Function.Bijective (⇑((adequate.{u, u} B).ι.mapExtAddHom.{u + 1, u + 1}
      ((associatedAdequate B).obj M) ((associatedAdequate B).obj N) n) ∘
    ⇑(pureExtAddEquivExtAdequate B M N n)) ↔ _
  exact Function.Bijective.of_comp_iff _ (pureExtAddEquivExtAdequate B M N n).bijective

/-- **The canonical arrow is bijective in degree `0`**, where Tag 06ZW is the full faithfulness of
the inclusion of the adequate modules. -/
public theorem bijective_pureExtToExt_zero (M N : ModuleCat.{u} A) :
    letI : HasDerivedCategory.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      HasDerivedCategory.standard _
    letI : HasExt.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      hasExt_of_hasDerivedCategory _
    Function.Bijective (pureExtToExt B M N 0) :=
  (bijective_pureExtToExt_iff B M N 0).2
    (bijective_mapExtAddHom_ι_adequate_zero B ((associatedAdequate B).obj M)
      ((associatedAdequate B).obj N))

/-- **[Stacks, Tag 0709] in degree `1`.** For `U = Spec A` affine and `A`-modules `M`, `N`, the
canonical arrow `Pext¹_A(M, N) ⟶ Ext¹_{Mod((Sch/U)_τ, 𝒪)}(M^a, N^a)` is bijective, with no
hypothesis. It is the isomorphism `Pext¹_A(M, N) ≅ Ext¹_{Adeq(𝒪)}(M^a, N^a)` of
`Stacks.Adequate.pureExtAddEquivExtAdequate` followed by the comparison of Tag 06ZW, which is
bijective in degree `1` because the adequate modules are closed under extensions
(`Stacks.Adequate.bijective_mapExtAddHom_ι_adequate_one`). The arrow is natural in `M` and `N`
by `Stacks.Adequate.pureExtToExt_naturality_left` and `_naturality_right`. -/
@[stacks 0709 "degree 1: the canonical arrow pureExtToExt, natural in M and N by \
pureExtToExt_naturality_left/_right, is bijective in degree 1; every degree is \
pureExtToExt_bijective_and_natural in HigherExtsAdequate/AdequateExtComparisonAll"]
public theorem bijective_pureExtToExt_one (M N : ModuleCat.{u} A) :
    letI : HasDerivedCategory.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      HasDerivedCategory.standard _
    letI : HasExt.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      hasExt_of_hasDerivedCategory _
    Function.Bijective (pureExtToExt B M N 1) :=
  (bijective_pureExtToExt_iff B M N 1).2
    (bijective_mapExtAddHom_ι_adequate_one B ((associatedAdequate B).obj M)
      ((associatedAdequate B).obj N))

/-- **The canonical arrow is bijective in every degree as soon as the comparison of Tag 06ZW is**:
the assembly of [Stacks, Tag 0709] in every degree, stated against the form of Tag 06ZW for all
adequate modules and all degrees. Applied to Tag 06ZW in every degree it gives Tag 0709 in every
degree, `Stacks.Adequate.pureExtToExt_bijective_and_natural`. -/
public theorem bijective_pureExtToExt_of_bijective_mapExtAddHom :
    letI := adequate_isClosedUnderKernels.{u, u} B
    letI := adequate_isClosedUnderCokernels.{u, u} B
    letI := adequate_isClosedUnderFiniteProducts.{u, u} B
    letI : Abelian (adequate.{u, u} B).FullSubcategory := abelian_adequate B
    letI : PreservesFiniteLimits (adequate.{u, u} B).ι := (exact_ι_adequate B).1
    letI : PreservesFiniteColimits (adequate.{u, u} B).ι := (exact_ι_adequate B).2
    letI : HasDerivedCategory.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory.{u + 1} (adequate.{u, u} B).FullSubcategory :=
      HasDerivedCategory.standard _
    letI : HasExt.{u + 1} (SheafOfModules.{u} B.structureSheaf) :=
      hasExt_of_hasDerivedCategory _
    letI : HasExt.{u + 1} (adequate.{u, u} B).FullSubcategory :=
      hasExt_of_hasDerivedCategory _
    (∀ (F G : (adequate.{u, u} B).FullSubcategory) (n : ℕ),
        Function.Bijective ((adequate.{u, u} B).ι.mapExtAddHom.{u + 1, u + 1} F G n)) →
      ∀ (M N : ModuleCat.{u} A) (n : ℕ), Function.Bijective (pureExtToExt B M N n) :=
  fun h M N n => (bijective_pureExtToExt_iff B M N n).2 (h _ _ n)

end Stacks.Adequate

end
