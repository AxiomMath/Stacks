module

public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.PairsScalingSite
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsBase.PureExtCanonicalArrow

/-!
# Tags 06ZW and 0709 in every degree

For an affine scheme `U = Spec A` and the big site `(Sch/U)_τ` with structure sheaf `𝒪`:

* `Stacks.Adequate.bijective_mapExtAddHom_ι_adequate`, Tag 06ZW: for adequate `𝒪`-modules `𝓕`,
  `𝓖` and every `i ≥ 0`, the natural map `Ext^i_{Adeq(𝒪)}(𝓕, 𝓖) ⟶ Ext^i_{Mod(𝒪)}(𝓕, 𝓖)` is
  bijective. It is the comparison `Stacks.Adequate.bijective_mapExtAddHom_ι_adequate_of_siteZExt`
  applied to the vanishing of `Ext^i(L, M̲)`, `i > 0`, for linearly adequate `L` on the algebras
  of the site, `Stacks.Adequate.subsingleton_zExt_siteModuleFunctors_isLinearlyAdequate`.
* `Stacks.Adequate.pureExtToExt_bijective_and_natural`, Tag 0709: for `A`-modules `M`, `N` and
  every `i`, the canonical arrow `Pext^i_A(M, N) ⟶ Ext^i_{Mod(𝒪)}(M^a, N^a)` of
  `Stacks.Adequate.pureExtToExt` is bijective, and it is natural in `M` and in `N`.

## References

* [Stacks Project, Tag 06ZW](https://stacks.math.columbia.edu/tag/06ZW)
* [Stacks Project, Tag 0709](https://stacks.math.columbia.edu/tag/0709)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

-- As in `PureExtCanonicalArrow`: these instances would replace the abelian structure of the
-- sheaves of modules used by every statement below.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-- Let `U = Spec A` be affine and `𝓕`, `𝓖` adequate `𝒪`-modules. For every `i ≥ 0` the natural map
`Ext^i_{Adeq(𝒪)}(𝓕, 𝓖) ⟶ Ext^i_{Mod(𝒪)}(𝓕, 𝓖)`, induced by the exact inclusion of the adequate
modules, is bijective.

The `letI` preamble is not a list of hypotheses: it is the abelian structure of `Adeq(𝒪)`
(Tag 06VQ (1)), the exactness of its inclusion (Tag 06VQ (2)) and the standard derived-category
and `Ext` choices, spelled exactly as in `bijective_mapExtAddHom_ι_adequate_zero`. -/
@[stacks 06ZW "every degree i ≥ 0"]
public theorem bijective_mapExtAddHom_ι_adequate :
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
    ∀ (F G : (adequate.{u, u} B).FullSubcategory) (n : ℕ),
      Function.Bijective ((adequate.{u, u} B).ι.mapExtAddHom.{u + 1, u + 1} F G n) :=
  bijective_mapExtAddHom_ι_adequate_of_siteZExt B
    (subsingleton_zExt_siteModuleFunctors_isLinearlyAdequate B)

/-- Let `U = Spec A` be affine and `M`, `N` be `A`-modules. For every `i`, the canonical arrow
`Pext^i_A(M, N) ⟶ Ext^i_{Mod(𝒪)}(M^a, N^a)` of `pureExtToExt` is bijective, and it is functorial in
`M` and in `N`: precomposition with `g : M' ⟶ M` on `Pext` corresponds to composition with the
class of `g^a`, and the action of `g : N ⟶ N'`, through any map of the chosen pure injective
resolutions lying over `g`, to composition with the class of `g^a`. -/
@[stacks 0709 "every degree i: the canonical arrow is bijective and natural in M and N"]
public theorem pureExtToExt_bijective_and_natural :
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
    (∀ (M N : ModuleCat.{u} A) (n : ℕ), Function.Bijective (pureExtToExt B M N n)) ∧
    (∀ {M M' : ModuleCat.{u} A} (N : ModuleCat.{u} A) (g : M' ⟶ M) (n : ℕ)
      (x : Module.pureExt (A := A) M N n),
      pureExtToExt B M' N n
          ((HomologicalComplex.homologyMap
            (Module.homComplexPrecomp g.hom (Module.pureExtResolution (A := A) N)) n).hom x) =
        (Ext.mk₀ ((associatedTilde B).map g)).comp (pureExtToExt B M N n x) (zero_add n)) ∧
    (∀ (M : ModuleCat.{u} A) {N N' : ModuleCat.{u} A} (g : N ⟶ N')
      (F : Module.pureExtResolution (A := A) N ⟶ Module.pureExtResolution (A := A) N')
      (_ : (F.f 0).hom.comp (Module.pureExtAugmentation N) =
        (Module.pureExtAugmentation N').comp g.hom)
      (n : ℕ) (x : Module.pureExt (A := A) M N n),
      pureExtToExt B M N' n
          ((HomologicalComplex.homologyMap (Module.homComplexPostcomp M F) n).hom x) =
        (pureExtToExt B M N n x).comp (Ext.mk₀ ((associatedTilde B).map g)) (add_zero n)) :=
  ⟨bijective_pureExtToExt_of_bijective_mapExtAddHom B (bijective_mapExtAddHom_ι_adequate B),
    fun N g n x => pureExtToExt_naturality_left B N g n x,
    fun M {_ _} g F hF n x => pureExtToExt_naturality_right B M g F hF n x⟩

end Stacks.Adequate

end
