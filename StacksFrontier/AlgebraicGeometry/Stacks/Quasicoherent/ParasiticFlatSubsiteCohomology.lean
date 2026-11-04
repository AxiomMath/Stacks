module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticModules
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteCohomologyAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteLocalFactorizations
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.ULiftUnitAbelianComparison

/-!
# Cohomology of a parasitic module vanishes, for the étale and the fppf topology

Let `𝒳` be an algebraic stack, let `τ` be the étale or the fppf topology, and let `ℱ` be a
parasitic `𝒪_𝒳`-module on `𝒳_τ` (**Stacks 0773**): its sections vanish at every object of `𝒳`
lying over a scheme flat over `𝒳`. Part (1) of **Stacks 0775** asserts

`H^i_τ(𝒳, ℱ) = 0` for all `i`.

This file proves it with no hypothesis beyond the source's, at the module universe `u + 1` that
contains the objects of the site.

## The proof

The flat objects of `𝒳` form a full subcategory `𝒳'` satisfying the two conditions of
**Stacks 07AK**: it is closed under the morphisms lying over smooth, respectively flat and locally
finitely presented, morphisms of schemes (`AlgebraicGeometry.Stack.flatObject_of_flat`), and it
contains the distinguished object of a smooth surjective presentation `(Sch/U) ⟶ 𝒳`, which is a
smooth hence flat object. So restriction to `𝒳'` does not change the cohomology of abelian sheaves
on `𝒳_τ` (`AlgebraicGeometry.Stack.subsiteCohomologyIsoOfSmoothSurjective`, the cohomology
comparison of **Stacks 07AK**). This comparison is **Stacks 0GR0** part (2)(a) for the fppf
topology, with `𝒳'` the flat-fppf site of **Stacks 0787**, and its analogue for the étale
topology.

The restriction of a parasitic sheaf to `𝒳'` is the zero sheaf, so its cohomology on `𝒳'`
vanishes, hence so does its cohomology on `𝒳_τ`
(`AlgebraicGeometry.Stack.isZero_functorH_of_subsingleton_flatObject`). Finally the cohomology of
a sheaf of `𝒪_𝒳`-modules is the cohomology of its underlying abelian sheaf, by **Stacks 03FD**
(`Stacks.Cohomology.ULiftUnitComparison.extULiftUnitIso`).

This replaces the source's double use of the Čech-to-cohomology spectral sequence of a smooth
presentation (**Stacks 06XJ**) and its reduction to a scheme (**Stacks 0755**): those spectral
sequences are what the proof of Stacks 07AK runs on, by dévissage.

## Main results

* `AlgebraicGeometry.Stack.subsiteCohomologyIsoOfSmoothSurjective`: the cohomology comparison of
  **Stacks 07AK**, from a given smooth surjective presentation whose distinguished object lies in
  the subcategory.
* `AlgebraicGeometry.Stack.isClosedUnderSitePullback_flatObject`: the flat objects satisfy
  condition (1) of Stacks 07AK, for the étale and for the fppf topology.
* `AlgebraicGeometry.Stack.flatSubsiteCohomologyIso`: restriction to the flat objects does not
  change cohomology, for the étale and for the fppf topology (**Stacks 0GR0** (2)(a) for the
  latter).
* `AlgebraicGeometry.Stack.isZero_functorH_of_subsingleton_flatObject`: an abelian sheaf vanishing
  at the flat objects has vanishing cohomology.
* `AlgebraicGeometry.Stack.isZero_ext_uliftUnit_of_isParasitic`: **Stacks 0775** part (1).

## Implementation notes

The structure sheaf `𝒪_𝒳` of **Stacks 06TV** has its rings of sections in `Type u`, whereas the
modules here have sections in `Type (u + 1)`, the universe of the objects of the site, where
sheaves of modules form a Grothendieck abelian category and the comparison of **Stacks 03FD**
holds. At that universe `𝒪_𝒳` enters as a module through its universe lift
`Stacks.SheafOfModules.uliftUnit`, which is still free of rank one, so that `Ext^i` out of it is
the cohomology `H^i_τ(𝒳, -)` of the source: in degree zero it is the global sections
(`Stacks.Cohomology.ULiftUnitComparison.uliftUnitHomAddEquiv`).

## References

* [Stacks Project, Tag 0775](https://stacks.math.columbia.edu/tag/0775)
* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
* [Stacks Project, Tag 0GR0](https://stacks.math.columbia.edu/tag/0GR0)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open Stacks.Sites.CoverDescent

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Stack

universe u w t

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {τ : SiteKind} {P : ObjectProperty 𝒳.val.val.obj}

/-! ### The cohomology comparison of Stacks 07AK from a given presentation -/

/-- **Stacks 07AK, the cohomology comparison, from a given smooth surjective presentation.** Let
`𝒳' ⊆ 𝒳` satisfy condition (1) of Stacks 07AK for `τ` the étale or the fppf topology, and let
`a : (Sch/U₀) ⟶ 𝒳` be smooth and surjective with its distinguished object in `𝒳'`. Then for every
degree `q`, `H^q(𝒳'_τ, g⁻¹ℱ) ≅ H^q(𝒳_τ, ℱ)` naturally in the abelian sheaf `ℱ` on `𝒳_τ`.

This is `AlgebraicGeometry.Stack.subsiteCohomologyIsoOfAtlas` with condition (2) of Stacks 07AK
supplied as a presentation rather than as an object of `𝒳'`: the proof is the same descent along
the class `AlgebraicGeometry.Stack.SmoothOverAtlas` of the presentation. -/
def subsiteCohomologyIsoOfSmoothSurjective
    (hcl : IsClosedUnderSitePullback B S hS 𝒳.val.val.p P τ) {U₀ : BigFppfOver B S hS}
    (a : schemeStack.{u, w} B S hS U₀ ⟶ 𝒳) (hasm : AlgebraicStacks.IsSmooth B S hS a)
    (hasurj : IsSurjective B S hS a)
    (hx : P ((CatFiberedInGroupoids.homFunctor a.hom).obj (Over.mk (𝟙 U₀)))) (q : ℕ) :
    haveI := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
      𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids hcl
    subsiteRestriction B S hS 𝒳.val.val.p (B.baseTopology τ) P ⋙
        Sheaf.functorH.{u + 1, u + 1, u, u + 1}
          (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) P) q ≅
      Sheaf.functorH.{u + 1, u + 1, u, u + 1}
        (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ)) q :=
  haveI := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids hcl
  haveI := isCocontinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids hcl
  haveI := isRightAdjoint_subsiteRestriction_of_isClosedUnderSitePullback hcl
  haveI := preservesCoveringPullbacks_of_isClosedUnderSitePullback hcl
  have h𝔎 := isClosedUnderRepresentableCovers_smoothOverAtlas a τ P hcl hasm hasurj hx
  let F₀ := componentPresheaf (𝟭 𝒳.val.val.obj)
  have hF₀ : SmoothOverAtlas 𝒳 a F₀ := Or.inl rfl
  haveI := isIso_freeComparison.{u + 1, u, u + 1, u + 1}
    (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ))
    (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) P) P.ι F₀
    (fun F hF => restrictHom_bijective_of_mem.{u + 1, u, u + 1, u + 1} _ h𝔎 hF₀ F hF)
  let e₁ := freeAbelianSheafIsoConstantSheafOfUnique
    (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) P) (P.ι.op ⋙ F₀)
    (fun y => componentPresheafIdUnique (op (P.ι.obj y.unop)))
  let e₂ := freeAbelianSheafIsoConstantSheafOfUnique
    (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ)) F₀ componentPresheafIdUnique
  subsiteCohomologyIso B S hS 𝒳.val.val.p (B.baseTopology τ) P
    ((P.ι.sheafPullback AddCommGrpCat.{u + 1} _ _).mapIso e₁.symm ≪≫
      asIso (freeComparison.{u + 1, u, u + 1, u + 1}
        (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ))
        (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) P) P.ι F₀) ≪≫ e₂)
    (fun I _ n b => Stacks.Cohomology.ColimitsOfCohomology.ext_eq_zero_of_iso_first e₁.symm
      (n + 1) (fun c => ext_restriction_eq_zero_of_mem.{u + 1, u + 1, u, u + 1} h𝔎
        (fun I _ d m c => subsiteObjectCohomology_eq_zero B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids (B.baseTopology τ) P I d m c) hF₀ I n c) b) q

/-! ### The flat objects -/

variable (𝒳) in
/-- **The flat objects satisfy condition (1) of Stacks 07AK**, for the étale and for the fppf
topology: an object mapping to a flat object over a smooth, respectively flat, morphism of schemes
is flat (`AlgebraicGeometry.Stack.flatObject_of_flat`), a smooth morphism being flat. -/
theorem isClosedUnderSitePullback_flatObject (hτ : τ = .etale ∨ τ = .fppf) :
    IsClosedUnderSitePullback B S hS 𝒳.val.val.p (flatObject B S hS 𝒳.val) τ := by
  rcases hτ with rfl | rfl
  · exact Or.inl ⟨rfl, fun f _ hy => flatObject_of_flat B S hS 𝒳 f inferInstance hy⟩
  · exact Or.inr ⟨rfl, fun f hf _ hy => flatObject_of_flat B S hS 𝒳 f hf hy⟩

variable (𝒳) in
/-- **Restriction to the flat objects does not change cohomology**, for `τ` the étale or the
fppf topology: `H^q(𝒳'_τ, g⁻¹ℱ) ≅ H^q(𝒳_τ, ℱ)` naturally in the abelian sheaf `ℱ` on `𝒳_τ`, where
`𝒳' ⊆ 𝒳` is the full subcategory of flat objects with the induced topology and `g⁻¹` is
restriction.

For the fppf topology `𝒳'_τ` is the flat-fppf site of **Stacks 0787** and this is **Stacks 0GR0**
part (2)(a) for abelian sheaves. It is the cohomology comparison of Stacks 07AK
(`AlgebraicGeometry.Stack.subsiteCohomologyIsoOfSmoothSurjective`) for the flat objects, whose
condition (1) is `AlgebraicGeometry.Stack.isClosedUnderSitePullback_flatObject` and whose condition
(2) is met by any smooth surjective presentation `(Sch/U) ⟶ 𝒳`: its distinguished object is a
smooth, hence flat, object. -/
def flatSubsiteCohomologyIso (hτ : τ = .etale ∨ τ = .fppf) (q : ℕ) :
    haveI := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
      𝒳.val.val.p (flatObject B S hS 𝒳.val) τ 𝒳.val.isFiberedInGroupoids
      (isClosedUnderSitePullback_flatObject 𝒳 hτ)
    subsiteRestriction B S hS 𝒳.val.val.p (B.baseTopology τ) (flatObject B S hS 𝒳.val) ⋙
        Sheaf.functorH.{u + 1, u + 1, u, u + 1}
          (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ)
            (flatObject B S hS 𝒳.val)) q ≅
      Sheaf.functorH.{u + 1, u + 1, u, u + 1}
        (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ)) q :=
  subsiteCohomologyIsoOfSmoothSurjective (isClosedUnderSitePullback_flatObject 𝒳 hτ)
    (exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳).choose_spec.choose
    (exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳).choose_spec.choose_spec.1
    (exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳).choose_spec.choose_spec.2
    (flatObject_of_smoothObject.{u, w} B S hS 𝒳 (smoothObject_atlas_obj.{u, w} B S hS _
      (exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳).choose_spec.choose_spec.1)) q

/-- **An abelian sheaf vanishing at the flat objects has vanishing cohomology**, for `τ` the étale
or the fppf topology. Its restriction to the flat objects is the zero sheaf, whose cohomology
vanishes, and restriction does not change cohomology
(`AlgebraicGeometry.Stack.flatSubsiteCohomologyIso`). -/
theorem isZero_functorH_of_subsingleton_flatObject (hτ : τ = .etale ∨ τ = .fppf)
    (A : Sheaf (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ)) AddCommGrpCat.{u + 1})
    (hA : ∀ x : 𝒳.val.val.obj, flatObject B S hS 𝒳.val x → Subsingleton (A.obj.obj (op x)))
    (q : ℕ) :
    IsZero ((Sheaf.functorH.{u + 1, u + 1, u, u + 1}
      (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ)) q).obj A) := by
  have := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p (flatObject B S hS 𝒳.val) τ 𝒳.val.isFiberedInGroupoids
    (isClosedUnderSitePullback_flatObject 𝒳 hτ)
  refine ((flatSubsiteCohomologyIso 𝒳 hτ q).app A).isZero_iff.1
    (Functor.map_isZero (Sheaf.functorH.{u + 1, u + 1, u, u + 1}
      (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) (flatObject B S hS 𝒳.val)) q) ?_)
  have hz : IsZero ((subsiteRestriction B S hS 𝒳.val.val.p (B.baseTopology τ)
      (flatObject B S hS 𝒳.val)).obj A).obj :=
    Functor.isZero _ fun x => @AddCommGrpCat.isZero_of_subsingleton _ (hA _ x.unop.property)
  exact (IsZero.iff_id_eq_zero _).2 (Sheaf.hom_ext (hz.eq_of_src _ _))

/-! ### Stacks 0775, part (1) -/

/-- **Stacks 0775** part (1). Let `𝒳` be an algebraic stack, let `τ` be the étale or the fppf
topology, and let `ℱ` be a parasitic sheaf of `𝒪_𝒳`-modules on `𝒳_τ` (**Stacks 0773**). Then
`H^i_τ(𝒳, ℱ) = 0` for all `i`.

The modules have their sections in the universe `u + 1` of the objects of the site, where the
structure sheaf `𝒪_𝒳` is a module through its universe lift `Stacks.SheafOfModules.uliftUnit`
and `H^i_τ(𝒳, -) = Ext^i(𝒪_𝒳, -)`, in any universe `t` of `Ext`-groups. By **Stacks 03FD** this
is the cohomology of the underlying abelian sheaf
(`Stacks.Cohomology.ULiftUnitComparison.extULiftUnitIso`), which vanishes because that sheaf
vanishes at the flat objects (`AlgebraicGeometry.Stack.isZero_functorH_of_subsingleton_flatObject`,
from the cohomology comparison of **Stacks 07AK** along the inclusion of the flat objects). -/
@[stacks 0775 "part (1), for τ the étale or the fppf topology, with no hypothesis: \
H^i_τ(𝒳, ℱ) = 0 for a parasitic ℱ, at the module universe u + 1 of the objects of the site"]
theorem isZero_ext_uliftUnit_of_isParasitic (hτ : τ = .etale ∨ τ = .fppf)
    [HasExt.{t} (SheafOfModules.{u + 1}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ))]
    (F : SheafOfModules.{u + 1}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ))
    (hF : IsParasitic B S hS 𝒳 τ F.val) (i : ℕ) :
    IsZero ((extFunctorObj.{t} (Stacks.SheafOfModules.uliftUnit.{u + 1}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ))
        i).obj F) :=
  Stacks.Cohomology.ULiftUnitComparison.isZero_ext_uliftUnit_of_isZero_functorH.{u, u, u + 1}
    (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ) F i
    (isZero_functorH_of_subsingleton_flatObject hτ
      ((SheafOfModules.toSheaf _).obj F) (fun x hx => hF x hx) i)

end AlgebraicGeometry.Stack

end
