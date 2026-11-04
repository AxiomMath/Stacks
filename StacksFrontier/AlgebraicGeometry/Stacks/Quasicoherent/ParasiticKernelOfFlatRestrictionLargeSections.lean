module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EvaluationConservative
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Stacks.ParasiticPullbackVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedPushforwardQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentModuleUniverse
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangePropertySheafified
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteDerivedModuleBaseChange
public import StacksFrontier.Homology.DerivedCategory.IsZero

/-!
# The kernel of restriction to the flat-fppf site, at module universe `u + 1`

Let `𝒳` be an algebraic stack and let `g^* = g^{-1}` be restriction of sheaves of modules from the
fppf site of `𝒳` to its flat-fppf site (**Stacks 0788** (2)), at module universe `u + 1`, the
universe where the derived direct image of **Stacks 07BC** lives
(`AlgebraicGeometry.Stack.FlatFppf.moduleInverseImage`). A module is parasitic
(**Stacks 0773**) exactly when `g^*` kills it — its sections over every flat object vanish, and
those are the sections of `g^*` of it — and so a complex is killed by the exact functor `g^*` on
derived categories exactly when all its cohomology modules are parasitic. This is
**Stacks 07B9** (2)(b) at that universe, for any class `L` of modules such as the faithful
`LQCoh^fbc` of **Stacks 0762**.

## Main results

* `isParasitic_iff_isZero_moduleInverseImage`: a module is parasitic exactly when `g^*` of it
  vanishes.
* `isZero_moduleInverseImage_mapDerivedCategory_iff_forall_isParasitic`: `g^*K = 0` exactly when
  every cohomology module of `K` is parasitic.
* `isZero_moduleInverseImage_mapDerivedCategory_iff_of_class`: for `K` in `D_L(𝒪_𝒳)`, `g^*K = 0`
  exactly when `K` lies in `D_{Parasitic ∩ L}(𝒪_𝒳)`.

## References

* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 07B9](https://stacks.math.columbia.edu/tag/07B9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack.FlatFppf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **A module is parasitic exactly when its restriction to the flat-fppf site vanishes**, at
module universe `u + 1`: the sections of the restriction over a flat object are the sections of
the module there. -/
theorem isParasitic_iff_isZero_moduleInverseImage
    (F : SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) :
    IsParasitic.{u, w, u + 1} B S hS 𝒳 .fppf F.val ↔
      IsZero ((moduleInverseImage B S hS 𝒳).obj F) := by
  refine Iff.trans ?_
    (Stacks.SheafOfModulesEvaluation.isZero_iff_forall_isZero_evaluation _ _).symm
  simp only [ModuleCat.isZero_iff_subsingleton]
  exact ⟨fun hF x => hF x.unop.obj x.unop.property, fun hF x hx => hF (op ⟨x, hx⟩)⟩

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

variable [HasDerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))]
  [HasDerivedCategory (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))]

/-- **The kernel of `g^*` on the unbounded derived category, at module universe `u + 1`**: `g^*K`
vanishes exactly when every cohomology module of `K` is parasitic, for any models of the two
derived categories. -/
theorem isZero_moduleInverseImage_mapDerivedCategory_iff_forall_isParasitic
    (K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))) :
    IsZero ((moduleInverseImage B S hS 𝒳).mapDerivedCategory.obj K) ↔
      ∀ n : ℤ, IsParasitic.{u, w, u + 1} B S hS 𝒳 .fppf
        ((DerivedCategory.homologyFunctor _ n).obj K).val := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  refine forall_congr' fun n => ?_
  rw [isParasitic_iff_isZero_moduleInverseImage]
  exact (((moduleInverseImage B S hS 𝒳).mapDerivedCategoryHomologyIso n).app K).isZero_iff

/-- **Stacks 07B9** (2)(b) at module universe `u + 1`, for any class `L` of modules: for `K` in
`D_L(𝒪_𝒳)`, `g^*K = 0` exactly when `K` lies in `D_{Parasitic ∩ L}(𝒪_𝒳)`. -/
theorem isZero_moduleInverseImage_mapDerivedCategory_iff_of_class
    (L : ObjectProperty (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))
    (K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))
    (hK : DerivedCategoryB.derivedCategoryB L K) :
    IsZero ((moduleInverseImage B S hS 𝒳).mapDerivedCategory.obj K) ↔
      DerivedCategoryB.derivedCategoryB
        (A := SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
        (parasiticModules.{u, w, u + 1} B S hS 𝒳 .fppf ⊓ L) K :=
  (isZero_moduleInverseImage_mapDerivedCategory_iff_forall_isParasitic B S hS 𝒳 K).trans
    ⟨fun hp n => ⟨hp n, hK n⟩, fun hp n => (hp n).1⟩

end AlgebraicGeometry.Stack.FlatFppf
