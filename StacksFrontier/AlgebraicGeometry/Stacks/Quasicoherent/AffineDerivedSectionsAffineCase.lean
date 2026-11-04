module

public import StacksFrontier.AlgebraicGeometry.Stacks.AffineCoveringFamily
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDerivedSectionsComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentSemiorthogonalDecompositionSucc
public import StacksFrontier.AlgebraicGeometry.Stacks.ParasiticLisseEtaleVanishing
public import StacksFrontier.CategoryTheory.Sites.VanishingOnCovering

/-!
# Stacks 0H15 over an affine scheme: detecting isomorphisms of `𝒜` on flat affine objects

Let `𝒳` be an algebraic stack and `𝒜 ⊂ D(𝒪_𝒳)` the objects of `D_{LQCoh^fbc}(𝒪_𝒳)` left
orthogonal to `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` (Stacks 07BA, 0H11 at module universe `u + 1`);
every `Lg_! H` lies in `𝒜`. This file proves the formal half of the last paragraph of the proof
of **Stacks 0H15** (the case `𝒳 = (Sch/X)_{fppf}` with `X = Spec(R)` affine):

* a morphism `φ : N ⟶ K` of `𝒜` is an isomorphism as soon as `RΓ(x, φ)` is one for every flat
  object `x` lying over an affine scheme: its cone lies in `𝒜` and, by the edge isomorphism of
  `D_{LQCoh^fbc}` over affine objects, has parasitic cohomology, so it is left orthogonal to
  itself;
* consequently the base change property of Stacks 0H15 passes from `N` to `K`;
* when every flat affine object maps flatly to one flat affine object `ξ` (for `(Sch/X)_{fppf}`,
  `ξ = X`), invertibility of `RΓ(ξ, φ)` suffices, by the flat case of Stacks 0H15 for `N` and `K`.

In the source, `N = M^•_{fppf}` for a K-flat complex `M^•` representing `RΓ(X, K)`, and the map
`N ⟶ Lg_! K` is `Lg_!` of the comparison `M^•_{flat, fppf} ⟶ K`.

## Main results

All in the namespace `AlgebraicGeometry.Stack.FlatFppf`:

* `isIso_of_isIso_derivedSections_flatAffine`
* `hasAffineDerivedSectionsBaseChange_of_isIso_derivedSections_flatAffine`
* `derivedSectionsBaseChange_naturality`
* `hasAffineDerivedSectionsBaseChange_of_isIso_derivedSections_of_flat_hom`
* `exists_flat_hom_schemeStack_id`
* `leftOrthogonal_derivedModuleLowerShriekSucc`

## References

* [Stacks Project, Tag 0H15](https://stacks.math.columbia.edu/tag/0H15)
* [Stacks Project, Tag 07BA](https://stacks.math.columbia.edu/tag/07BA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open Stacks.Cohomology.HypercohomologyEdge
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange

universe u w

namespace AlgebraicGeometry.Stack.FlatFppf

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasSheafify_fppfTopology_largeSections
  wEqualsLocallyBijective_fppfTopology_largeSections

attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

attribute [local instance] isGrothendieckAbelian_ambientModulesSucc

attribute [-instance] Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **`Lg_! H` is left orthogonal to `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`** (Stacks 07BA, at module
universe `u + 1`): `Hom(Lg_! H, P) = Hom(H, g^* P) = 0`, `g^*` killing objects with parasitic
cohomology. -/
theorem leftOrthogonal_derivedModuleLowerShriekSucc
    (H : DerivedCategory (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))) :
    (DerivedCategory.KernelColocalization.derivedInter (parasiticModulesSucc B S hS 𝒳)
      (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).leftOrthogonal
      ((derivedModuleLowerShriekSucc B S hS 𝒳).obj H) := by
  intro P f hP
  have hz : IsZero ((moduleInverseImage B S hS 𝒳).mapDerivedCategory.obj P) :=
    (isZero_moduleInverseImage_mapDerivedCategory_iff_forall_isParasitic B S hS 𝒳 P).2
      fun n => (hP n).1
  exact ((derivedModuleLowerShriekSuccAdjunction B S hS 𝒳).homEquiv _ P).injective
    (hz.eq_of_tgt _ _)

/-- **A morphism of `𝒜` is detected on flat affine objects.** Let `φ : N ⟶ K` be a morphism
between objects of `D_{LQCoh^fbc}(𝒪_𝒳)` left orthogonal to `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`. If
`RΓ(x, φ)` is invertible for every flat object `x` lying over an affine scheme, `φ` is an
isomorphism.

Its cone `C` lies in `D_{LQCoh^fbc}` and is left orthogonal to `D_{Parasitic ∩ LQCoh^fbc}`, both
being triangulated. Over a flat affine `x`, `RΓ(x, C) = 0`, so `Γ(x, H^q C) = H^q(RΓ(x, C)) = 0`
(the edge isomorphism, Stacks 0BKZ for `LQCoh^fbc`); a flat object is covered by flat affine ones,
so `H^q C` is parasitic. Then `C` is left orthogonal to itself, hence zero. -/
theorem isIso_of_isIso_derivedSections_flatAffine
    {N K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))}
    (φ : N ⟶ K)
    (hN : DerivedCategory.KernelColocalization.interLeftOrthogonal (parasiticModulesSucc B S hS 𝒳)
      (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) N)
    (hK : DerivedCategory.KernelColocalization.interLeftOrthogonal (parasiticModulesSucc B S hS 𝒳)
      (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) K)
    (hφ : ∀ x : 𝒳.val.val.obj, flatObject B S hS 𝒳.val x →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)) →
      IsIso ((derivedSections.{_, _, _, u + 1, u + 1} (ambientRingStructureSheaf B S hS 𝒳) x).map
        φ)) :
    IsIso φ := by
  let O := ambientRingStructureSheaf B S hS 𝒳
  obtain ⟨C, b, c, hT⟩ := distinguished_cocone_triangle φ
  have hCL : DerivedCategoryB.derivedCategoryB (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) C :=
    ObjectProperty.ext_of_isTriangulatedClosed₃ _ _ hT hN.2 hK.2
  have hCo : (DerivedCategory.KernelColocalization.derivedInter (parasiticModulesSucc B S hS 𝒳)
      (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).leftOrthogonal C :=
    ObjectProperty.ext_of_isTriangulatedClosed₃ _ _ hT hN.1 hK.1
  -- `RΓ(x, C) = 0` over flat affine objects
  have hRΓ : ∀ x : 𝒳.val.val.obj, flatObject B S hS 𝒳.val x →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)) →
      IsZero ((derivedSections.{_, _, _, u + 1, u + 1} O x).obj C) := fun x hx hxa => by
    let _ := Functor.IsRightDerivedFunctor.commShift (derivedSections.{_, _, _, u + 1, u + 1} O x)
      (derivedSectionsUnit O x)
      (HomotopyCategory.quasiIso (SheafOfModules.{u + 1} O) (ComplexShape.up ℤ)) ℤ
    have htri : (derivedSections.{_, _, _, u + 1, u + 1} O x).IsTriangulated :=
      Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor
        Stacks.Cohomology.Localization.enoughKInjectives (homotopySections O x)
        (derivedSections O x) (derivedSectionsUnit O x)
    have := hφ x hx hxa
    exact Triangle.isZero₃_of_isIso₁ _
      ((derivedSections.{_, _, _, u + 1, u + 1} O x).map_distinguished _ hT)
      (hφ x hx hxa)
  -- the cohomology sheaves of `C` vanish over flat affine objects
  have hsec : ∀ (q : ℤ) (x : 𝒳.val.val.obj), flatObject B S hS 𝒳.val x →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)) →
      IsZero ((SheafOfModules.evaluation O (op x)).obj
        ((DerivedCategory.homologyFunctor _ q).obj C)) := fun q x hx hxa => by
    have := isIso_hypercohomologyEdge_app_of_sheafFlatBaseChange B S hS 𝒳 E h C hCL x hxa q
    exact (((DerivedCategory.homologyFunctor _ q).map_isZero (hRΓ x hx hxa))).of_iso
      (asIso ((hypercohomologyEdge.{_, _, _, u + 1, u + 1} O x q).app C)).symm
  -- hence over all flat objects: a flat object is covered by flat affine ones
  have hpar : ∀ q : ℤ, parasiticModulesSucc B S hS 𝒳
      ((DerivedCategory.homologyFunctor _ q).obj C) := fun q x hx => by
    obtain ⟨I, y, f, hy, haff, hflat⟩ := exists_isAffine_covering_of_object B S hS 𝒳.val x
    have hz := Sheaf.isZero_sections_of_isZero_sections_of_covering
      ((SheafOfModules.toSheaf O).obj ((DerivedCategory.homologyFunctor _ q).obj C))
      (Presieve.ofArrows y f) hy (by
        rintro _ _ ⟨i⟩
        exact @AddCommGrpCat.isZero_of_subsingleton _
          (ModuleCat.isZero_iff_subsingleton.1 (hsec q (y i)
            (flatObject_of_flat B S hS 𝒳 (f i) (hflat i) hx) (haff i))))
    exact AddCommGrpCat.subsingleton_of_isZero hz
  have hC : DerivedCategory.KernelColocalization.derivedInter (parasiticModulesSucc B S hS 𝒳)
      (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) C := fun q => ⟨hpar q, hCL q⟩
  have hz : IsZero C := by
    rw [IsZero.iff_id_eq_zero]
    exact hCo (𝟙 C) hC
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 hz

/-- **The base change property of Stacks 0H15 passes along a morphism of `𝒜` invertible on flat
affine objects.** -/
theorem hasAffineDerivedSectionsBaseChange_of_isIso_derivedSections_flatAffine
    {N K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))}
    (φ : N ⟶ K)
    (hN : DerivedCategory.KernelColocalization.interLeftOrthogonal (parasiticModulesSucc B S hS 𝒳)
      (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) N)
    (hK : DerivedCategory.KernelColocalization.interLeftOrthogonal (parasiticModulesSucc B S hS 𝒳)
      (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) K)
    (hφ : ∀ x : 𝒳.val.val.obj, flatObject B S hS 𝒳.val x →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)) →
      IsIso ((derivedSections.{_, _, _, u + 1, u + 1} (ambientRingStructureSheaf B S hS 𝒳) x).map
        φ))
    (hbc : HasAffineDerivedSectionsBaseChange B S hS 𝒳 N) :
    HasAffineDerivedSectionsBaseChange B S hS 𝒳 K := by
  have := isIso_of_isIso_derivedSections_flatAffine B E h S hS 𝒳 φ hN hK hφ
  intro x x' a hx hx'
  exact (isIso_derivedSectionsBaseChange_iff_of_iso B S hS 𝒳 (asIso φ) a).1 (hbc a hx hx')

/-- The map of Stacks 0H15 is natural in the object: for `φ : N ⟶ K` and `a : x ⟶ x'`,
`(RΓ(x', φ) ⊗^L 𝒪(x)) ≫ (RΓ(x', K) ⊗^L 𝒪(x) ⟶ RΓ(x, K)) =
(RΓ(x', N) ⊗^L 𝒪(x) ⟶ RΓ(x, N)) ≫ RΓ(x, φ)`. -/
theorem derivedSectionsBaseChange_naturality
    {N K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))}
    (φ : N ⟶ K) {x x' : 𝒳.val.val.obj} (a : x ⟶ x') :
    (dBaseChange.{u, u + 1} ((ambientRingStructureSheaf B S hS 𝒳).obj.map a.op)
        (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x')
        (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x)).map
        ((derivedSections.{_, _, _, u + 1, u + 1} (ambientRingStructureSheaf B S hS 𝒳) x').map
          φ) ≫ derivedSectionsBaseChange B S hS 𝒳 a K =
      derivedSectionsBaseChange B S hS 𝒳 a N ≫
        (derivedSections.{_, _, _, u + 1, u + 1} (ambientRingStructureSheaf B S hS 𝒳) x).map φ := by
  let adj := dBaseChangeAdj.{u, u + 1} ((ambientRingStructureSheaf B S hS 𝒳).obj.map a.op)
    (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x')
    (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x)
  have h1 := adj.homEquiv_naturality_left_symm
    ((derivedSections.{_, _, _, u + 1, u + 1} (ambientRingStructureSheaf B S hS 𝒳) x').map φ)
    ((derivedSectionsRestrict.{_, _, _, u + 1, u + 1} (ambientRingStructureSheaf B S hS 𝒳)
      a).app K)
  have h2 := adj.homEquiv_naturality_right_symm
    ((derivedSectionsRestrict.{_, _, _, u + 1, u + 1} (ambientRingStructureSheaf B S hS 𝒳)
      a).app N)
    ((derivedSections.{_, _, _, u + 1, u + 1} (ambientRingStructureSheaf B S hS 𝒳) x).map φ)
  have h3 := (derivedSectionsRestrict.{_, _, _, u + 1, u + 1} (ambientRingStructureSheaf B S hS 𝒳)
    a).naturality φ
  exact h1.symm.trans ((congrArg (adj.homEquiv _ _).symm h3).trans h2)

/-- **Over a stack with a flat affine object `ξ` receiving a flat arrow from every flat affine
object** (for `(Sch/X)_{fppf}` with `X` affine, `ξ = X`): the base change property of
Stacks 0H15 passes from `N` to `K` along a morphism `φ : N ⟶ K` of `𝒜` such that `RΓ(ξ, φ)` is
invertible. Over a flat affine `x` with a flat arrow `a : x ⟶ ξ`, the maps of Stacks 0H15 along
`a` are invertible for `N` (its base change property) and for `K` (the flat case,
`isIso_derivedSectionsBaseChange_of_flat`), and they intertwine `RΓ(ξ, φ) ⊗^L 𝒪(x)` with
`RΓ(x, φ)`. -/
theorem hasAffineDerivedSectionsBaseChange_of_isIso_derivedSections_of_flat_hom
    {N K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))}
    (φ : N ⟶ K)
    (hN : DerivedCategory.KernelColocalization.interLeftOrthogonal (parasiticModulesSucc B S hS 𝒳)
      (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) N)
    (hK : DerivedCategory.KernelColocalization.interLeftOrthogonal (parasiticModulesSucc B S hS 𝒳)
      (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) K)
    (hbc : HasAffineDerivedSectionsBaseChange B S hS 𝒳 N)
    (ξ : 𝒳.val.val.obj) (hξ : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj ξ)))
    (hmap : ∀ x : 𝒳.val.val.obj, flatObject B S hS 𝒳.val x →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)) →
      ∃ a : x ⟶ ξ, Flat (B.inclusion.map (𝒳.val.val.p.map a).left))
    (hφ : IsIso ((derivedSections.{_, _, _, u + 1, u + 1} (ambientRingStructureSheaf B S hS 𝒳)
      ξ).map φ)) :
    HasAffineDerivedSectionsBaseChange B S hS 𝒳 K := by
  refine hasAffineDerivedSectionsBaseChange_of_isIso_derivedSections_flatAffine B E h S hS 𝒳 φ
    hN hK (fun x hx hxa => ?_) hbc
  obtain ⟨a, ha⟩ := hmap x hx hxa
  have := hbc a hxa hξ
  have := isIso_derivedSectionsBaseChange_of_flat B S hS 𝒳 E h K hK.2 a hxa hξ ha
  have e := derivedSectionsBaseChange_naturality B S hS 𝒳 φ a
  have : IsIso (derivedSectionsBaseChange B S hS 𝒳 a N ≫
      (derivedSections.{_, _, _, u + 1, u + 1} (ambientRingStructureSheaf B S hS 𝒳) x).map φ) := by
    rw [← e]; infer_instance
  exact IsIso.of_isIso_comp_left (derivedSectionsBaseChange B S hS 𝒳 a N) _

/-- **In `(Sch/X)_{fppf}` every flat object has a flat arrow to `X`**: an object `x : T ⟶ X` of
the stack of a scheme `X` is flat exactly when `T ⟶ X` is flat
(`AlgebraicGeometry.Stack.flatObject_schemeStack_iff`), and `x` itself is an arrow to the
terminal object `𝟙 X`. -/
theorem exists_flat_hom_schemeStack_id (X : BigFppfOver B S hS)
    (x : (schemeStack.{u, w} B S hS X).val.val.obj)
    (hx : flatObject B S hS (schemeStack.{u, w} B S hS X).val x) :
    ∃ a : x ⟶ (Over.mk.{u, u + 1} (𝟙 X) : (schemeStack.{u, w} B S hS X).val.val.obj),
      Flat (B.inclusion.map ((schemeStack.{u, w} B S hS X).val.val.p.map a).left) :=
  ⟨Over.homMk x.hom, (flatObject_schemeStack_iff.{u, w} B S hS X x).1 hx⟩

end AlgebraicGeometry.Stack.FlatFppf

end
