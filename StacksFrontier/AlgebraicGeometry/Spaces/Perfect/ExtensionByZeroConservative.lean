module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisStalkDegeneracies
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleShriekForgetStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleStalkConservative

/-!
# Extension by zero along an étale morphism is conservative

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S`.  Equation 08GU
computes the stalk of the extension by zero `f_!M` of a sheaf of `𝒪_X`-modules at a geometric
point `x̄` of `Y` as the direct sum of the stalks of `M` at the geometric points of `X` over
`x̄`.  A geometric point of `X` is one of the points over its own image, so every stalk of `M`
appears as a summand of a stalk of `f_!M`; hence `f_!M = 0` forces `M = 0`, and `f_!` — being
exact — reflects isomorphisms, both of sheaves of modules and of objects of the unbounded
derived category.

## Main results

* `AlgebraicGeometry.Space.isZero_of_isZero_etaleModuleLowerShriek` and
  `AlgebraicGeometry.Space.isZero_of_isZero_leftAdjoint_etaleModulePullback`: extension by
  zero reflects zero objects.
* `AlgebraicGeometry.Space.isIso_of_isIso_map_leftAdjoint_etaleModulePullback` and
  `AlgebraicGeometry.Space.`
  `isIso_of_isIso_mapDerivedCategory_map_leftAdjoint_etaleModulePullback`: it reflects
  isomorphisms of modules, and so does the induced functor on unbounded derived categories.

## Implementation notes

Extension by zero is taken as an arbitrary left adjoint of restriction wherever possible, as
elsewhere in this development; the canonical one of
`AlgebraicGeometry.Space.etaleModuleLowerShriek` is where the stalk computation is available,
and `CategoryTheory.Adjunction.leftAdjointUniq` carries the conclusion to any other.

## References

* [Stacks Project, Tag 08GU](https://stacks.math.columbia.edu/tag/08GU)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂ u

namespace CategoryTheory

/-- A summand of a vanishing coproduct vanishes: the inclusion of the summand is split by the
map which is the identity on it and zero on the others. -/
theorem Limits.isZero_of_isZero_sigma {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {I : Type*} (K : I → C) [HasCoproduct K] (h : IsZero (∐ K)) (t : I) : IsZero (K t) := by
  classical
  have hsplit : Sigma.ι K t ≫
      Sigma.desc (fun i => if hi : i = t then eqToHom (by rw [hi]) else 0) = 𝟙 (K t) := by
    simp
  rw [IsZero.iff_id_eq_zero, ← hsplit, h.eq_of_tgt (Sigma.ι K t) 0, zero_comp]

/-- **An exact functor of abelian categories which reflects zero objects reflects
isomorphisms.**  Exactness carries the kernel and the cokernel of a morphism to those of its
image, so a morphism whose image is invertible has vanishing kernel and cokernel, hence is both
a monomorphism and an epimorphism. -/
theorem Functor.isIso_of_isIso_map_of_reflects_isZero {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] (F : A ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : ∀ M : A, IsZero (F.obj M) → IsZero M) {Xo Yo : A} (g : Xo ⟶ Yo)
    (hg : IsIso (F.map g)) : IsIso g := by
  have := hg
  have hm : Mono g :=
    Preadditive.mono_of_isZero_kernel g
      (hF _ ((isZero_kernel_of_mono (F.map g)).of_iso (PreservesKernel.iso F g)))
  have he : Epi g :=
    Preadditive.epi_of_isZero_cokernel g
      (hF _ ((isZero_cokernel_of_epi (F.map g)).of_iso (PreservesCokernel.iso F g)))
  exact isIso_of_mono_of_epi g

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A sheaf of modules on the small étale site of an algebraic space all of whose geometric
stalks vanish is zero**: the geometric points are a conservative family by Stacks 04K5. -/
theorem isZero_of_forall_isZero_edsModuleStalk {X : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS X.1 X.2)
    (h : ∀ x : GeometricPoint B S hS X.1, IsZero ((edsModuleStalk B S hS x).obj M)) :
    IsZero M := by
  refine Stacks.isZero_of_isZero_sheafModuleFiber (etaleRingSheaf B S hS X)
    (isConservativeFamilyOfPoints_etaleSitePoint B S hS X.1 X.2) ?_
  rintro ⟨Φ, hΦ⟩
  obtain ⟨x, rfl⟩ := (ObjectProperty.ofObj_iff _ Φ).1 hΦ
  exact h x

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)

/-- The lift of a geometric point of `X` along `f` to itself, over its own image in `Y`. -/
def tautologicalGeometricPointLift (x : GeometricPoint B S hS X.1) :
    GeometricPointLift B S hS f.hom (geometricPointMap f.hom x) :=
  ⟨x.val.value, rfl⟩

/-- The geometric point attached to the tautological lift is the point itself. -/
theorem liftGeometricPoint_tautologicalGeometricPointLift (x : GeometricPoint B S hS X.1) :
    liftGeometricPoint B S hS f (tautologicalGeometricPointLift B S hS f x) = x :=
  rfl

/-- **Extension by zero along an étale morphism reflects zero objects.**  By Equation 08GU the
stalk of `f_!M` at the image of a geometric point `x̄` of `X` is the direct sum of the stalks of
`M` at the points of `X` over that image, one of which is `x̄` itself; so all stalks of `M`
vanish, and a sheaf of modules with vanishing geometric stalks is zero. -/
theorem isZero_of_isZero_etaleModuleLowerShriek (M : Modules.{u, u} B S hS X.1 X.2)
    (h : IsZero ((etaleModuleLowerShriek B S hS f hf).obj M)) : IsZero M := by
  refine isZero_of_forall_isZero_edsModuleStalk B S hS M fun x => ?_
  refine isZero_edsModuleStalk_of_isZero_sheafFiber B S hS M x ?_
  have hshriek : IsZero ((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).sheafFiber.obj
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).obj
        ((etaleModuleLowerShriek B S hS f hf).obj M))) :=
    Functor.map_isZero _ (Functor.map_isZero _ h)
  have habelian : IsZero
      ((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).sheafFiber.obj
        ((abelianEtaleExtensionByZero B S hS f hf).obj
          ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).obj M))) :=
    hshriek.of_iso
      (((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).sheafFiber
        (A := AddCommGrpCat.{u})).mapIso ((etaleModuleShriekForgetIso B S hS f hf).app M))
  have hsum : IsZero (∐ fun t : GeometricPointLift B S hS f.hom (geometricPointMap f.hom x) =>
      (liftSitePoint B S hS f t).sheafFiber.obj
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).obj M)) :=
    habelian.of_iso (EtaleShriekStalk.stalkExtensionByZeroIso B S hS f hf
      (geometricPointMap f.hom x) _).symm
  exact Limits.isZero_of_isZero_sigma _ hsum (tautologicalGeometricPointLift B S hS f x)

variable {shriek : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2}
  (adj : shriek ⊣ etaleModulePullback.{u, u} B S hS f hf)

include adj in
/-- **Any left adjoint of restriction along an étale morphism reflects zero objects.**  Two
left adjoints of one functor are isomorphic, so this is
`AlgebraicGeometry.Space.isZero_of_isZero_etaleModuleLowerShriek`. -/
theorem isZero_of_isZero_leftAdjoint_etaleModulePullback (M : Modules.{u, u} B S hS X.1 X.2)
    (h : IsZero (shriek.obj M)) : IsZero M :=
  isZero_of_isZero_etaleModuleLowerShriek B S hS f hf M
    (h.of_iso ((Adjunction.leftAdjointUniq adj
      (etaleModuleLowerShriekAdjunction B S hS f hf)).app M).symm)

include adj in
/-- **Any left adjoint of restriction along an étale morphism reflects isomorphisms of sheaves
of modules.**  It is exact, and an exact functor of abelian categories reflecting zero objects
reflects isomorphisms. -/
theorem isIso_of_isIso_map_leftAdjoint_etaleModulePullback [shriek.Additive]
    [PreservesFiniteLimits shriek] [PreservesFiniteColimits shriek]
    {M N : Modules.{u, u} B S hS X.1 X.2} (α : M ⟶ N) (h : IsIso (shriek.map α)) : IsIso α :=
  Functor.isIso_of_isIso_map_of_reflects_isZero shriek
    (fun P hP => isZero_of_isZero_leftAdjoint_etaleModulePullback B S hS f hf adj P hP) α h

attribute [local instance] HasDerivedCategory.standard

include adj in
/-- **Any left adjoint of restriction along an étale morphism reflects isomorphisms of the
unbounded derived category.**  An exact functor inverts a morphism of derived categories exactly
when it inverts each of its homology maps, and it reflects invertibility of those. -/
theorem isIso_of_isIso_mapDerivedCategory_map_leftAdjoint_etaleModulePullback [shriek.Additive]
    [PreservesFiniteLimits shriek] [PreservesFiniteColimits shriek]
    {K L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)} (φ : K ⟶ L)
    (h : IsIso (shriek.mapDerivedCategory.map φ)) : IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  exact isIso_of_isIso_map_leftAdjoint_etaleModulePullback B S hS f hf adj _
    ((shriek.isIso_mapDerivedCategory_map_iff φ).1 h n)

end AlgebraicGeometry.Space

end
