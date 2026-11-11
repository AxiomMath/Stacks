module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.SliceLocalCohomology
public import StacksFrontier.AlgebraicGeometry.GroupScheme.SmoothPointsSheafBaseChangeEpi
public import StacksFrontier.AlgebraicGeometry.GroupScheme.SmoothGroupTorsorThickening
public import StacksFrontier.CategoryTheory.Sites.Cohomology.BaseChangePushforwardFirstCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.RightDerivedSectionsEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Size.EssentiallySmall
public import StacksFrontier.AlgebraicGeometry.GroupScheme.KernelOfReductionCohomology

/-!
# First cohomology of a smooth commutative group scheme lifts along a first-order thickening

Let `B` be a big fppf site, `S` a scheme of it, `z : Z ⟶ S` a monomorphism (in the application
the closed immersion `Spec k⟦t⟧/(tⁿ⁺¹) ⟶ Spec k⟦t⟧`) and `G` a smooth commutative group scheme over
`S`. For an object `U` of the big fppf site over `S` such that `U ×_S Z ⟶ U` is a first-order
thickening and `U` is Noetherian of dimension at most one, the restriction map

  `H¹_fppf(U, G) ⟶ H¹_fppf(U ×_S Z, G)`

is surjective. This is the cohomological content of part (b) of the proof of Stacks 0AFB, where
the source says that the obstruction to deforming a `G`-torsor along a first-order thickening lies
in an `H²` of a vector bundle on a curve, which vanishes.

## The proof

Write `𝒢 = G` for the sheaf of points, `𝒢'` for the sheaf `T ↦ 𝒢(T ×_S Z)`
(`CategoryTheory.Sheaf.baseChangePushforward`) and `φ : 𝒢 ⟶ 𝒢'` for restriction. The map of the
statement factors as `H¹(U, 𝒢) ⟶ H¹(U, 𝒢') ⟶ H¹(U ×_S Z, 𝒢') ≅ H¹(U ×_S Z, 𝒢)`, and:

* `H¹(U ×_S Z, 𝒢) ⟶ H¹(U ×_S Z, 𝒢')` is bijective, since `φ` is bijective over every object
  lying over `Z` (`AlgebraicGeometry.BigFppfOver.bijective_map_of_bijective_app_of_hom`);
* `H¹(U, 𝒢) ⟶ H¹(U, 𝒢')` is surjective: `φ` is locally surjective over `U`, by formal smoothness
  (`AlgebraicGeometry.exists_mem_topology_toBaseChangePushforward_pointsSheaf_eq`), so its
  cokernel has no cohomology over `U`, and its kernel, a vector group over `U`, has no `H²` over
  `U`
  (`AlgebraicGeometry.subsingleton_H'_two_of_isLimit_kernel_toBaseChangePushforward_pointsSheaf`);
* a class of `H¹(U ×_S Z, 𝒢)` dies on `T ×_S Z` for an étale covering `{T ⟶ U}`
  (`AlgebraicGeometry.exists_mem_topology_cohomologyPresheaf_map_baseChange_eq_zero`), so its image
  in `H¹(U ×_S Z, 𝒢')` comes from `H¹(U, 𝒢')`
  (`CategoryTheory.Sheaf.exists_baseChangeFst_cohomologyPresheaf_map_eq`).

## Main results

* `AlgebraicGeometry.surjective_cohomologyPresheaf_map_baseChangeFst_pointsSheaf`: the
  surjectivity.
* `Stacks.Cohomology.LongExactSequence.map_comp_apply`,
  `Stacks.Cohomology.LongExactSequence.map_cohomologyPresheaf_map`: functoriality of
  the maps `Stacks.Cohomology.LongExactSequence.map` in the sheaf and their naturality in the
  object.

## References

* [Stacks Project, Tag 0AFB](https://stacks.math.columbia.edu/tag/0AFB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.LongExactSequence

universe w u

namespace Stacks.Cohomology.LongExactSequence

section

variable {C : Type*} [Category.{u} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]

/-- The map on cohomology over an object induced by a composite of morphisms of sheaves is the
composite of the induced maps. -/
public lemma map_comp_apply {F G H : Sheaf J AddCommGrpCat.{u}} (f : F ⟶ G) (g : G ⟶ H) (n : ℕ)
    (U : C) (x : Sheaf.H' F n U) :
    map.{w} (f ≫ g) n U x = map.{w} g n U (map.{w} f n U x) := by
  change ((Sheaf.cohomologyPresheafFunctor.{w} J n).map (f ≫ g)).app (op U) x =
    ((Sheaf.cohomologyPresheafFunctor.{w} J n).map g).app (op U)
      (((Sheaf.cohomologyPresheafFunctor.{w} J n).map f).app (op U) x)
  rw [Functor.map_comp, NatTrans.comp_app]
  rfl

/-- The map on cohomology induced by a morphism of sheaves commutes with restriction along a
morphism of the site. -/
public lemma map_cohomologyPresheaf_map {F G : Sheaf J AddCommGrpCat.{u}} (f : F ⟶ G) (n : ℕ)
    {U V : C} (ε : V ⟶ U) (x : Sheaf.H' F n U) :
    map.{w} f n V ((F.cohomologyPresheaf n).map ε.op x) =
      (G.cohomologyPresheaf n).map ε.op (map.{w} f n U x) := by
  change ((Sheaf.cohomologyPresheafFunctor.{w} J n).map f).app (op V)
      ((F.cohomologyPresheaf n).map ε.op x) = _
  rw [← ConcreteCategory.comp_apply, NatTrans.naturality, ConcreteCategory.comp_apply]
  rfl

end

end Stacks.Cohomology.LongExactSequence

namespace AlgebraicGeometry

section Assembly

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
  {Z : Scheme.{u}} (hZ : B.Contains Z) (z : B.obj hZ ⟶ B.obj hS) [Mono z]
  [HasSheafify (BigFppfOver.topology B S hS) AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf (BigFppfOver.topology B S hS) AddCommGrpCat.{u})]

/-- **First cohomology of a smooth commutative group scheme lifts along a first-order
thickening of curves.** Let `z : Z ⟶ S` be a monomorphism of the big fppf site, `G` a smooth
commutative group scheme over the affine local scheme `S`, and `U` an object over `S` that is
Noetherian of dimension at most one and such that `U ×_S Z ⟶ U` is a first-order thickening. Then
restriction `H¹_fppf(U, G) ⟶ H¹_fppf(U ×_S Z, G)` is surjective. -/
public theorem surjective_cohomologyPresheaf_map_baseChangeFst_pointsSheaf
    [IsAffine S] [IsLocalRing Γ(S, ⊤)] (G : Over S) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (hG : B.Contains G.left) (U : BigFppfOver B S hS)
    (hU : Stacks.Thickenings.IsFirstOrderThickening
      (B.inclusion.map (Sheaf.baseChangeFst z U).left))
    [IsNoetherian (B.inclusion.obj U.left)]
    (hdim : topologicalKrullDim (B.inclusion.obj U.left : Type u) ≤ 1) :
    Function.Surjective
      (((pointsSheaf B S hS G hG).cohomologyPresheaf 1).map (Sheaf.baseChangeFst z U).op) := by
  set F := pointsSheaf B S hS G hG
  have : EssentiallySmall.{u} B.Schemes := AlgebraicGeometry.essentiallySmall_schemeBelow B.cutoff
  have : EssentiallySmall.{u} (BigFppfOver B S hS) :=
    CategoryTheory.essentiallySmall_over (B.obj hS)
  have : EnoughInjectives (Sheaf (BigFppfOver.topology B S hS) AddCommGrpCat.{u}) :=
    Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite.{u} _
  have hloc := exists_mem_topology_toBaseChangePushforward_pointsSheaf_eq B hS hZ z G hG U hU
  have hker : Subsingleton (Sheaf.H' (kernel (F.toBaseChangePushforward z)) 2 U) := 
    subsingleton_H'_two_of_isLimit_kernel_toBaseChangePushforward_pointsSheaf B hS hZ z G hG U hU
      hdim _ (kernel.ι (F.toBaseChangePushforward z)) (kernel.condition _) (kernelIsKernel _)
  have hleray : ∀ c : Sheaf.H' (F.baseChangePushforward z) 1
        ((Over.map z).obj ((Over.pullback z).obj U)),
      (∃ R ∈ BigFppfOver.topology B S hS U, ∀ ⦃T : BigFppfOver B S hS⦄ (t : T ⟶ U), R t →
        ((F.baseChangePushforward z).cohomologyPresheaf 1).map
          ((Over.map z).map ((Over.pullback z).map t)).op c = 0) →
      ∃ d : Sheaf.H' (F.baseChangePushforward z) 1 U,
        ((F.baseChangePushforward z).cohomologyPresheaf 1).map
          (Sheaf.baseChangeFst z U).op d = c := fun c hc ↦
    Sheaf.exists_baseChangeFst_cohomologyPresheaf_map_eq (C := B.Schemes) (J := B.topology)
      (X := B.obj hZ) (Y := B.obj hS) z F U c hc
  have hkill := exists_mem_topology_cohomologyPresheaf_map_baseChange_eq_zero B hS hZ z G hG U
    hU.isThickening
  set φ := F.toBaseChangePushforward z
  set V := (Over.map z).obj ((Over.pullback z).obj U)
  -- (c): `φ` is bijective on the cohomology over `V`, since `V` lies over `Z`
  have hV : Function.Bijective (map.{w} φ 1 V) :=
    BigFppfOver.bijective_map_of_bijective_app_of_hom B S hS φ V (fun T g ↦ by
      have := Sheaf.isIso_toBaseChangePushforward_hom_app z F (g.left ≫ pullback.snd _ _) (by
        rw [Category.assoc]
        exact Over.w g)
      exact ConcreteCategory.bijective_of_isIso _) 1
  -- (a): `φ` is surjective on the cohomology over `U`
  have hU : Function.Surjective (map.{w} φ 1 U) := by
    have h₁ : Function.Surjective (map.{w} (Abelian.coimage.π φ) 1 U) := fun y ↦
      (exact_map_δ _ (shortExact_kernel_coimage φ) 1 2 rfl U y).mp (hker.elim _ _)
    have h₂ : Function.Surjective (map.{w} (Abelian.factorThruCoimage φ) 1 U) :=
      (bijective_map_f_of_subsingleton (shortExact_coimage_cokernel φ) U (fun q ↦
        AddCommGrpCat.subsingleton_of_isZero
          (BigFppfOver.isZero_H'_of_subsingleton_of_hom B S hS _ U (fun T g ↦
            BigFppfOver.subsingleton_cokernel_obj B S hS φ T (fun Y f s ↦ hloc (f ≫ g) s)) q))
        1).2
    have hfac : Abelian.coimage.π φ ≫ Abelian.factorThruCoimage φ = φ := Abelian.coimage.fac φ
    intro y
    obtain ⟨x₁, rfl⟩ := h₂ y
    obtain ⟨x, rfl⟩ := h₁ x₁
    exact ⟨x, by rw [← map_comp_apply, hfac]⟩
  -- (b) and the diagram chase
  intro c₀
  obtain ⟨R, hR, hkill'⟩ := hkill c₀
  obtain ⟨d, hd⟩ := hleray (map.{w} φ 1 V c₀) ⟨R, hR, fun T t ht ↦ by
    rw [← map_cohomologyPresheaf_map, hkill' t ht, map_zero]⟩
  obtain ⟨e, rfl⟩ := hU d
  refine ⟨e, hV.1 ?_⟩
  rw [map_cohomologyPresheaf_map, hd]

end Assembly

end AlgebraicGeometry
