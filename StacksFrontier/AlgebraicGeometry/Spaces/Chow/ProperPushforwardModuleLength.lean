module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFibreSum
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionGeometricLength
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricLengthPointIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPushforwardFibreLength
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp

/-!
# The length of a proper direct image of a coherent module over a generic point

In Situation 0EDT let `f : X ⟶ Y` be a proper morphism over the base of good algebraic spaces,
let `F` be a coherent `𝒪_X`-module with `dim_δ(Supp(F)) ≤ k` and let `η` be the generic point of
an integral closed subspace `W ⊂ Y` of δ-dimension `k`. Then at a geometric point `ȳ` over `η`

`length_ȳ(f_*F) = ∑_{x ∈ Supp(F), f(x) = η} length_x(F) · [κ(x) : κ(η)]`.

This is the computation the proof of Stacks 0EP3 performs, and it is reduced here, as in the
source, to a morphism with finite fibre over `η`: `F` is the direct image `i_*G` of a coherent
module on its scheme-theoretic support `i : Z → X` (Stacks 07U0, 07UG), so that
`f_*F = (f ∘ i)_*G` and the fibre of `f ∘ i` over `η` is the finite set of points of `Supp(F)`
over `η`. The lengths and residue degrees are unchanged along the closed immersion `i`
(Stacks 0EE3, and Stacks 0EMX).

## Main results

* `AlgebraicGeometry.Space.geometricLength_eq_of_iso`: isomorphic modules have the same length
  at a geometric point.
* `AlgebraicGeometry.Space.geometricLength_modulePushforward_of_isClosedImmersion`: Stacks 0EE3
  for the direct image of modules of Stacks 03LU along a closed immersion.
* `AlgebraicGeometry.Space.residueFieldDegreeAt_eq_one_of_mono`: a monomorphism induces trivial
  residue field extensions.
* `AlgebraicGeometry.Space.geometricLength_directImageModule_toNat_eq_finsum`: the formula above.

## References

* [Stacks Project, Tag 0EP3](https://stacks.math.columbia.edu/tag/0EP3)
* [Stacks Project, Tag 07U0](https://stacks.math.columbia.edu/tag/07U0)
* [Stacks Project, Tag 07UG](https://stacks.math.columbia.edu/tag/07UG)
* [Stacks Project, Tag 0EE3](https://stacks.math.columbia.edu/tag/0EE3)
* [Stacks Project, Tag 0EMX](https://stacks.math.columbia.edu/tag/0EMX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Isomorphic modules have the same length at a geometric point.** -/
theorem geometricLength_eq_of_iso (X : AlgebraicSpaces B S hS) (x : GeometricPoint B S hS X.1)
    {F G : Modules.{u, u} B S hS X.1 X.2} (e : F ≅ G) :
    geometricLength B S hS X x F = geometricLength B S hS X x G :=
  (LinearEquiv.ofLinearMap (geometricModuleStalkLinearMap B S hS X x e.hom)
    (geometricModuleStalkLinearMap B S hS X x e.inv)
    (LinearMap.ext fun z => by
      change geometricModuleStalkMap B S hS X x e.hom (geometricModuleStalkMap B S hS X x e.inv z)
        = z
      rw [← geometricModuleStalkMap_comp, e.inv_hom_id, geometricModuleStalkMap_id])
    (LinearMap.ext fun z => by
      change geometricModuleStalkMap B S hS X x e.inv (geometricModuleStalkMap B S hS X x e.hom z)
        = z
      rw [← geometricModuleStalkMap_comp, e.hom_inv_id, geometricModuleStalkMap_id])).length_eq

/-- **Stacks 0EE3 for the direct image of modules along a closed immersion**, at a geometric
point of the source. -/
theorem geometricLength_modulePushforward_of_isClosedImmersion {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f.hom) (x : GeometricPoint B S hS X.1)
    (G : Modules.{u, u} B S hS X.1 X.2) :
    geometricLength B S hS Y (geometricPointMap f.hom x) ((modulePushforward B S hS f).obj G) =
      geometricLength B S hS X x G :=
  (geometricLength_eq_of_iso B S hS Y _ (modulePushforwardIsoChartDirectImage B S hS f hf G)).trans
    (geometricLength_chartDirectImage B S hS f hf x G)

/-- The residue field extension of a monomorphism at a point is trivial: the residue field
homomorphism is an isomorphism by Stacks 0EMX, so its degree is one. -/
theorem residueFieldDegreeAt_eq_one_of_mono {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hDX : IsDecentSpace B S hS X)
    (hDY : IsDecentSpace B S hS Y) (f : X ⟶ Y) [Mono f] (x : points B S hS X) :
    residueFieldDegreeAt B S hS hY hDX hDY f x = 1 := by
  have hmono : Mono (residueFieldMorphism B S hS X hDX x ≫ f) := by
    have := (residueFieldRepresentative B S hS X hDX x).2.2
    exact mono_comp _ _
  have hiso := (isIso_residueFieldHom_iff_mono B S hS X Y hY hDX hDY f x).mpr hmono
  let φ := residueFieldHom B S hS X Y hY hDX hDY f x
  have hbij : Function.Bijective φ :=
    (ConcreteCategory.isIso_iff_bijective (CommRingCat.ofHom φ)).mp hiso
  let := residueFieldAlgebra B S hS hY hDX hDY f x
  let e : residueField B S hS Y hDY (pointsMap B S hS X f x) ≃ₐ[
      residueField B S hS Y hDY (pointsMap B S hS X f x)] residueField B S hS X hDX x :=
    AlgEquiv.ofBijective (Algebra.ofId _ _) hbij
  change Module.finrank _ _ = 1
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

end General

section Chow

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)

include hY in
/-- A point of `Supp(F)` with `dim_δ(Supp(F)) ≤ k` whose image specializes to the generic point
of an integral closed subspace of δ-dimension `k` maps to that generic point. -/
private theorem pointsMap_eq_ambientGenericPoint_of_specializes {f : X ⟶ Y} (hfB : f ≫ sY = sX)
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [IsCoherent D.site D.base D.base_mem X hX.1 F] (k : ℤ)
    (hdimF : deltaDimensionClosed D sX hX (moduleSupport D.site D.base D.base_mem hX.1 F)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) ≤ (k : EInt))
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) (hW : deltaDimension D sY W = k)
    {x : points D.site D.base D.base_mem X}
    (hx : x ∈ moduleSupport D.site D.base D.base_mem hX.1 F)
    (hsp : pointsMap D.site D.base D.base_mem X f x ⤳
      W.ambientGenericPoint D.site D.base D.base_mem) :
    pointsMap D.site D.base D.base_mem X f x = W.ambientGenericPoint D.site D.base D.base_mem := by
  have hxk := (deltaDimensionClosed_le_coe_iff D sX hX _ _ k).mp hdimF x hx
  have hfx := inducedDimensionValue_pointsMap_le D sX hX sY hY f hfB x
  by_contra hne
  have hlt := lt_inducedDimensionValue_of_specializes D.site D.base D.base_mem hY.1
    (D.isDecentSpace_of_isGood sY hY) D.isAlgebraicSpace
    (isDecentSpace_of_isAbsolutelyQuasiSeparated D.site D.base D.base_mem D.space
      D.isAlgebraicSpace D.quasiSeparated)
    D.locallyNoetherian D.universallyCatenary D.delta sY hY.2.2 hsp hne
  have hWk : inducedDimensionValue D.site D.base D.base_mem D.delta sY
      (W.ambientGenericPoint D.site D.base D.base_mem) = k := hW
  rw [hWk] at hlt
  omega

/-- Over a closed subspace `Z ⊂ X` whose points are the support of `F`, the length of
`(f ∘ i)_*G` at a geometric point over the generic point `η` of `W` is the fibre sum over `η`. -/
private theorem geometricLength_modulePushforward_comp_closedSubspace_toNat_eq_finsum {f : X ⟶ Y}
    (hfB : f ≫ sY = sX) (hproper : IsProper D.site D.base D.base_mem f)
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [IsCoherent D.site D.base D.base_mem X hX.1 F] (k : ℤ)
    (hdimF : deltaDimensionClosed D sX hX (moduleSupport D.site D.base D.base_mem hX.1 F)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) ≤ (k : EInt))
    (γX : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγX : ∀ x, (γX x).LiesOver x)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) (hW : deltaDimension D sY W = k)
    (ybar : GeometricPoint D.site D.base D.base_mem Y)
    (hybar : ybar.LiesOver (W.ambientGenericPoint D.site D.base D.base_mem))
    (Z : ClosedSubspaces D.site D.base D.base_mem X)
    (G : Modules.{u, u} D.site D.base D.base_mem Z.1.toFunctor Z.2.1)
    [IsCoherent D.site D.base D.base_mem Z.1.toFunctor Z.2.1 G]
    (hrange : moduleSupport D.site D.base D.base_mem hX.1 F =
      Set.range (pointsMap D.site D.base D.base_mem Z.1.toFunctor Z.1.ι)) :
    (geometricLength D.site D.base D.base_mem ⟨Y, hY.1⟩ ybar
        ((modulePushforward D.site D.base D.base_mem
          (closedSubspaceInclusion D.site D.base D.base_mem ⟨X, hX.1⟩ Z ≫
            (ObjectProperty.homMk f :
              (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩))).obj G)).toNat =
      ∑ᶠ z ∈ {z | pointsMap D.site D.base D.base_mem Z.1.toFunctor (Z.1.ι ≫ f) z =
          W.ambientGenericPoint D.site D.base D.base_mem},
        (geometricLength D.site D.base D.base_mem
          (closedSubspaceToSpace D.site D.base D.base_mem ⟨X, hX.1⟩ Z)
          (canonicalGeometricPoint D.site D.base D.base_mem Z.1.toFunctor z) G).toNat *
        residueFieldDegreeAt D.site D.base D.base_mem hY.1
          (isDecentSpace_of_isClosedSubspace D.site D.base D.base_mem
            (D.isDecentSpace_of_isGood sX hX) Z.2)
          (D.isDecentSpace_of_isGood sY hY) (Z.1.ι ≫ f) z := by
  let XA : AlgebraicSpaces D.site D.base D.base_mem := ⟨X, hX.1⟩
  let YA : AlgebraicSpaces D.site D.base D.base_mem := ⟨Y, hY.1⟩
  let fA : XA ⟶ YA := ObjectProperty.homMk f
  let i := closedSubspaceInclusion D.site D.base D.base_mem XA Z
  let g : closedSubspaceToSpace D.site D.base D.base_mem XA Z ⟶ YA := i ≫ fA
  have hg : IsProper D.site D.base D.base_mem g.hom :=
    isProper_comp D.site D.base D.base_mem Z.2.1 hX.1 hY.1 i.hom f
      (isProper_of_isClosedImmersion D.site D.base D.base_mem Z.2.1 hX.1 i.hom Z.2.2) hproper
  set η := W.ambientGenericPoint D.site D.base D.base_mem
  have hgz : ∀ z, pointsMap D.site D.base D.base_mem Z.1.toFunctor g.hom z =
      pointsMap D.site D.base D.base_mem X f (pointsMap D.site D.base D.base_mem _ i.hom z) :=
    fun z => pointsMap_comp_apply D.site D.base D.base_mem i.hom f z
  have hmemS : ∀ z, pointsMap D.site D.base D.base_mem Z.1.toFunctor i.hom z ∈
      moduleSupport D.site D.base D.base_mem hX.1 F := fun z => hrange ▸ ⟨z, rfl⟩
  have : Mono i.hom := inferInstanceAs (Mono (Subfunctor.ι _))
  have hfin : {z : points D.site D.base D.base_mem Z.1.toFunctor |
      pointsMap D.site D.base D.base_mem _ g.hom z = η}.Finite :=
    ((finite_moduleSupport_fibre D sX hX sY hY hfB hproper.2.1.2 F k hdimF γX hγX W hW).preimage
      (pointsMap_injective_of_mono D.site D.base D.base_mem i.hom).injOn).subset
      fun z hz => ⟨(hgz z).symm.trans hz, hmemS z⟩
  have hmax : ∀ z ∈ supportOfSheaf D.site D.base D.base_mem Z.1.toFunctor
      ((SheafOfModules.toSheaf _).obj G),
      η ∈ closure {pointsMap D.site D.base D.base_mem _ g.hom z} →
        pointsMap D.site D.base D.base_mem _ g.hom z = η := by
    intro z _ hcl
    rw [hgz z] at hcl ⊢
    exact pointsMap_eq_ambientGenericPoint_of_specializes D sX hX sY hY hfB F k hdimF W hW
      (hmemS z) (specializes_iff_mem_closure.mpr hcl)
  exact geometricLength_modulePushforward_toNat_eq_finsum D.site D.base D.base_mem
    (isDecentSpace_of_isClosedSubspace D.site D.base D.base_mem
      (D.isDecentSpace_of_isGood sX hX) Z.2)
    (D.isDecentSpace_of_isGood sY hY) (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
    g hg G η hfin hmax ybar hybar _
    (canonicalGeometricPoint_image D.site D.base D.base_mem Z.1.toFunctor)

/-- Pushing a fibre sum over a closed subspace `i : Z → X` with `F ≅ i_*G` and `Supp(F) = i(Z)`
forward along `i` gives the fibre sum of `length_x(F) · [κ(x) : κ(y)]` over `Supp(F)`. -/
private theorem finsum_closedSubspace_fibre_eq_finsum_moduleSupport_fibre (f : X ⟶ Y)
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [IsCoherent D.site D.base D.base_mem X hX.1 F]
    (γX : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγX : ∀ x, (γX x).LiesOver x)
    (Z : ClosedSubspaces D.site D.base D.base_mem X)
    (G : Modules.{u, u} D.site D.base D.base_mem Z.1.toFunctor Z.2.1)
    (e : (modulePushforward D.site D.base D.base_mem
      (closedSubspaceInclusion D.site D.base D.base_mem ⟨X, hX.1⟩ Z)).obj G ≅ F)
    (hrange : moduleSupport D.site D.base D.base_mem hX.1 F =
      Set.range (pointsMap D.site D.base D.base_mem Z.1.toFunctor Z.1.ι))
    (y : points D.site D.base D.base_mem Y) :
    ∑ᶠ z ∈ {z | pointsMap D.site D.base D.base_mem Z.1.toFunctor (Z.1.ι ≫ f) z = y},
        (geometricLength D.site D.base D.base_mem
          (closedSubspaceToSpace D.site D.base D.base_mem ⟨X, hX.1⟩ Z)
          (canonicalGeometricPoint D.site D.base D.base_mem Z.1.toFunctor z) G).toNat *
        residueFieldDegreeAt D.site D.base D.base_mem hY.1
          (isDecentSpace_of_isClosedSubspace D.site D.base D.base_mem
            (D.isDecentSpace_of_isGood sX hX) Z.2)
          (D.isDecentSpace_of_isGood sY hY) (Z.1.ι ≫ f) z =
      ∑ᶠ x ∈ {x | pointsMap D.site D.base D.base_mem X f x = y ∧
        x ∈ moduleSupport D.site D.base D.base_mem hX.1 F},
        (geometricLength D.site D.base D.base_mem ⟨X, hX.1⟩ (γX x) F).toNat *
          cycleResidueDegree D sX hX sY hY f x := by
  have hXdec := D.isDecentSpace_of_isGood sX hX
  have hZdec := isDecentSpace_of_isClosedSubspace D.site D.base D.base_mem hXdec Z.2
  have hgz (z) := pointsMap_comp_apply D.site D.base D.base_mem Z.1.ι f z
  refine finsum_mem_eq_of_bijOn (pointsMap D.site D.base D.base_mem Z.1.toFunctor Z.1.ι)
    ⟨fun z hz => ⟨(hgz z).symm.trans hz, hrange ▸ ⟨z, rfl⟩⟩,
      (pointsMap_injective_of_mono D.site D.base D.base_mem Z.1.ι).injOn, fun x hx => ?_⟩
    fun z _ => ?_
  · obtain ⟨z, rfl⟩ : x ∈ Set.range _ := hrange ▸ hx.2
    exact ⟨z, (hgz z).trans hx.1, rfl⟩
  · have hlen : geometricLength D.site D.base D.base_mem
          (closedSubspaceToSpace D.site D.base D.base_mem ⟨X, hX.1⟩ Z)
          (canonicalGeometricPoint D.site D.base D.base_mem Z.1.toFunctor z) G =
        geometricLength D.site D.base D.base_mem ⟨X, hX.1⟩
          (γX (pointsMap D.site D.base D.base_mem _ Z.1.ι z)) F := by
      rw [← geometricLength_modulePushforward_of_isClosedImmersion D.site D.base D.base_mem
        (closedSubspaceInclusion D.site D.base D.base_mem ⟨X, hX.1⟩ Z) Z.2.2 _ G,
        geometricLength_eq_of_iso D.site D.base D.base_mem _ _ e]
      refine geometricLength_eq_of_image_eq D.site D.base D.base_mem hX.1 _ _ ?_ F
      rw [geometricPointMap_image, canonicalGeometricPoint_image, hγX]
      rfl
    rw [hlen, residueFieldDegreeAt_comp D.site D.base D.base_mem hX.1 hY.1 hZdec hXdec
      (D.isDecentSpace_of_isGood sY hY) Z.1.ι f z,
      residueFieldDegreeAt_eq_one_of_mono D.site D.base D.base_mem hX.1 hZdec hXdec Z.1.ι z,
      one_mul]
    rfl

/-- **The length of a proper direct image over the generic point of a subspace of
δ-dimension `k`.** In Situation 0EDT let `f : X ⟶ Y` be proper over the base, let `F` be a
coherent `𝒪_X`-module with `dim_δ(Supp(F)) ≤ k` and let `W ⊂ Y` be an integral closed subspace
of δ-dimension `k` with generic point `η`. Then at a geometric point `ȳ` over `η`

`length_ȳ(f_*F) = ∑_{x ∈ Supp(F), f(x) = η} length_x(F) · [κ(x) : κ(η)]`. -/
theorem geometricLength_directImageModule_toNat_eq_finsum {f : X ⟶ Y} (hfB : f ≫ sY = sX)
    (hproper : IsProper D.site D.base D.base_mem f)
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [IsCoherent D.site D.base D.base_mem X hX.1 F] (k : ℤ)
    (hdimF : deltaDimensionClosed D sX hX (moduleSupport D.site D.base D.base_mem hX.1 F)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) ≤ (k : EInt))
    (γX : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγX : ∀ x, (γX x).LiesOver x)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) (hW : deltaDimension D sY W = k)
    (ybar : GeometricPoint D.site D.base D.base_mem Y)
    (hybar : ybar.LiesOver (W.ambientGenericPoint D.site D.base D.base_mem)) :
    (geometricLength D.site D.base D.base_mem ⟨Y, hY.1⟩ ybar
        (directImageModule D hX.1 hY.1 f F)).toNat =
      ∑ᶠ x ∈ {x | pointsMap D.site D.base D.base_mem X f x =
          W.ambientGenericPoint D.site D.base D.base_mem ∧
        x ∈ moduleSupport D.site D.base D.base_mem hX.1 F},
        (geometricLength D.site D.base D.base_mem ⟨X, hX.1⟩ (γX x) F).toNat *
          cycleResidueDegree D sX hX sY hY f x := by
  classical
  let XA : AlgebraicSpaces D.site D.base D.base_mem := ⟨X, hX.1⟩
  let YA : AlgebraicSpaces D.site D.base D.base_mem := ⟨Y, hY.1⟩
  let fA : XA ⟶ YA := ObjectProperty.homMk f
  have : F.IsQuasicoherentOnSite := inferInstance
  have hftS : SheafOfModules.IsFiniteTypeOnSite F :=
    isFiniteTypeOnSite_of_isCoherentOnSite D.site D.base D.base_mem XA F
  obtain ⟨hZ, G, hGqc, ⟨e⟩⟩ := exists_module_on_schemeTheoreticSupport D.site D.base
    D.base_mem XA F inferInstance
    (Stacks.SheafOfModules.presheafIsFiniteType_of_isFiniteTypeOnSite F hftS)
  let Zc : ClosedSubspaces D.site D.base D.base_mem X :=
    ⟨schemeTheoreticSupport D.site D.base D.base_mem XA F, hZ⟩
  let i := closedSubspaceInclusion D.site D.base D.base_mem XA Zc
  have : IsCoherent D.site D.base D.base_mem Zc.1.toFunctor Zc.2.1 G :=
    isCoherent_module_on_schemeTheoreticSupport D.site D.base D.base_mem XA
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) F hZ G hGqc e
  have hrange : moduleSupport D.site D.base D.base_mem hX.1 F =
      Set.range (pointsMap D.site D.base D.base_mem Zc.1.toFunctor Zc.1.ι) :=
    supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport D.site D.base D.base_mem XA F
      inferInstance hftS
  let e2 : directImageModule D hX.1 hY.1 f F ≅
      (modulePushforward D.site D.base D.base_mem (i ≫ fA)).obj G :=
    (modulePushforward D.site D.base D.base_mem fA).mapIso e.symm ≪≫
      ((modulePushforwardCompIso D.site D.base D.base_mem i fA).app G :
        (modulePushforward D.site D.base D.base_mem fA).obj
          ((modulePushforward D.site D.base D.base_mem i).obj G) ≅ _)
  rw [geometricLength_eq_of_iso D.site D.base D.base_mem YA ybar e2]
  exact (geometricLength_modulePushforward_comp_closedSubspace_toNat_eq_finsum D sX hX sY hY hfB
    hproper F k hdimF γX hγX W hW ybar hybar Zc G hrange).trans
    (finsum_closedSubspace_fibre_eq_finsum_moduleSupport_fibre D sX hX sY hY f F γX hγX Zc G e
      hrange _)

end Chow

end AlgebraicGeometry.Space

end
