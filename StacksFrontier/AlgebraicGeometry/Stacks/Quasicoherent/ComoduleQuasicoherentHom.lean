module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ComoduleSubsheafCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfCartesianQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatObjectCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LowerShriekQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfHomQuasiCompactStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentModulesAbelian

/-!
# A quasi-coherent module mapping onto `ℱ ∩ u_*H` over a flat object

Let `𝒳` be a quasi-separated algebraic stack, `ℱ` a quasi-coherent `𝒪_𝒳`-module, `u` a flat
object of `𝒳` over an affine scheme and `H ⊆ ℱ(u)` a submodule.  The subsheaf `ℱ ∩ u_*H` of
`AlgebraicGeometry.FibredSite.comoduleSubsheaf` is not quasi-coherent on `𝒳`, but its restriction
`ℋ` to the flat-fppf site is: quasi-separatedness gives every object over an affine scheme a
universal pair with `u` (the hom-set form of Stacks 0GMS (2)(c)), so `ℱ ∩ u_*H` is cartesian along
flat arrows between affine objects, hence `ℋ` is cartesian between flat affine objects and is
quasi-coherent there.  Then `g_!ℋ` is quasi-coherent on `𝒳` (Stacks 07B0 (2)) and the counit
`g_!ℋ ⟶ ℱ ∩ u_*H ⟶ ℱ` is, over every flat object, the inclusion of `ℱ ∩ u_*H`
(`g^{-1}g_! = id`, Stacks 0789 (2)).

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_quasicoherent_hom_range_eq_comoduleSubmodule`

## References

* [Stacks Project, Tag 07B0](https://stacks.math.columbia.edu/tag/07B0)
* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
* [Stacks Project, Tag 0GMS](https://stacks.math.columbia.edu/tag/0GMS)
* [Stacks Project, Tag 0GRF](https://stacks.math.columbia.edu/tag/0GRF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.FibredSite

universe u w w'

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS}

attribute [local instance] objModule

/-- **Universal pairs on a quasi-separated algebraic stack.** -/
theorem exists_isUniversalPair_of_isQuasiSeparatedAbs
    (h𝒳 : IsQuasiSeparatedAbs.{u, w, w'} B S hS 𝒳) {x u : 𝒳.val.val.obj}
    (hx : IsAffineOver B S hS (𝒳.val.val.p.obj x)) (hu : IsAffineOver B S hS (𝒳.val.val.p.obj u)) :
    ∃ (v : 𝒳.val.val.obj) (pr₁ : v ⟶ x) (pr₂ : v ⟶ u), IsAffineOver B S hS (𝒳.val.val.p.obj v) ∧
      IsUniversalPair B S hS 𝒳.val.val.p pr₁ pr₂ := by
  obtain ⟨v, hv, pr₁, pr₂, h⟩ :=
    exists_affineObject_exists_covering_hom_pair_of_isQuasiSeparatedAbs.{u, w, w'} B S hS 𝒳 h𝒳
      x hx u hu
  refine ⟨v, pr₁, pr₂, hv, fun z c b _ => ?_⟩
  obtain ⟨T, hT, hfac⟩ := h z c b
  exact ⟨T, hT, fun z' g hg _ => hfac g hg⟩

variable (𝒳) in
/-- **The comodule subsheaf is cartesian along flat arrows between affine objects**, on a
quasi-separated algebraic stack. -/
theorem isIso_restrictionBaseChange_comoduleSubsheaf
    (h𝒳 : IsQuasiSeparatedAbs.{u, w, w'} B S hS 𝒳)
    (F : AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModules B S hS 𝒳)
    {u : 𝒳.val.val.obj} (hu : IsAffineOver B S hS (𝒳.val.val.p.obj u))
    (H : Submodule (objRing B S hS 𝒳.val.val.p u) (F.obj.val.obj (op u)))
    ⦃z x : 𝒳.val.val.obj⦄ (φ : z ⟶ x)
    (hφ : Flat (B.inclusion.map (𝒳.val.val.p.map φ).left))
    (hz : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj z))
    (hx : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj x)) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (AlgebraicGeometry.Stack.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        (etaleTopology B) (etaleTopology_le_topology B)).obj)
      (comoduleSubsheaf F.obj H F.property).toSheafOfModules.val φ.op) := by
  obtain ⟨v, pr₁, pr₂, hv, hpr⟩ := exists_isUniversalPair_of_isQuasiSeparatedAbs h𝒳 hx hu
  have hflat : Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map φ)) := hφ
  have hR : ((AlgebraicGeometry.Stack.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (etaleTopology B) (etaleTopology_le_topology B)).obj.map φ.op).hom.Flat := by
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)) := hx
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj z)) := hz
    show RingHom.Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map φ)).appTop.hom
    exact HasRingHomProperty.appTop (P := @Flat) _ hflat
  exact Stacks.PresheafOfModules.isIso_restrictionBaseChange_submodule
    (R := (AlgebraicGeometry.Stack.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        (etaleTopology B) (etaleTopology_le_topology B)).obj) F.obj.val
    (comoduleSubsheaf F.obj H F.property).toSubmodule φ.op hR
    (isIso_restrictionBaseChange_of_isQuasicoherentOnSite F.obj F.property φ hz hx)
    (comoduleSubmodule_le_span F.obj H F.property φ hflat hx hz hv hpr)

/-- An isomorphism of sheaves of modules is bijective on sections. -/
theorem bijective_val_app_of_isIso {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R} (f : M ⟶ N) (hf : IsIso f)
    (X : Cᵒᵖ) : Function.Bijective (f.val.app X) := by
  have h₁ : IsIso ((SheafOfModules.forget _).map f) := Functor.map_isIso _ _
  have h₂ : IsIso ((PresheafOfModules.evaluation _ X).map ((SheafOfModules.forget _).map f)) :=
    Functor.map_isIso _ _
  exact (ConcreteCategory.isIso_iff_bijective _).1 h₂

variable (𝒳) in
/-- **A quasi-coherent module mapping onto `ℱ ∩ u_*H` over a flat object `u`.**  On a
quasi-separated algebraic stack, for a flat object `u` over an affine scheme and a submodule
`H ⊆ ℱ(u)` of the sections of a quasi-coherent module `ℱ`, there is a map `𝒫 ⟶ ℱ` of
quasi-coherent modules whose image on the sections over `u` is `(ℱ ∩ u_*H)(u)`, and which is
injective on the sections over `u`. -/
theorem exists_quasicoherent_hom_range_eq_comoduleSubmodule
    (h𝒳 : IsQuasiSeparatedAbs.{u, w, w'} B S hS 𝒳)
    (F : AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModules B S hS 𝒳)
    {u : 𝒳.val.val.obj} (hu : IsAffineOver B S hS (𝒳.val.val.p.obj u))
    (hflat : flatObject B S hS 𝒳.val u)
    (H : Submodule (objRing B S hS 𝒳.val.val.p u) (F.obj.val.obj (op u))) :
    ∃ (P : AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModules B S hS 𝒳) (φ : P ⟶ F),
      Set.range (φ.hom.val.app (op u)) = comoduleSubmodule F.obj H u ∧
        Function.Injective (φ.hom.val.app (op u)) := by
  let N := comoduleSubsheaf F.obj H F.property
  let G := N.toSheafOfModules
  let H' := (FlatFppf.modulePullback B S hS 𝒳).obj G
  have hH' : H'.IsQuasicoherentOnSite :=
    FlatFppf.isQuasicoherentOnSite_of_isIso_restrictionBaseChange_affine B S hS 𝒳 H'
      fun y y' f hy hy' => FlatFppf.isIso_restrictionBaseChange_modulePullback B S hS G
        (isIso_restrictionBaseChange_comoduleSubsheaf 𝒳 h𝒳 F hu H) f hy hy'
  let adj := FlatFppf.moduleLowerShriekAdjunction B S hS 𝒳
  let ε := adj.counit.app G
  refine ⟨⟨(FlatFppf.moduleLowerShriek B S hS 𝒳).obj H',
    FlatFppf.isQuasicoherentOnSite_moduleLowerShriek_of_isQuasicoherentOnSite B S hS 𝒳 H' hH'⟩,
    ObjectProperty.homMk (ε ≫ N.ι), ?_⟩
  have hunit : IsIso (adj.unit.app ((FlatFppf.modulePullback B S hS 𝒳).obj G)) := by
    have := FlatFppf.isIso_moduleLowerShriekAdjunction_unit B S hS 𝒳
    infer_instance
  have hpb : IsIso ((FlatFppf.modulePullback B S hS 𝒳).map ε) := by
    have : IsIso (adj.unit.app ((FlatFppf.modulePullback B S hS 𝒳).obj G) ≫
        (FlatFppf.modulePullback B S hS 𝒳).map ε) := by
      rw [adj.right_triangle_components G]
      infer_instance
    exact IsIso.of_isIso_comp_left (adj.unit.app _) _
  let := FlatFppf.isContinuous_inclusion' B S hS 𝒳
  let := FlatFppf.isCocontinuous_inclusion' B S hS 𝒳
  let e := subsiteModulePullbackIsoRestriction B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    B.topology le_rfl (FlatFppf.objectProperty B S hS 𝒳)
  have hb : Function.Bijective (ε.val.app (op u)) :=
    bijective_val_app_of_isIso _ ((NatIso.isIso_map_iff e ε).1 hpb)
      (op (⟨u, hflat⟩ : FlatFppf B S hS 𝒳))
  show Set.range (fun y => (ε.val.app (op u) y).1) = _ ∧
    Function.Injective (fun y => (ε.val.app (op u) y).1)
  refine ⟨Set.ext fun x => ⟨?_, fun hx => ?_⟩, fun y y' h => hb.1 (Subtype.ext h)⟩
  · rintro ⟨y, rfl⟩
    exact (ε.val.app (op u) y).2
  · obtain ⟨y, hy⟩ := hb.2 ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
