module

public import StacksFrontier.AlgebraicGeometry.Spaces.IdealAnnihilatorSubsheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.AffineSiteBaseChangeAcyclic
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianModulesSheafAnyUniverse
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.TildePullback
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftBaseChangeAcyclic
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftCartesian

/-!
# Cartesian modules on a site of affine schemes with its rings raised to the module universe

Let `L : C ⥤ Scheme` be a functor with affine values, preserving fibre products, on a category
with fibre products, and let `J` be a topology on `C` which is flatly cofinal for `L`
(`Stacks.AffineSiteBaseChange.IsFlatCofinal`): every covering sieve contains a finite family
which `L` carries to a flat covering. This file proves, for the global functions `Γ ∘ L` and
more generally for a structure sheaf `O` related to them by a ring transport over the identity
of `C` (a family of ring isomorphisms `O(U) ≃+* Γ(L U)`, as when the rings `Γ(L U)` are raised to
a larger universe), the three inputs under which the subcategory of Stacks 0GZS is the
subcategory of objects with cartesian cohomology sheaves
(`ChaoticComparison.isCartesianPushforward_iff_isCartesianPresheaf_homology`, in the namespace
`Stacks.ModulesOnACategory`):
the restriction maps of `O` are flat, cartesian presheaves of `O`-modules are sheaves, and
sheaves of `O`-modules with cartesian underlying presheaf have no higher cohomology.

## Main results

* `Stacks.AffineSiteBaseChange.IsFlatCofinal.inducedTopology`: flat cofinality is transported
  along an equivalence of categories.
* `Stacks.AffineSiteBaseChange.isSheaf_of_isCartesianPresheaf`: a cartesian presheaf of modules
  over `Γ ∘ L` is a sheaf.
* `Stacks.AffineSiteBaseChange.isSheaf_baseChangePresheaf`: the base change `N ⊗_{O(x)} O_x` is a
  sheaf on the slice at `x`.
* `Stacks.AffineSiteBaseChange.isCartesianPushforward_iff_of_ringTransport`: on a ringed site in
  a single universe whose structure sheaf is related to `Γ ∘ L` by a ring transport over the
  identity, an object of the derived category lies in the subcategory of Stacks 0GZS exactly
  when its cohomology sheaves are cartesian; it is assembled from
  `Stacks.AffineSiteBaseChange.flat_ringSheaf_map_of_ringTransport`,
  `Stacks.AffineSiteBaseChange.isSheaf_of_isCartesianPresheaf_of_ringTransport` and
  `Stacks.AffineSiteBaseChange.isZero_rightDerived_evaluation_of_ringTransport`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public section

-- The ambient-universe instances on sheaves of modules state their module universe as a `max`
-- pattern which the module universes below do not match syntactically; instance search against
-- them leaves stuck universe constraints. The same instances are supplied at explicit universes.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

open CategoryTheory CategoryTheory.Limits Opposite

universe t u v w u' v'

namespace Stacks.AffineSiteBaseChange

open _root_.AlgebraicGeometry
open Stacks.ModulesOnACategory.ChaoticComparison
  (isCartesianPresheaf_iff_isIso_restrictionBaseChange)

variable {C : Type v} [Category.{w} C] {L : C ⥤ _root_.AlgebraicGeometry.Scheme.{u}}
  {J : GrothendieckTopology C}

/-- **Flat cofinality is transported along an equivalence.** If `J` is flatly cofinal for `L`
and `e : C ≌ D` is an equivalence, then the topology induced on `D` along `e⁻¹` is flatly
cofinal for `e⁻¹ ⋙ L`: a finite flat covering family of `e⁻¹ y` inside the image of a covering
sieve is carried to `D` by `e` followed by the counit. -/
theorem IsFlatCofinal.inducedTopology (hJ : IsFlatCofinal L J) {D : Type u'} [Category.{v'} D]
    (e : C ≌ D) : IsFlatCofinal (e.inverse ⋙ L) (e.inverse.inducedTopology J) := by
  intro y S hS
  have hS' : S.functorPushforward e.inverse ∈ J (e.inverse.obj y) :=
    (Functor.functorPushforward_mem_iff (e.inverse.inducedTopology J) J e.inverse).2 hS
  obtain ⟨E, hfin, hE, hES, hEJ⟩ := hJ _ _ hS'
  obtain ⟨hcov, hfl⟩ := (Scheme.presieve₀_mem_precoverage_iff (E.map L)).1 hE
  -- the arrows `e (E.f i) ≫ ε_y`, read in `C`, are those of `E` up to the unit
  have hunit : ∀ i, e.unit.app (E.X i) ≫ e.inverse.map (e.functor.map (E.f i) ≫ e.counit.app y) =
      E.f i := fun i => by
    rw [Functor.map_comp, ← Category.assoc,
      show e.unit.app (E.X i) ≫ e.inverse.map (e.functor.map (E.f i)) =
        E.f i ≫ e.unit.app _ from (e.unit.naturality (E.f i)).symm,
      Category.assoc, e.unit_inverse_comp, Category.comp_id]
  have hL : ∀ i : E.I₀, L.map (e.unit.app (E.X i)) ≫
      L.map (e.inverse.map (e.functor.map (E.f i) ≫ e.counit.app y)) = L.map (E.f i) :=
    fun i => by rw [← L.map_comp, hunit]
  refine ⟨⟨E.I₀, fun i => e.functor.obj (E.X i), fun i => e.functor.map (E.f i) ≫ e.counit.app y⟩,
    hfin, ?_, ?_, ?_⟩
  · refine (Scheme.presieve₀_mem_precoverage_iff _).2 ⟨fun x => ?_, fun (i : E.I₀) => ?_⟩
    · obtain ⟨i, z, hz⟩ := hcov x
      refine ⟨i, L.map (e.unit.app (E.X i)) z, ?_⟩
      have hz' : (L.map (E.f i)) z = x := hz
      rw [← hz', ← hL i]
      rfl
    · have hi : L.map (e.inverse.map (e.functor.map (E.f i) ≫ e.counit.app y)) =
          inv (L.map (e.unit.app (E.X i))) ≫ L.map (E.f i) := by
        rw [IsIso.eq_inv_comp, hL]
      have : Flat (L.map (E.f i)) := hfl i
      show Flat (L.map (e.inverse.map (e.functor.map (E.f i) ≫ e.counit.app y)))
      rw [hi]
      infer_instance
  · rw [PreZeroHypercover.sieve₀, Sieve.generate_le_iff]
    rintro W g ⟨i⟩
    obtain ⟨Z, s, g', hs, hg'⟩ := hES _ (Sieve.le_generate _ _ _ ⟨i⟩)
    have : e.functor.map (E.f i) ≫ e.counit.app y = e.functor.map g' ≫ e.counit.app Z ≫ s := by
      rw [hg', Functor.map_comp, Category.assoc]
      congr 1
      exact e.counit.naturality s
    show S.arrows (e.functor.map (E.f i) ≫ e.counit.app y)
    rw [this, ← Category.assoc]
    exact S.downward_closed hs _
  · refine (Functor.functorPushforward_mem_iff (e.inverse.inducedTopology J) J e.inverse).1 ?_
    refine J.superset_covering ?_ hEJ
    rw [PreZeroHypercover.sieve₀, Sieve.generate_le_iff]
    rintro W g ⟨i⟩
    exact ⟨_, e.functor.map (E.f i) ≫ e.counit.app y, e.unit.app (E.X i),
      Sieve.le_generate _ _ _ ⟨i⟩, (hunit i).symm⟩

/-- The opposite of a functor with affine values has affine values. -/
private theorem isAffine_unop_op_obj [∀ X, IsAffine (L.obj X)] :
    ∀ Y : Cᵒᵖ, IsAffine (unop (L.op.obj Y)) := fun Y =>
  (inferInstance : IsAffine (L.obj Y.unop))

/-- **On a flatly cofinal site of affine schemes, a cartesian presheaf of modules over the
global functions is a sheaf**, at any universe of module sections: the topology is refined by
finite flat coverings of affine schemes, along which a cartesian presheaf of modules satisfies
descent (`Stacks.PresheafOfModules.isSheaf_of_cartesian_of_flat_refinements'`). -/
theorem isSheaf_of_isCartesianPresheaf [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan L]
    [∀ X, IsAffine (L.obj X)] (hJ : IsFlatCofinal L J)
    (P : PresheafOfModules.{max t u} (rings L ⋙ forget₂ CommRingCat RingCat))
    (hP : Stacks.ModulesOnACategory.ChaoticComparison.IsCartesianPresheaf P) :
    Presheaf.IsSheaf J P.presheaf := by
  have := isAffine_unop_op_obj (L := L)
  refine Stacks.PresheafOfModules.isSheaf_of_cartesian_of_flat_refinements'.{u, v, u, t, w, 0}
    L (rings L) ?_ ?_ P
    (fun f => (isCartesianPresheaf_iff_isIso_restrictionBaseChange P).1 hP f) J ?_
  · intro U E hfin hE
    obtain ⟨hcover, hflat⟩ := (Scheme.presieve₀_mem_precoverage_iff _).mp hE
    let _ (i : E.I₀) : Flat (L.map (E.f i)) := hflat i
    exact Scheme.faithfullyFlat_pi_appTop (fun i => L.obj (E.X i)) (fun i => L.map (E.f i))
      (fun y => by
        obtain ⟨i, hi⟩ := hcover y
        exact ⟨i, hi⟩)
  · intro _ _ _ _ _ _ _ _ h
    exact isPushout_appTop_of_isPullback (Functor.map_isPullback L h)
  · intro V S hS
    obtain ⟨E, hfin, hE, hES, -⟩ := hJ V S hS
    exact ⟨E, hfin, hE, hES⟩

open Stacks.TerminalBaseChange Stacks.Sites.OverModules in
/-- **On a flatly cofinal site of affine schemes, the base change `N ⊗_{O(x)} O_x` is a sheaf on
the slice at `x`**, for every `O(x)`-module `N` of any universe: it is cartesian
(`Stacks.AffineSiteBaseChange.isIso_restrictionBaseChange_baseChangePresheaf`), and the slice is
again flatly cofinal (`Stacks.AffineSiteBaseChange.IsFlatCofinal.over`). -/
theorem isSheaf_baseChangePresheaf [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan L]
    [∀ X, IsAffine (L.obj X)] (hJ : IsFlatCofinal L J) (x : C)
    (N : ModuleCat.{max t u}
      ((overRingPresheaf (rings L ⋙ forget₂ CommRingCat RingCat) x).obj (op (Over.mk (𝟙 x))))) :
    Presheaf.IsSheaf (J.over x)
      ((baseChangePresheaf.{t} (overRingPresheaf (rings L ⋙ forget₂ CommRingCat RingCat) x)
        (Over.mkIdTerminal (X := x))).obj N).presheaf := by
  have : PreservesLimitsOfShape WalkingCospan (Over.forget x ⋙ L) := by
    apply comp_preservesLimitsOfShape
  have : ∀ Y : Over x, IsAffine ((Over.forget x ⋙ L).obj Y) := fun Y =>
    (inferInstance : IsAffine (L.obj Y.left))
  exact isSheaf_of_isCartesianPresheaf.{t} (L := Over.forget x ⋙ L) (hJ.over x) _
    ((isCartesianPresheaf_iff_isIso_restrictionBaseChange _).2
      (fun _ _ f => isIso_restrictionBaseChange_baseChangePresheaf.{t} _ _ N f))


end Stacks.AffineSiteBaseChange

namespace Stacks.AffineSiteBaseChange

open _root_.AlgebraicGeometry Stacks.TerminalBaseChange Stacks.Sites.OverModules
  Stacks.UniverseLift Stacks.ModulesOnACategory.ChaoticComparison
  Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange

section RingTransport

variable (Z : RingedSite.{max u w, max u w, max u w}) (L : Z.C ⥤ Scheme.{u})
  [HasPullbacks Z.C] [PreservesLimitsOfShape WalkingCospan L] [∀ X, IsAffine (L.obj X)]
  (hJ : IsFlatCofinal L Z.J)
  (T : RingTransport (CategoryTheory.Equivalence.refl : Z.C ≌ Z.C)
    (rings L ⋙ forget₂ CommRingCat RingCat) (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj)

omit [HasPullbacks Z.C] [PreservesLimitsOfShape WalkingCospan L] [∀ X, IsAffine (L.obj X)] in
/-- The sections of the global functions of `L` commute. -/
theorem mul_comm_rings (V : Z.Cᵒᵖ) (a b : (rings L ⋙ forget₂ CommRingCat RingCat).obj V) :
    a * b = b * a := by
  let _ : CommRing ((rings L ⋙ forget₂ CommRingCat RingCat).obj V) :=
    inferInstanceAs (CommRing ((rings L).obj V))
  exact mul_comm a b

include T in
/-- **The restriction maps of the structure sheaf are flat** when `L` carries every morphism to a
flat morphism of schemes: they are the restriction maps of `Γ ∘ L`, read through the ring
isomorphisms of the ring transport. -/
theorem flat_ringSheaf_map_of_ringTransport (hL : ∀ {X Y : Z.C} (f : X ⟶ Y), Flat (L.map f))
    ⦃U V : Z.Cᵒᵖ⦄ (a : V ⟶ U) :
    letI := Stacks.ModulesOnACategory.TildePullback.commSections_ringSheaf Z
    RingHom.Flat ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj.map a).hom := by
  let := Stacks.ModulesOnACategory.TildePullback.commSections_ringSheaf Z
  have hφ : RingHom.Flat ((rings L).map a).hom := by
    have := isAffine_unop_op_obj (L := L)
    have := hL a.unop
    exact HasRingHomProperty.appTop (P := @Flat) _ this
  have h : ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj.map a).hom =
      (T.iso U).symm.toRingHom.comp (((rings L).map a).hom.comp (T.iso V).toRingHom) := by
    ext x
    exact ((T.iso U).symm_apply_apply _).symm.trans (congrArg (T.iso U).symm (T.naturality a x))
  rw [h]
  exact RingHom.Flat.comp (RingHom.Flat.comp (RingHom.Flat.of_bijective (T.iso V).bijective) hφ)
    (RingHom.Flat.of_bijective (T.iso U).symm.bijective)

/-- The base changes on the slices are sheaves for the global functions of `L`. -/
private theorem baseChangeIsSheaf_ringsSheaf :
    BaseChangeIsSheaf.{max u w} (ringsSheaf hJ) (mul_comm_rings Z L) := fun x N =>
  isSheaf_baseChangePresheaf.{max u w} hJ x N

include hJ T in
/-- **A cartesian presheaf of modules over the structure sheaf is a sheaf.** Read over `Γ ∘ L`
through the ring transport, it is a cartesian presheaf of modules over the global functions of a
flatly cofinal site of affine schemes
(`Stacks.AffineSiteBaseChange.isSheaf_of_isCartesianPresheaf`). -/
theorem isSheaf_of_isCartesianPresheaf_of_ringTransport
    (P : PresheafOfModules.{max u w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj)
    (hP : IsCartesianPresheaf P) :
    Presheaf.IsSheaf Z.J P.presheaf := by
  have h₀ := isSheaf_of_isCartesianPresheaf.{max u w} hJ (T.symm.functor.obj P)
    (T.symm.isCartesianPresheaf_functor_obj hP)
  have h₁ := T.isSheaf_functor_obj (R := ringsSheaf hJ)
    (R' := (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (T.symm.functor.obj P) h₀
  exact (Presheaf.isSheaf_of_iso_iff ((PresheafOfModules.toPresheaf _).mapIso
    (T.counitIso.app P))).1 h₁

include hJ T in
/-- **The base changes on the slices are sheaves**: for every object `x` and every
`O(x)`-module `N`, the base change `N ⊗_{O(x)} O_x` is a sheaf on the slice at `x`. This is
`Stacks.AffineSiteBaseChange.isSheaf_baseChangePresheaf` for `Γ ∘ L`, transported along the ring
transport. -/
theorem baseChangeIsSheaf_of_ringTransport :
    BaseChangeIsSheaf.{max u w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
      (RingedSite.mul_comm_ringSheaf Z) :=
  T.baseChangeIsSheaf (R := ringsSheaf hJ) (R' := (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
    (mul_comm_rings Z L) (RingedSite.mul_comm_ringSheaf Z) (baseChangeIsSheaf_ringsSheaf Z L hJ)

/-- **The base changes on the slices have no higher cohomology**: for every object `x`, every
`O(x)`-module `N`, every object of the slice at `x` and every `p > 0`, the `p`-th cohomology of
`N ⊗_{O(x)} O_x` over that object vanishes. This is
`Stacks.AffineSiteBaseChange.isZero_rightDerived_evaluation_baseChange` for `Γ ∘ L`, transported
along the ring transport. -/
theorem baseChangeAcyclic_of_ringTransport :
    letI (y : Z.C) := Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{max u w,
      max u w, max u w, max u w} (overRingSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) y)
    BaseChangeAcyclic.{max u w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
      (RingedSite.mul_comm_ringSheaf Z) (baseChangeIsSheaf_of_ringTransport.{u, w} Z L hJ T) := by
  let (y : Z.C) := Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{max u w,
    max u w, max u w, max u w} (overRingSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) y)
  let (y : Z.C) := Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{max u w,
    max u w, u, max u w} (overRingSheaf (ringsSheaf hJ) y)
  have hsh := baseChangeIsSheaf_ringsSheaf Z L hJ
  exact T.baseChangeAcyclic (R := ringsSheaf hJ)
    (R' := (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (mul_comm_rings Z L)
    (RingedSite.mul_comm_ringSheaf Z) hsh
    fun x N V p hp => isZero_rightDerived_evaluation_baseChange.{max u w} hJ x N (hsh x N) V p hp

include hJ T in
/-- **A sheaf of modules with cartesian underlying presheaf has no higher cohomology over any
object.** Its restriction to the slice at an object is the base change of its sections there
(`ChaoticComparison.isZero_rightDerived_evaluation_of_isCartesianPresheaf`),
and those base changes are acyclic
(`Stacks.AffineSiteBaseChange.baseChangeAcyclic_of_ringTransport`). -/
theorem isZero_rightDerived_evaluation_of_ringTransport
    (G : SheafOfModules.{max u w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
    (hG : IsCartesianPresheaf G.val) (U : Z.C) (p : ℕ) (hp : 0 < p) :
    letI := Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{max u w, max u w,
      max u w, max u w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
    IsZero (((_root_.SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
      (op U)).rightDerived p).obj G) := by
  let (y : Z.C) := Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{max u w,
    max u w, max u w, max u w} (overRingSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) y)
  let := Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{max u w, max u w,
    max u w, max u w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
  exact isZero_rightDerived_evaluation_of_isCartesianPresheaf.{max u w}
    (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) (RingedSite.mul_comm_ringSheaf Z)
    (baseChangeIsSheaf_of_ringTransport.{u, w} Z L hJ T)
    (baseChangeAcyclic_of_ringTransport.{u, w} Z L hJ T) G hG U p hp

include hJ T in
/-- **The subcategory of Stacks 0GZS is the subcategory of objects with cartesian cohomology
sheaves.** If `L` carries every morphism to a flat morphism of schemes, an object `K` of the
derived category of sheaves of modules has `Rε_*K` cartesian exactly when every cohomology sheaf
of `K` is cartesian: this is
`ChaoticComparison.isCartesianPushforward_iff_isCartesianPresheaf_homology`
with its three inputs supplied by `flat_ringSheaf_map_of_ringTransport`,
`isSheaf_of_isCartesianPresheaf_of_ringTransport` and
`isZero_rightDerived_evaluation_of_ringTransport`. -/
theorem isCartesianPushforward_iff_of_ringTransport
    (hL : ∀ {X Y : Z.C} (f : X ⟶ Y), Flat (L.map f))
    (K : DerivedCategory (SheafOfModules.{max u w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))) :
    letI := Stacks.ModulesOnACategory.TildePullback.commSections_ringSheaf Z
    IsCartesianPushforward.{max u w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
        (baseChangeDataOfComm.{max u w, max u w, max u w, max u w}
          (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj CommSections.mul_comm) K ↔
      DerivedCategoryB.derivedCategoryB
        (cartesianSheaves.{max u w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) K := by
  let := Stacks.ModulesOnACategory.TildePullback.commSections_ringSheaf Z
  let := Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{max u w, max u w,
      max u w, max u w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
  exact isCartesianPushforward_iff_isCartesianPresheaf_homology.{max u w}
    (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
    (flat_ringSheaf_map_of_ringTransport.{u, w} Z L T hL) _
    (isSheaf_of_isCartesianPresheaf_of_ringTransport.{u, w} Z L hJ T)
    (isZero_rightDerived_evaluation_of_ringTransport.{u, w} Z L hJ T) K

end RingTransport

end Stacks.AffineSiteBaseChange

end
