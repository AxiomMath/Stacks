module

public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.RingTheory.FreeRing
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSite
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtaleSite
public import StacksFrontier.CategoryTheory.FiberedCategory.Inertia
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Equivalence
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Functoriality

/-!
# The structure sheaf of a category fibred in groupoids (Stacks 06TV)

Let `p : 𝒳 ⥤ (Sch/S)` be a category fibred in groupoids over the big fppf category of a scheme
`S`, and let `τ` be a topology on the underlying category of schemes which is coarser than the
site's own fppf topology. The structure sheaf of the associated site of Tag 06TP is the inverse
image along `p` of the structure sheaf of the site of schemes.

The inverse image along the structure functor is restriction of the base sheaf: its presheaf
evaluates at an object of the fibred category as the ring of global functions on the underlying
scheme. The base sheaf is the fppf structure sheaf of Tag 03DU restricted to `τ`, which is a
sheaf because `τ` is coarser. Restriction along `p` preserves the sheaf condition because `p` is
a 1-morphism of fibred categories to the identity fibred category, hence continuous for the
inherited topologies (Tag 06NW). The construction exposes the restricted presheaf directly, so
its values and restriction maps are available without sheafification.

## Implementation notes

The source states this for each of the five standard topologies — Zariski, étale, smooth, syntomic,
fppf. Here `τ` is an arbitrary topology on the underlying category of schemes with
`hτ : τ ≤ B.topology`, the only property of the five that the construction uses, as in
`AlgebraicGeometry.Stack.associatedTopology` (Tag 06TP). Each standard topology is an instance:
`AlgebraicGeometry.Stack.etaleTopology_le_topology` proves the inequality for the étale topology,
and each of the other four is a `CategoryTheory.Precoverage` of selected families cut out of the
site's own by a condition on the morphisms, for which the inequality is proved the same way.

## Main definitions

* `AlgebraicGeometry.Stack.baseStructureSheaf`: the base commutative ring sheaf.
* `AlgebraicGeometry.Stack.structureSheaf`: the commutative structure sheaf on an associated site.
* `AlgebraicGeometry.Stack.ringStructureSheafCore`: its underlying sheaf of rings.
* `AlgebraicGeometry.Stack.ringStructureSheaf`: the same with its rings lifted to a universe
  containing the site.

## References

* [Stacks Project, Tag 06TV](https://stacks.math.columbia.edu/tag/06TV)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u v w r

namespace AlgebraicGeometry.Stack

/-- The forgetful functor of rings is represented by the free ring on one generator. -/
noncomputable def ringForgetIsoCoyoneda :
    coyoneda.obj (Opposite.op (RingCat.of (FreeRing PUnit.{u + 1}))) ≅ forget RingCat.{u} :=
  NatIso.ofComponents (fun R => Equiv.toIso
    { toFun := fun f => f.hom (FreeRing.of PUnit.unit)
      invFun := fun x => RingCat.ofHom (FreeRing.lift (fun _ => x))
      left_inv := fun _ => RingCat.hom_ext <| FreeRing.hom_ext fun _ => FreeRing.lift_of _ _
      right_inv := fun x => FreeRing.lift_of _ _ })
    (by intro R T f; ext x; rfl)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A topology coarser than the site's fppf topology stays coarser after localizing at `S`. -/
theorem over_le_over {τ : GrothendieckTopology B.Schemes} (hτ : τ ≤ B.topology) :
    τ.over (B.obj hS) ≤ B.topology.over (B.obj hS) := by
  intro X R hR
  rw [GrothendieckTopology.mem_over_iff] at hR ⊢
  exact hτ _ hR

/-- The big étale topology on the underlying category of schemes is coarser than the fppf one:
a selected étale covering family is in particular a selected family. -/
theorem etaleTopology_le_topology : etaleTopology B ≤ B.topology := by
  apply Precoverage.toGrothendieck_mono
  intro X R hR
  obtain ⟨E, rfl, hE⟩ := hR
  exact ⟨E, rfl, hE.1⟩

/-- The structure sheaf of the big site of schemes over `S`, for any topology coarser than the
fppf one, obtained by restricting the fppf structure sheaf of Tag 03DU. -/
noncomputable def baseStructureSheaf (τ : GrothendieckTopology B.Schemes)
    (hτ : τ ≤ B.topology) :
    Sheaf (τ.over (B.obj hS)) CommRingCat.{u} :=
  ⟨(BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ,
    Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ CommRingCat RingCat)
      ((BigFppfOver.structureSheaf B S hS).property.of_le (over_le_over B S hS hτ))⟩

/-- The presheaf of `baseStructureSheaf` sends an object to the global sections of its underlying
scheme. -/
@[simp]
theorem baseStructureSheaf_obj (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) :
    (baseStructureSheaf B S hS τ hτ).obj =
      (BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ := rfl

/-- The structure sheaf of a category fibred in groupoids, given by inverse image of the
commutative ring sheaf of the big site of schemes. -/
@[stacks 06TV]
noncomputable def structureSheaf {X : Type v} [Category.{w} X]
    (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) :
    Sheaf (associatedTopology B S hS p τ) CommRingCat.{u} := by
  let J := τ.over (B.obj hS)
  have hId : (𝟭 (BigFppfOver B S hS)).inheritedTopology J ≤ J :=
    Precoverage.toGrothendieck_le_iff_le_toPrecoverage.2 fun _ _ hR => by simpa using hR.2
  let Oid : Sheaf ((𝟭 (BigFppfOver B S hS)).inheritedTopology J) CommRingCat.{u} :=
    ⟨(baseStructureSheaf B S hS τ hτ).obj,
      (baseStructureSheaf B S hS τ hτ).property.of_le hId⟩
  letI : p.IsFibered := hp.isFibered
  letI : (𝟭 (BigFppfOver B S hS)).IsFibered :=
    Functor.isFiberedInGroupoids_id.isFibered
  letI := ((Functor.isFibredOneMorphism_id p).isContinuous_and_isCocontinuous_inheritedTopology
    J).1
  exact ⟨p.op ⋙ Oid.obj, p.op_comp_isSheaf _ _ Oid⟩

/-- The presheaf of `structureSheaf` sends an object of the fibred category to the global sections
of the underlying scheme of its image under `p`. -/
@[simp]
theorem structureSheaf_obj {X : Type v} [Category.{w} X]
    (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) :
    (structureSheaf B S hS p hp τ hτ).obj =
      p.op ⋙ (BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ := rfl

/-- The underlying sheaf of rings of `AlgebraicGeometry.Stack.baseStructureSheaf`. -/
noncomputable def baseRingStructureSheaf (τ : GrothendieckTopology B.Schemes)
    (hτ : τ ≤ B.topology) :
    Sheaf (τ.over (B.obj hS)) RingCat.{u} :=
  ⟨(baseStructureSheaf B S hS τ hτ).obj ⋙ forget₂ CommRingCat RingCat,
    (BigFppfOver.structureSheaf B S hS).property.of_le (over_le_over B S hS hτ)⟩

/-- The presheaf of `baseRingStructureSheaf` is that of the fppf structure sheaf. -/
@[simp]
theorem baseRingStructureSheaf_obj (τ : GrothendieckTopology B.Schemes)
    (hτ : τ ≤ B.topology) :
    (baseRingStructureSheaf B S hS τ hτ).obj =
      (BigFppfOver.structureSheaf B S hS).obj := rfl

/-- The underlying sheaf of rings of `AlgebraicGeometry.Stack.structureSheaf`. Its presheaf is
definitionally the commutative structure presheaf followed by `forget₂ CommRingCat RingCat`. -/
noncomputable def ringStructureSheafCore {X : Type v} [Category.{w} X]
    (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) :
    Sheaf (associatedTopology B S hS p τ) RingCat.{u} := by
  let J := τ.over (B.obj hS)
  have hId : (𝟭 (BigFppfOver B S hS)).inheritedTopology J ≤ J :=
    Precoverage.toGrothendieck_le_iff_le_toPrecoverage.2 fun _ _ hR => by simpa using hR.2
  let Oid : Sheaf ((𝟭 (BigFppfOver B S hS)).inheritedTopology J) RingCat.{u} :=
    ⟨(baseRingStructureSheaf B S hS τ hτ).obj,
      (baseRingStructureSheaf B S hS τ hτ).property.of_le hId⟩
  letI : p.IsFibered := hp.isFibered
  letI : (𝟭 (BigFppfOver B S hS)).IsFibered :=
    Functor.isFiberedInGroupoids_id.isFibered
  letI := ((Functor.isFibredOneMorphism_id p).isContinuous_and_isCocontinuous_inheritedTopology
    J).1
  exact ⟨p.op ⋙ Oid.obj, p.op_comp_isSheaf _ _ Oid⟩

/-- The presheaf of `ringStructureSheafCore` is the fppf structure presheaf composed with `p`. -/
@[simp]
theorem ringStructureSheafCore_obj {X : Type v} [Category.{w} X]
    (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) :
    (ringStructureSheafCore B S hS p hp τ hτ).obj =
      p.op ⋙ (BigFppfOver.structureSheaf B S hS).obj := rfl

/-- The structure sheaf with its rings lifted to a universe containing the site. This realizes
the same ring of sections, transported through `ULift`. -/
noncomputable def ringStructureSheaf {X : Type v} [Category.{w} X]
    (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) :
    Sheaf (associatedTopology B S hS p τ) RingCat.{max u v w r} := by
  let F : RingCat.{u} ⥤ RingCat.{max u v w r} :=
    { obj R := RingCat.of (ULift.{max v w r} R)
      map f := RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          (f.hom.comp ULift.ringEquiv.toRingHom)) }
  let O := ringStructureSheafCore B S hS p hp τ hτ
  refine ⟨O.obj ⋙ F, ?_⟩
  let : PreservesLimitsOfSize.{w, max w v} (forget RingCat.{u}) :=
    preservesLimits_of_natIso ringForgetIsoCoyoneda
  let : PreservesLimitsOfSize.{w, max w v} (forget RingCat.{max u v w r}) :=
    preservesLimits_of_natIso ringForgetIsoCoyoneda
  let : ReflectsLimitsOfSize.{w, max w v} (forget RingCat.{max u v w r}) :=
    reflectsLimits_of_reflectsIsomorphisms
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget RingCat.{max u v w r})
  change Presheaf.IsSheaf _ ((O.obj ⋙ forget RingCat.{u}) ⋙ uliftFunctor.{max v w r})
  exact Presheaf.isSheaf_comp_of_isSheaf _ _ _
    (Presheaf.isSheaf_comp_of_isSheaf _ _ _ O.property)

end AlgebraicGeometry.Stack

end
