module

public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.AffineCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineSpannedRelations
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffinePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCover
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentLocality

/-!
# A sheaf of modules cartesian on affine objects is quasi-coherent

On the fppf site associated with a category fibred in groupoids over `(Sch/S)_fppf`, a sheaf of
modules whose restriction maps between affine objects are base changes
(`AlgebraicGeometry.FibredSite.IsCartesianOnAffines`) is quasi-coherent: on the slice at an affine
object `x` it is presented by the module of its sections over `x`.  Together with
`AlgebraicGeometry.FibredSite.isCartesianOnAffines_of_isQuasicoherentOnSite` this characterizes
quasi-coherence as cartesianness on affine objects (Stacks 03DX on the affine slices).

## Main results

* `AlgebraicGeometry.FibredSite.hasGlobalPresentation_over_of_isCartesianOnAffines`.
* `AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_of_isCartesianOnAffines`.
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct

universe u v w

namespace AlgebraicGeometry.FibredSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Type v} [Category.{w} 𝒳] {p : 𝒳 ⥤ BigFppfOver B S hS} (hp : p.IsFiberedInGroupoids)

/-- **A sheaf of modules cartesian on affine objects has, on the slice at an affine object, the
base-change property of the sections of its universe lift**, in the form
`AlgebraicGeometry.FibredSite.HasSectionBaseChangeOn` asks for. -/
theorem hasSectionBaseChangeOn_of_isCartesianOnAffines
    (N : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hN : IsCartesianOnAffines hp N.val) {x : 𝒳} (hx : IsAffineOver B S hS (p.obj x))
    (Q : Over x → Prop) (hQ : ∀ W, Q W → IsAffineOver B S hS (p.obj W.left)) :
    HasSectionBaseChangeOn B S hS p hp
      (SheafOfModules.uliftForPresentation.{max v w, w, u, u, max v w u} (N.over x)) Q := by
  intro W hW i1 i2 i3 i4 i5
  have hb := hN (Over.mkIdTerminal.from W).left hx (hQ W hW)
  let : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (N.val.obj (op (Over.mk (𝟙 x)).left)) := sectionModule hp N.val (Over.mk (𝟙 x)).left
  let : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      (N.val.obj (op W.left)) := sectionModule hp N.val W.left
  let : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (N.val.obj (op W.left)) := sectionModuleAlong hp N.val (Over.mkIdTerminal.from W).left
  have : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) (N.val.obj (op W.left)) :=
    sectionIsScalarTower hp N.val (Over.mkIdTerminal.from W).left
  exact Module.BaseChange.bijective_liftBaseChange_of_comm _
    (restrictionLinearMap hp N.val (Over.mkIdTerminal.from W).left)
    (ULift.moduleEquiv (M := N.val.obj (op (Over.mk (𝟙 x)).left)))
    (ULift.moduleEquiv (R := Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤))
      (M := N.val.obj (op W.left))) (fun _ => rfl) hb

/-- **A sheaf of modules cartesian on affine objects is globally presented on the slice at an
affine object.** -/
theorem hasGlobalPresentation_over_of_isCartesianOnAffines
    (N : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hN : IsCartesianOnAffines hp N.val) {x : 𝒳} (hx : IsAffineOver B S hS (p.obj x)) :
    (N.over x).HasGlobalPresentation := by
  have hcov : Sieve.ofArrows (fun _ : PUnit.{1} => (Over.mk (𝟙 x) : Over x))
      (fun _ => 𝟙 _) ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x)
        (Over.mk (𝟙 x)) := by
    have htop : Sieve.ofArrows (fun _ : PUnit.{1} => (Over.mk (𝟙 x) : Over x))
        (fun _ => 𝟙 _) = ⊤ :=
      (Sieve.id_mem_iff_eq_top).1 (Sieve.ofArrows_mk _ (fun _ => 𝟙 _) PUnit.unit)
    rw [htop]
    exact GrothendieckTopology.top_mem _ _
  have h := isLocallySpannedBySections_and_hasLocallySpannedRelations_of_hasSectionBaseChangeOn
    B S hS p hp (N.over x) hx (fun _ : PUnit.{1} => 𝟙 (Over.mk (𝟙 x))) hcov
    (hasSectionBaseChangeOn_of_isCartesianOnAffines hp N hN hx _ fun _ hW => hW.1)
  exact SheafOfModules.HasGlobalPresentation.of_isGeneratedByUnit
    (SheafOfModules.isGeneratedByUnit_of_isLocallySpannedBySections _ h.1)
    (SheafOfModules.hasGeneratedRelations_of_isLocallySpannedBySections _ _ h.2)

/-- **A sheaf of modules cartesian on affine objects is quasi-coherent.** -/
theorem isQuasicoherentOnSite_of_isCartesianOnAffines
    (N : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hN : IsCartesianOnAffines hp N.val) : N.IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation N
    (coversTop_affineObj B S hS p hp)
    (fun i => hasGlobalPresentation_over_of_isCartesianOnAffines hp N hN i.property)

end AlgebraicGeometry.FibredSite
