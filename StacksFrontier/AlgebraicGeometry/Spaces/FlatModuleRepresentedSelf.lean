module

public import StacksFrontier.AlgebraicGeometry.RelativeProjFlat.GradedPieces
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleChartSections

/-!
# Flatness over a represented algebraic space, read on the representing scheme

Let `T` be an object of the big fppf site whose represented functor is an algebraic space, and
let `G` be a module over it which is flat over the identity of that space (Stacks 05VV). Read at
the identity chart, its restriction `AlgebraicGeometry.Space.representedZariskiRestriction` to
the representing scheme is flat over the identity of that scheme, and when `G` is
quasi-coherent its sections over every affine open are flat.

## Main results

* `AlgebraicGeometry.Space.isFlatOver_representedZariskiRestriction_of_isFlatOver_id` and
  `AlgebraicGeometry.Space.flat_sections_representedZariskiRestriction_of_isFlatOver_id`:
  **flatness of a module over its own represented algebraic space is Zariski flatness of its
  restriction to the representing scheme**, and over an affine open it is flatness of the
  sections. This is flatness over the space *itself*, not over a base scheme, so it is read on
  the identity chart on both sides of the square.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Represented

variable (T : BigFppfOver B S hS)

variable (hT : IsAlgebraicSpace B S hS (yoneda.obj T))
  (G : Modules.{u, u} B S hS (yoneda.obj T) hT)

/-- **A module flat over its own represented algebraic space restricts to a module flat over
the representing scheme.**  Read at the identity chart on both sides of the square, flatness
over the space in the sense of Stacks 05VV is the ringed-space flatness of Stacks 08KT of
`AlgebraicGeometry.Space.representedZariskiRestriction` over the identity of the representing
scheme. -/
theorem isFlatOver_representedZariskiRestriction_of_isFlatOver_id
    (hflat : IsFlatOver B S hS hT (𝟙 (yoneda.obj T)) G) :
    AlgebraicGeometry.IsFlatOver
      (𝟙 ((BigFppfOver.toScheme B S hS).obj T) :
        (BigFppfOver.toScheme B S hS).obj T ⟶ _).toLRSHom.toShHom
      (representedZariskiRestriction B S hS T hT G) := by
  have hd : AlgebraicGeometry.IsFlatOver
      (LocallyRingedSpace.forgetToSheafedSpace.map
        ((BigFppfOver.toScheme B S hS).map
          (𝟙 ((SmallEtale.toOver B S hS (yoneda.obj T)).obj
            (selfChart B S hS T)))).toLRSHom)
      (representedZariskiRestriction B S hS T hT G) :=
    hflat
      { U := selfChart B S hS T
        V := selfChart B S hS T
        g := 𝟙 _
        comm := by
          rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] }
  rwa [CategoryTheory.Functor.map_id] at hd

/-- **The sections of a quasi-coherent module flat over its own represented algebraic space are
flat over the functions on an affine open of the representing scheme.**  Here the sections are
those of `AlgebraicGeometry.Space.representedZariskiRestriction`. -/
theorem flat_sections_representedZariskiRestriction_of_isFlatOver_id
    (hGqc : G.IsQuasicoherentOnSite) (hflat : IsFlatOver B S hS hT (𝟙 (yoneda.obj T)) G)
    (V : ((BigFppfOver.toScheme B S hS).obj T).Opens) (hV : IsAffineOpen V) :
    Module.Flat Γ((BigFppfOver.toScheme B S hS).obj T, V)
      Γ(representedZariskiRestriction B S hS T hT G, V) := by
  have : SheafOfModules.IsQuasicoherent (representedZariskiRestriction B S hS T hT G) :=
    isQuasicoherent_restrictToChart B S hS ⟨yoneda.obj T, hT⟩ G hGqc (selfChart B S hS T)
  exact AlgebraicGeometry.flat_sections_of_isFlatOver_id _
    (isFlatOver_representedZariskiRestriction_of_isFlatOver_id B S hS T hT G hflat) V hV

end Represented

end AlgebraicGeometry.Space

end
