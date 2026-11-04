module

public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiReadingInvertibleQuotients
public import StacksFrontier.AlgebraicGeometry.Spaces.RetractionPushforwardReflect

/-!
# The Zariski reading reflects isomorphisms of quasi-coherent modules, functorially

On the represented algebraic space of a test object `T`, the Zariski reading
`AlgebraicGeometry.Space.zariskiReadingFunctor T` is fully faithful on quasi-coherent modules:
the counit of its adjunction is invertible there.  The isomorphism
`AlgebraicGeometry.Space.isoOfZariskiReadingIso` lifting an isomorphism of readings is read back
as that isomorphism, and a morphism of quasi-coherent modules is determined by its reading.

## Main results

* `AlgebraicGeometry.Space.zariskiReading_map_isoOfZariskiReadingIso_hom`: the reading of the
  lift of `e` is `e`.
* `AlgebraicGeometry.Space.zariskiReading_map_injective`: the reading is faithful on morphisms
  out of a quasi-coherent module.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (T : BigFppfOver B S hS)

/-- For an adjunction `F ⊣ G` whose counit is invertible at `N` and `N'`, the morphism
`ε_N⁻¹ ≫ F(e) ≫ ε_{N'}` lifting `e : G N ⟶ G N'` is read back by `G` as `e`. -/
theorem _root_.CategoryTheory.Adjunction.map_inv_counit_comp_map_comp_counit {C D : Type*}
    [Category C] [Category D] {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) {N N' : C}
    [IsIso (adj.counit.app N)] (e : G.obj N ⟶ G.obj N') :
    G.map (inv (adj.counit.app N) ≫ F.map e ≫ adj.counit.app N') = e := by
  have h1 : adj.unit.app (G.obj N) ≫ G.map (adj.counit.app N) = 𝟙 _ :=
    adj.right_triangle_components N
  have hinv : G.map (inv (adj.counit.app N)) = adj.unit.app (G.obj N) := by
    rw [Functor.map_inv]
    exact (IsIso.eq_inv_of_inv_hom_id h1).symm
  rw [G.map_comp, G.map_comp, hinv, ← Category.assoc, adj.unit_naturality e, Category.assoc,
    adj.right_triangle_components N', Category.comp_id]

/-- **The reading of the lift of an isomorphism of Zariski readings is that isomorphism.** -/
theorem zariskiReading_map_isoOfZariskiReadingIso_hom
    {N N' : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (hN : N.IsQuasicoherentOnSite) (hN' : N'.IsQuasicoherentOnSite)
    (e : (zariskiReadingFunctor T).obj N ≅ (zariskiReadingFunctor T).obj N') :
    (zariskiReadingFunctor T).map (isoOfZariskiReadingIso T hN hN' e).hom = e.hom := by
  have := isIso_zariskiReadingAdjunction_counit_app T N hN
  exact (zariskiReadingAdj T).map_inv_counit_comp_map_comp_counit e.hom

/-- **The Zariski reading is faithful on morphisms out of a quasi-coherent module.** -/
theorem zariskiReading_map_injective
    {N N' : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (hN : N.IsQuasicoherentOnSite) {a b : N ⟶ N'}
    (h : (zariskiReadingFunctor T).map a = (zariskiReadingFunctor T).map b) : a = b := by
  have := isIso_zariskiReadingAdjunction_counit_app T N hN
  exact (zariskiReadingAdj T).map_injective_of_isIso_counit h

end AlgebraicGeometry.Space

end
