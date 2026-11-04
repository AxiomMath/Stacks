module

public import StacksFrontier.AlgebraicGeometry.ColimitClose.Basic

/-!
# Finitely many sections of a quasi-coherent module come from one of finite type

On a quasi-compact quasi-separated scheme `S`, let `F` be a quasi-coherent `𝒪_S`-module and let
`σ_k ∈ Γ(V_k, F)` be finitely many sections over affine opens `V_k`. Then there is a
quasi-coherent `𝒪_S`-module `E` of finite type with a morphism `u : E ⟶ F` and sections
`e_k ∈ Γ(V_k, E)` with `u(e_k) = σ_k`.

This is the step of the proof of [Stacks, Tag 07RM] which, after writing `f_*L` as the directed
colimit of its finite type quasi-coherent submodules ([Stacks, Tag 01PG]), chooses one stage of
the colimit through which the finitely many sections defining the local immersions all factor.

## Main results

* `Stacks.QuasiProjectiveCompactification.exists_isFiniteType_hom_lift`: the statement above.

## Implementation notes

Each section is a section of some finite type quasi-coherent submodule of `F`, by
`Stacks.AlgebraicGeometry.Tag01PGColimitClose.affineSections_of_qcqs`; the category of those
submodules is filtered (`AlgebraicGeometry.finiteTypeQuasicoherentSubobject_isFiltered`), so the
finitely many submodules obtained lie in a common one, which is `E`, with `u` its inclusion.

## References

* [Stacks Project, Tag 07RM](https://stacks.math.columbia.edu/tag/07RM)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.QuasiProjectiveCompactification

/-- **Finitely many sections over affine opens factor through one finite type submodule.** On a
quasi-compact quasi-separated scheme `S`, for a quasi-coherent `𝒪_S`-module `F` and finitely
many sections `σ k` of `F` over affine opens `V k`, there are a quasi-coherent `𝒪_S`-module `E`
of finite type, a morphism `u : E ⟶ F` and sections `e k` of `E` over `V k` with
`u (e k) = σ k`. -/
theorem exists_isFiniteType_hom_lift {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (F : S.Modules) [F.IsQuasicoherent] {κ : Type*} [Finite κ] (V : κ → S.Opens)
    (hV : ∀ k, IsAffineOpen (V k)) (σ : ∀ k, Γ(F, V k)) :
    ∃ (E : S.Modules) (_ : E.IsQuasicoherent) (_ : E.IsFiniteType) (u : E ⟶ F)
      (e : ∀ k, Γ(E, V k)), ∀ k, u.app (V k) (e k) = σ k := by
  classical
  have := Fintype.ofFinite κ
  choose G t ht using fun k =>
    Stacks.AlgebraicGeometry.Tag01PGColimitClose.affineSections_of_qcqs F ⟨V k, hV k⟩ (σ k)
  obtain ⟨H, hH⟩ := IsFiltered.sup_objs_exists (Finset.univ.image G)
  have hle : ∀ k, G k ⟶ H := fun k =>
    (hH (Finset.mem_image_of_mem G (Finset.mem_univ k))).some
  refine ⟨(H.obj : S.Modules), H.2.1, H.2.2, H.obj.arrow,
    fun k => (Subobject.ofLE _ _ (hle k).hom.le).app (V k) (t k), fun k => ?_⟩
  rw [← ht k, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Subobject.ofLE_arrow]

end Stacks.QuasiProjectiveCompactification

end
