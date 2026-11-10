module

public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsBigFppfRepresentable

/-!
# Small values of a limit preserving Zariski sheaf from its locally Noetherian values

Let `S` be a locally Noetherian scheme contained in a big fppf site `B`, and let `F'` be a functor
on the big fppf site of `S` which is a sheaf for the Zariski coverings and limit preserving. If
the values of `F'` on the locally Noetherian objects are `u`-small, so are all its values: over an
affine object lying over an affine open of `S` the value is a filtered colimit, over a `u`-small
directed set, of values on locally Noetherian objects, and in general it embeds into the product
of the values on a `u`-small affine open covering.

## Main results

* `AlgebraicGeometry.ExtendingFunctors.small_obj_of_small_restriction`: a limit preserving
  Zariski sheaf whose values on the locally Noetherian objects are `u`-small has `u`-small
  values.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry.ExtendingFunctors

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S) [IsLocallyNoetherian S]
  {F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w (u + 1))}

include hS in
/-- **Small values over affine objects.**  If `F'` is limit preserving and its values on the
locally Noetherian objects are `u`-small, then its value on an affine object lying over an affine
open of `S` is `u`-small. -/
theorem small_obj_of_isAffineOverAffineOpen
    (hFl : LimitPreserving.{u, max w (u + 1), u, u, u + 1, u} (BigFppfOver.toScheme B S hS) F')
    (hsmall : ∀ V : LocallyNoetherianOver B S hS,
      Small.{u} (F'.obj (op ((LocallyNoetherianOver.toBigFppfOver B S hS).obj V))))
    (W : BigFppfOver B S hS) (hW : IsAffineOverAffineOpen ((bigFppfOverToOver B hS).obj W)) :
    Small.{u} (F'.obj (op W)) := by
  let P := IsContainedLocallyNoetherianOver B (S := S)
  obtain ⟨Λ, _, _, _, D, c, hc, ci, haff⟩ :=
    exists_lfpPresentation (hasFinitePresentationAffines_isContainedLocallyNoetherianOver B hS) _ hW
  let ι := LocallyNoetherianOver.toBigFppfOver B S hS
  let G : (lfpPart P).FullSubcategory ⥤ LocallyNoetherianOver B S hS :=
    ObjectProperty.ιOfLE (lfpPart_le P) ⋙ toLocallyNoetherianOver B hS
  let D' : Λᵒᵖ ⥤ BigFppfOver B S hS := D ⋙ G ⋙ ι
  let hK := fullyFaithfulBigFppfOverToOver B hS
  let c' : Cone D' :=
    { pt := W
      π :=
        { app := fun l => hK.preimage (ci.inv ≫ c.π.app l)
          naturality := by
            intro l l' f
            apply hK.map_injective
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
              Functor.map_comp, Functor.FullyFaithful.map_preimage]
            exact congrArg (ci.inv ≫ ·) (c.w f).symm } }
  have hKc : IsLimit ((bigFppfOverToOver B hS).mapCone c') :=
    IsLimit.ofIsoLimit hc (Cone.ext ci (fun l => by
      change c.π.app l = ci.hom ≫ (bigFppfOverToOver B hS).map
        (hK.preimage (Y := D'.obj l) (ci.inv ≫ c.π.app l))
      rw [hK.map_preimage]
      exact (Iso.hom_inv_id_assoc ci (c.π.app l)).symm))
  have : IsConnected Λᵒᵖ := IsCofiltered.isConnected _
  have hc' : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c') :=
    isLimitOfPreserves (Over.forget S) hKc
  obtain ⟨hcol⟩ := hFl Λᵒᵖ D' c' hc' haff hW.1
  have : ∀ l, Small.{u} (F'.obj (op (D'.obj l))) := fun l => hsmall (G.obj (D.obj l))
  refine small_of_surjective (f := fun x : Σ l : Λᵒᵖ, F'.obj (op (D'.obj l)) =>
    F'.map (c'.π.app x.1).op x.2) fun y => ?_
  obtain ⟨l, x, hx⟩ := exists_eq_map_of_isColimit_mapCocone F' D' c' hcol y
  exact ⟨⟨l, x⟩, hx⟩

/-- **A limit preserving Zariski sheaf with `u`-small values on the locally Noetherian objects has
`u`-small values.** -/
theorem small_obj_of_small_restriction
    (hFs : IsCoveringSheafOnSubcategory.{max w (u + 1), u, u} .zariski (IsContainedOver B (S := S))
      ((toBigFppfOver B hS).op ⋙ F'))
    (hFl : LimitPreserving.{u, max w (u + 1), u, u, u + 1, u} (BigFppfOver.toScheme B S hS) F')
    (hsmall : ∀ V : LocallyNoetherianOver B S hS,
      Small.{u} (F'.obj (op ((LocallyNoetherianOver.toBigFppfOver B S hS).obj V))))
    (T : BigFppfOver B S hS) : Small.{u} (F'.obj (op T)) := by
  obtain ⟨ι, W, j, haff, -, -, hsep⟩ :=
    exists_isAffineOverAffineOpen_bigFppfOver_cover.{max w (u + 1)} B hS T
  have : ∀ i, Small.{u} (F'.obj (op (W i))) := fun i =>
    small_obj_of_isAffineOverAffineOpen B hS hFl hsmall (W i) (haff i)
  exact small_of_injective (f := fun x : F'.obj (op T) => fun i => F'.map (j i).op x)
    fun x y hxy => hsep hFs x y fun i => congrFun hxy i

end AlgebraicGeometry.ExtendingFunctors
