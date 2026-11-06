module

public import StacksFrontier.Deformation.Artin.LocallyNoetherianAlgebraicSpaceCriterion

/-!
# The diagonal from affine test objects of finite presentation

Let `S` be a locally Noetherian scheme contained in a big fppf site `B`. Criterion (3) of
**Stacks 0GE5** for the diagonal of a functor `F` on the locally Noetherian site of `S` asks that
the equalizer of two sections of `F` be representable only over the affine test objects of finite
presentation over `S` (`AlgebraicGeometry.ExtendingFunctors.DiagRepresentableOnAffineLfp`). This
file proves that, for an étale sheaf `F` which is limit preserving, criterion (3) implies
criterion (2): the diagonal of `F` is representable over every locally Noetherian test object.

The file also records that a limit preserving Zariski sheaf whose values on the locally Noetherian
objects are subsingletons has subsingleton values everywhere.

## Main results

* `AlgebraicGeometry.ExtendingFunctors.relativelyRepresentable_diag_of_affineLfp_of_isSheaf`:
  Stacks 0GE5, (3) ⇒ (2), for the diagonal of a limit preserving étale sheaf on the locally
  Noetherian site.
* `AlgebraicGeometry.ExtendingFunctors.subsingleton_obj_of_subsingleton_restriction`: a limit
  preserving Zariski sheaf whose values on the locally Noetherian objects are subsingletons has
  subsingleton values.

## References

* [Stacks Project, Tag 0GE3](https://stacks.math.columbia.edu/tag/0GE3)
* [Stacks Project, Tag 0GE5](https://stacks.math.columbia.edu/tag/0GE5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Presheaf

universe v w u

namespace AlgebraicGeometry.ExtendingFunctors

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)

/-- Representability of the diagonal over the affine test objects of finite presentation is
invariant under isomorphisms of functors. -/
theorem diagRepresentableOnAffineLfp_of_iso
    {P Q : (LocallyNoetherianOver B S hS)ᵒᵖ ⥤ Type (max w (u + 1))} (e : P ≅ Q)
    (h : DiagRepresentableOnAffineLfp B hS P) : DiagRepresentableOnAffineLfp B hS Q := by
  intro V hV hVl a b
  obtain ⟨X, snd, hX⟩ := h V hV hVl (e.inv.app _ a) (e.inv.app _ b)
  refine ⟨X, snd, ?_⟩
  have := (representsEqualizer_iff_of_iso e snd _ _).1 hX
  simpa only [← types_comp_apply (e.inv.app _) (e.hom.app _), ← NatTrans.comp_app,
    Iso.inv_hom_id, NatTrans.id_app, types_id_apply] using this

variable [IsLocallyNoetherian S]

/-- **Stacks 0GE5, (3) ⇒ (2), for the diagonal of a functor on the big fppf site.** Let `F'` be a
Zariski sheaf on the big fppf site of `S` which is limit preserving, and whose restriction to the
locally Noetherian site has diagonal representable over the affine test objects of finite
presentation over `S`. Then the restriction has representable diagonal. -/
theorem relativelyRepresentable_diag_restriction_of_affineLfp
    {F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w (u + 1))}
    (hFs : IsCoveringSheafOnSubcategory.{max w (u + 1), u, u} .zariski (IsContainedOver B (S := S))
      ((toBigFppfOver B hS).op ⋙ F'))
    (hFl : LimitPreserving.{u, max w (u + 1), u, u, u + 1, u} (BigFppfOver.toScheme B S hS) F')
    (hdiag : DiagRepresentableOnAffineLfp B hS
      ((LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ F')) :
    (uliftYoneda.{max w (u + 1)} (C := LocallyNoetherianOver B S hS)).relativelyRepresentable
      (diag ((LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙ F')) := by
  rw [uliftYoneda_relativelyRepresentable_diag_iff]
  intro V a b
  obtain ⟨X, snd, h, hlft⟩ :=
    exists_representsEqualizer_lft_of_affineLfp B hS hFs hFl hdiag _ a b
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj
      ((LocallyNoetherianOver.toBigFppfOver B S hS).obj V)) := V.property
  have hX : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj X) :=
    LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B S hS).map snd)
  refine ⟨⟨X, hX⟩, ObjectProperty.homMk snd, fun Z ψ ψ' hψ => ?_, fun Z φ => ?_⟩
  · exact ObjectProperty.hom_ext _ (h.1 _ ψ.hom ψ'.hom (congrArg (fun k => k.hom) hψ))
  · refine (h.2 _ φ.hom).trans ⟨fun ⟨ψ, hψ⟩ => ⟨ObjectProperty.homMk ψ,
      ObjectProperty.hom_ext _ hψ⟩, fun ⟨ψ, hψ⟩ => ⟨ψ.hom, congrArg (fun k => k.hom) hψ⟩⟩

/-- **Stacks 0GE5, (3) ⇒ (2), for the diagonal of a limit preserving étale sheaf on the locally
Noetherian site.** Let `F` be a functor on the locally Noetherian site of `S` which satisfies the
sheaf condition for étale coverings and is limit preserving. If the equalizer of any two sections
of `F` over an affine test object of finite presentation over `S` is representable, then the
diagonal of `F` is representable. -/
theorem relativelyRepresentable_diag_of_affineLfp_of_isSheaf
    {F : (LocallyNoetherianOver B S hS)ᵒᵖ ⥤ Type (max w (u + 1))}
    (hFs : ∀ E : Covering (LocallyNoetherianOver B S hS),
      LocallyNoetherianOver.IsEtaleCovering B S hS E → E.2.presieve₀.IsSheafFor F)
    (hFl : LimitPreserving.{u, max w (u + 1), u, u, u + 1, u}
      (LocallyNoetherianOver.toScheme B S hS) F)
    (hdiag : DiagRepresentableOnAffineLfp B hS F) :
    (uliftYoneda.{max w (u + 1)} (C := LocallyNoetherianOver B S hS)).relativelyRepresentable
      (diag F) := by
  obtain ⟨e⟩ := nonempty_restriction_extensionToBigFppfOver_iso hFs hFl
  exact uliftYoneda_relativelyRepresentable_diag_of_iso e
    (relativelyRepresentable_diag_restriction_of_affineLfp B hS
      (isCoveringSheafOnSubcategory_extensionToBigFppfOver hFs hFl)
      (limitPreserving_extensionToBigFppfOver hFs hFl)
      (diagRepresentableOnAffineLfp_of_iso B hS e.symm hdiag))

include hS in
/-- **Subsingleton values over affine objects lying over affine opens of `S`.** A limit preserving
functor on the big fppf site of `S` whose values on the locally Noetherian objects are
subsingletons has subsingleton values over every affine object lying over an affine open of
`S`. -/
theorem subsingleton_obj_of_isAffineOverAffineOpen {F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (hFl : LimitPreserving.{u, v, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) F')
    (hsub : ∀ V : LocallyNoetherianOver B S hS,
      Subsingleton (F'.obj (op ((LocallyNoetherianOver.toBigFppfOver B S hS).obj V))))
    (W : BigFppfOver B S hS) (hW : IsAffineOverAffineOpen ((bigFppfOverToOver B hS).obj W)) :
    Subsingleton (F'.obj (op W)) := by
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
    IsLimit.ofIsoLimit hc (Cone.ext ci fun l => (Iso.hom_inv_id_assoc ci (c.π.app l)).symm.trans
      (congrArg (ci.hom ≫ ·) (hK.map_preimage (Y := D'.obj l) _).symm))
  have : IsConnected Λᵒᵖ := IsCofiltered.isConnected _
  have hc' : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c') :=
    isLimitOfPreserves (Over.forget S) hKc
  obtain ⟨hcol⟩ := hFl Λᵒᵖ D' c' hc' haff hW.1
  refine ⟨fun x y => ?_⟩
  obtain ⟨l, x', rfl⟩ := exists_eq_map_of_isColimit_mapCocone F' D' c' hcol x
  obtain ⟨m, y', rfl⟩ := exists_eq_map_of_isColimit_mapCocone F' D' c' hcol y
  rw [← c'.w (IsCofiltered.minToLeft l m), ← c'.w (IsCofiltered.minToRight l m), op_comp, op_comp,
    Functor.map_comp_apply, Functor.map_comp_apply]
  exact congrArg _ (@Subsingleton.elim _ (hsub (G.obj (D.obj (IsCofiltered.min l m)))) _ _)

/-- **A limit preserving Zariski sheaf whose values on the locally Noetherian objects are
subsingletons has subsingleton values.** -/
theorem subsingleton_obj_of_subsingleton_restriction {F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (hFs : IsCoveringSheafOnSubcategory.{v, u, u} .zariski (IsContainedOver B (S := S))
      ((toBigFppfOver B hS).op ⋙ F'))
    (hFl : LimitPreserving.{u, v, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) F')
    (hsub : ∀ V : LocallyNoetherianOver B S hS,
      Subsingleton (F'.obj (op ((LocallyNoetherianOver.toBigFppfOver B S hS).obj V))))
    (T : BigFppfOver B S hS) : Subsingleton (F'.obj (op T)) := by
  obtain ⟨ι, W, j, haff, -, -, hsep⟩ := exists_isAffineOverAffineOpen_bigFppfOver_cover.{v} B hS T
  refine ⟨fun x y => hsep hFs x y fun i => ?_⟩
  have := subsingleton_obj_of_isAffineOverAffineOpen B hS hFl hsub (W i) (haff i)
  exact Subsingleton.elim _ _

end AlgebraicGeometry.ExtendingFunctors

end
