module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Transpose
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde

/-!
# Global sections of an inverse image over a spectrum, normalized against the unit

Let `β : A ⟶ A'` be a homomorphism of commutative rings and let `N` be a quasi-coherent
`𝒪_{Spec A}`-module.  Taking global sections of the unit of the inverse-image--direct-image
adjunction for `Spec β` and reading the result through
`AlgebraicGeometry.pushforwardΓIso` gives an `A`-linear map

    Γ(N, ⊤) ⟶ Γ((Spec β)^* N, ⊤)

into the `A'`-module of global sections of the inverse image, with its scalars restricted
along `β`.  **This file proves that this map exhibits `Γ((Spec β)^* N, ⊤)` as the extension of
scalars of `Γ(N, ⊤)` along `β`**, by exhibiting its transpose as an isomorphism.

## Main definitions

* `Stacks.AlgebraicGeometry.AffineBaseChangeIso.pullbackΓUnit`: the `A`-linear map above.
* `Stacks.AlgebraicGeometry.AffineBaseChangeIso.pullbackΓIso`: the comparison
  `A' ⊗_A Γ(N, ⊤) ≅ Γ((Spec β)^* N, ⊤)`.

## Main results

* `Stacks.AlgebraicGeometry.AffineBaseChangeIso.pullbackΓIso_hom_one_tmul`: the comparison
  sends `1 ⊗ m` to the value of `pullbackΓUnit` at `m`.  This is the normalization that makes
  the comparison *the* canonical one.
* `Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_transposeExtend_pullbackΓUnit`: the
  transpose of `pullbackΓUnit` is invertible.

## Route

The comparison is built from three invertible maps: the unit `M ≅ Γ(M^~, ⊤)` of the
tilde--sections adjunction at `M = A' ⊗_A Γ(N, ⊤)`, the global sections of
`AlgebraicGeometry.pullbackTildeIso`, and the global sections of the inverse image of
`AlgebraicGeometry.Scheme.Modules.fromTildeΓ`, which is invertible because `N` is
quasi-coherent.

The normalization is where the work is.  On the element `1 ⊗ m` the first map is
`tilde.toOpen` and the second is then pinned down by
`AlgebraicGeometry.pullbackTildeIso_hom_app_unit_toOpen`, which says that the canonical
comparison carries the inverse image of the section represented by `m` to the section
represented by `1 ⊗ m`; the third map is handled by naturality of the adjunction unit along
`fromTildeΓ N` together with the right triangle identity of the tilde--sections adjunction,
which says that `fromTildeΓ N` undoes `tilde.toOpen` on global sections.  No induction on
tensors is used: `Stacks.AlgebraicGeometry.AffineBaseChangeIso.transposeExtend_one_tmul`
already evaluates a transpose at `1 ⊗ m`, so agreement there is agreement everywhere by
`ModuleCat.ExtendScalars.hom_ext`.

## Implementation notes

There are two independent constructions of the comparison of an inverse image of an
associated sheaf with an associated sheaf of an extension of scalars, both obtained from
uniqueness of left adjoints: `AlgebraicGeometry.pullbackTildeIso` and
`Stacks.AlgebraicGeometry.SectionsColimit.tildePullbackIso`.  They differ in which factor
carries the transport, and **only the first carries the normalization against the unit**, so
only the first can be used here; `Stacks.AlgebraicGeometry.SectionsColimit.sectionsPullbackIso`,
which is the same isomorphism of global sections built on the second, cannot.

The invertibility of `fromTildeΓ N` is passed to `CategoryTheory.asIso` explicitly rather than
by instance search.  The source of `fromTildeΓ` is spelled as a direct application of `tilde`,
not as the value of the composite functor that appears here, and instance search does not see
through the definition of `AlgebraicGeometry.tilde.functor` to match the two.

## What is not done

**No assertion of [Stacks, Tag 02KG] is proved here, and no project tag attribute is
attached.**  Nothing here mentions a square of schemes or a base-change morphism of direct
images: this is a statement about a single morphism of affine schemes.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public section

open CategoryTheory TensorProduct Opposite
open AlgebraicGeometry
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.AffineBaseChangeIso

variable {A A' : CommRingCat.{u}} (β : A ⟶ A')

/-- Global sections of the unit of the inverse-image--direct-image adjunction for `Spec β`,
read through `AlgebraicGeometry.pushforwardΓIso` as an `A`-linear map into the global sections
of the inverse image with scalars restricted along `β`. -/
noncomputable def pullbackΓUnit (N : (Spec A).Modules) :
    moduleSpecΓFunctor.obj N ⟶ (ModuleCat.restrictScalars β.hom).obj
      (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map β)).obj N)) :=
  moduleSpecΓFunctor.map
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map β)).unit.app N) ≫
    (pushforwardΓIso A A' β).hom.app _

/-- The comparison of the extension of scalars of the global sections of a quasi-coherent
module over a spectrum with the global sections of its inverse image. -/
noncomputable def pullbackΓIso (N : (Spec A).Modules) [N.IsQuasicoherent] :
    (ModuleCat.extendScalars β.hom).obj (moduleSpecΓFunctor.obj N) ≅
      moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map β)).obj N) :=
  tilde.toTildeΓNatIso.app ((ModuleCat.extendScalars β.hom).obj (moduleSpecΓFunctor.obj N)) ≪≫
    moduleSpecΓFunctor.mapIso
      ((pullbackTildeIso A A' β).app (moduleSpecΓFunctor.obj N)).symm ≪≫
    moduleSpecΓFunctor.mapIso
      ((Scheme.Modules.pullback (Spec.map β)).mapIso
        (@asIso _ _ _ _ (Scheme.Modules.fromTildeΓ N)
          ((isQuasicoherent_iff_isIso_fromTildeΓ N).mp ‹_›)))

/-- **The comparison is the canonical one.**  It sends `1 ⊗ m` to the value at `m` of the
global sections of the adjunction unit. -/
lemma pullbackΓIso_hom_one_tmul (N : (Spec A).Modules) [N.IsQuasicoherent]
    (m : moduleSpecΓFunctor.obj N) :
    (pullbackΓIso β N).hom ((1 : A') ⊗ₜ[A, β.hom] m) = (pullbackΓUnit β N).hom m := by
  have hcancel (x) :
      ((pullbackTildeIso A A' β).inv.app (moduleSpecΓFunctor.obj N)).val.app (.op ⊤)
        (((pullbackTildeIso A A' β).hom.app (moduleSpecΓFunctor.obj N)).val.app (.op ⊤) x) = x := by
    have h := (moduleSpecΓFunctor.mapIso
      ((pullbackTildeIso A A' β).app (moduleSpecΓFunctor.obj N))).hom_inv_id
    exact congr($(h).hom x)
  have hA : ((pullbackTildeIso A A' β).inv.app (moduleSpecΓFunctor.obj N)).val.app (.op ⊤)
      (tilde.toOpen ((ModuleCat.extendScalars β.hom).obj (moduleSpecΓFunctor.obj N)) ⊤
        ((1 : A') ⊗ₜ[A, β.hom] m))
      = ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map β)).unit.app
          (tilde (moduleSpecΓFunctor.obj N))).val.app (.op ⊤)
          (tilde.toOpen (moduleSpecΓFunctor.obj N) ⊤ m) := by
    rw [← pullbackTildeIso_hom_app_unit_toOpen A A' β (moduleSpecΓFunctor.obj N) m]
    exact hcancel _
  have hlhs : (pullbackΓIso β N).hom ((1 : A') ⊗ₜ[A, β.hom] m) =
      ((Scheme.Modules.pullback (Spec.map β)).map (Scheme.Modules.fromTildeΓ N)).val.app (.op ⊤)
        (((pullbackTildeIso A A' β).inv.app (moduleSpecΓFunctor.obj N)).val.app (.op ⊤)
          (tilde.toOpen ((ModuleCat.extendScalars β.hom).obj (moduleSpecΓFunctor.obj N)) ⊤
            ((1 : A') ⊗ₜ[A, β.hom] m))) := by
    simp only [pullbackΓIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rfl
  have hnat := (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map β)).unit.naturality
    (Scheme.Modules.fromTildeΓ N)
  have hB := congr($(hnat).val.app (.op ⊤) (tilde.toOpen (moduleSpecΓFunctor.obj N) ⊤ m))
  have hC : (Scheme.Modules.fromTildeΓ N).val.app (.op ⊤)
      (tilde.toOpen (moduleSpecΓFunctor.obj N) ⊤ m) = m :=
    congr($(tilde.adjunction.right_triangle_components (Y := N)).hom m)
  rw [hlhs, hA]
  exact hB.symm.trans (congrArg
    (fun z => ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map β)).unit.app N).val.app
      (.op ⊤) z) hC)

/-- **Global sections of an inverse image over a spectrum are an extension of scalars.**  The
transpose of `pullbackΓUnit` under extension of scalars along `β` is invertible. -/
theorem isIso_transposeExtend_pullbackΓUnit (N : (Spec A).Modules) [N.IsQuasicoherent] :
    IsIso (transposeExtend β (pullbackΓUnit β N)) := by
  have h : transposeExtend β (pullbackΓUnit β N) = (pullbackΓIso β N).hom := by
    refine ModuleCat.ExtendScalars.hom_ext fun m => ?_
    exact (transposeExtend_one_tmul β (pullbackΓUnit β N) m).trans
      (pullbackΓIso_hom_one_tmul β N m).symm
  rw [h]
  infer_instance

end Stacks.AlgebraicGeometry.AffineBaseChangeIso

end
