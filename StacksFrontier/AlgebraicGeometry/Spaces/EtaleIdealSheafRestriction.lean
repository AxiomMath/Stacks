module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompIsoEtaleRestriction

/-!
# The ideal sheaf of the inverse image of a closed subspace along an étale morphism

Let `φ : U ⟶ X` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `Z ⊆ X` be a closed subspace, with defining ideal sheaf `𝓘_Z ⊆ 𝒪_X` of
Stacks 03MB.  The inverse image `φ⁻¹(Z) = Z ×_X U` is a closed subspace of `U`, and its defining
ideal sheaf is the étale restriction of `𝓘_Z`:

`𝓘_{φ⁻¹(Z)} = 𝓘_Z|_U`.

This is the clause of Stacks 04CO that the source calls clear from the construction of `𝓘` in
Stacks 03MB, and here it is indeed immediate: an étale chart `V` of `U` is carried by
`AlgebraicGeometry.Space.smallEtalePostcomp` to the chart of `X` whose structure morphism is
`V ⟶ U ⟶ X`, and the defining ideal of a closed subspace at a chart is the kernel of pullback of
regular functions along the base change of the subspace to that chart.  Both sides are therefore
the kernel of the *same* ring homomorphism `Γ(V) ⟶ Γ(Z ×_X V)`, so the two ideal sheaves have
equal sections at every chart.

## Main definitions

* `AlgebraicGeometry.Space.etaleRestrictionDefiningIdeal` and
  `AlgebraicGeometry.Space.etaleRestrictionDefiningIdealSheaf`: the étale restriction of `𝓘_Z`
  taken inside the submodules of `𝒪_U`, first as a family of ideals indexed by the étale charts
  of `U` and then as a sheaf submodule of `𝒪_U`.
* `AlgebraicGeometry.Space.etaleIdealSheafRestrictionIso`: **Stacks 04CO**, the identification of
  the étale restriction of the defining ideal sheaf of `Z` with the defining ideal sheaf of
  `φ⁻¹(Z)`, as an isomorphism of `𝒪_U`-modules.

## Main results

* `AlgebraicGeometry.Space.definingIdealAt_preimage_eq_definingIdealAt_postcomp`: the chartwise
  equality of ideals, which is the whole content.
* `AlgebraicGeometry.Space.etaleRestrictionDefiningIdealSheaf_eq`: that equality assembled, as an
  equality of sheaf submodules of `𝒪_U`.
* `AlgebraicGeometry.Space.etaleModulePullback_definingIdealSheaf_eq`: consequently an *equality*
  — not merely an isomorphism — of `𝒪_U`-modules between the étale restriction of `𝓘_Z` and
  `𝓘_{φ⁻¹(Z)}`.
* `AlgebraicGeometry.Space.etaleIdealSheafRestrictionIso_hom_apply_coe` and
  `AlgebraicGeometry.Space.etaleIdealSheafRestrictionIso_inv_apply_coe`: the isomorphism is the
  identity on the underlying regular functions over every étale chart of `U`, so it is the
  canonical one and not merely some abstract comparison.
* `AlgebraicGeometry.Space.etaleIdealSheafRestrictionIso_comp`: the identifications compose,
  for a composable pair of étale morphisms with étale composite.  This is the step-three
  ingredient of the functoriality in the étale source that Stacks 04CO also asserts; the other
  three are named in the "What is not proved" section of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleEtaleRestriction.lean`.

## Implementation notes

The chartwise equality needs no étaleness: it is `definingIdealAt_preimage` of
`StacksFrontier/AlgebraicGeometry/Spaces/LocallyPrincipalPullback.lean` compared with
`definingIdealAt_eq_ker` of `StacksFrontier/AlgebraicGeometry/Spaces/ClosedSubspaceIdeals.lean` at
the postcomposed chart, and `AlgebraicGeometry.Space.smallEtalePostcomp_obj_hom` is `rfl`.
Étaleness enters only to have the restriction functor
`AlgebraicGeometry.Space.etaleModulePullback` at all, that is, to know that postcomposition with
`φ` lands in the étale charts of `X`.

Étale restriction of modules is restriction along `AlgebraicGeometry.Space.smallEtalePostcomp`
with no change of scalars, so the sections of the restriction over a chart `V` of `U` are the
sections of the original over the postcomposed chart *on the nose*
(`AlgebraicGeometry.Space.etaleModulePullback_obj_val_obj` is `rfl`).  That is what lets the
restriction be formed inside the submodules of `𝒪_U`, by
`AlgebraicGeometry.Space.etaleRestrictionDefiningIdeal`, rather than only after passing to the
associated sheaves of modules: the restricted sections are already ideals of the *same* rings of
regular functions.  Locality of membership for the restricted family is not reproved from
continuity of postcomposition; it is read off from the chartwise equality, since the restricted
family *is* the defining ideal sheaf of `φ⁻¹(Z)`.  Assembling the two,
`AlgebraicGeometry.Space.etaleModulePullback_definingIdealSheaf_eq` is the chartwise equality
rewritten and then `rfl`.

The composition law holds on the nose for the same reason: the two iterated restrictions are
compared by `AlgebraicGeometry.Space.etaleModulePullbackComp`, which is the identity on sections
by `AlgebraicGeometry.Space.etaleModulePullbackComp_hom_app_val_app`, and the two closed
subspaces `ψ⁻¹(φ⁻¹(Z))` and `(ψ ≫ φ)⁻¹(Z)` are equal.  That comparison is the only reason this
file imports
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackCompIsoEtaleRestriction.lean`.

The isomorphism is nevertheless constructed by hand, chartwise from `LinearEquiv.ofEq`, and not
as `CategoryTheory.eqToIso` of that equality: its components are then visibly the identity on
underlying regular functions, which is what the two canonicity lemmas state and what a consumer
needs in order to compute with it.  Its naturality squares hold by `rfl`, again because no change
of scalars occurs.

## References

* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U X : AlgebraicSpaces B S hS}

/-- **The defining ideal of an inverse image is the defining ideal of the postcomposed chart.**
For a morphism `φ : U ⟶ X` of algebraic spaces and a closed subspace `Z ⊆ X`, the defining ideal
of `φ⁻¹(Z)` at an étale chart `V` of `U` is the defining ideal of `Z` at the chart `V ⟶ U ⟶ X` of
`X`: both are the kernel of pullback of regular functions along the base change of `Z` to `V`. -/
theorem definingIdealAt_preimage_eq_definingIdealAt_postcomp (φ : U ⟶ X)
    (hφ : IsEtale B S hS φ.hom) (Z : ClosedSubspaces B S hS X.1)
    (V : SmallEtale B S hS U.1) :
    definingIdealAt B S hS U (⟨Z.1.preimage φ.hom,
        isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
        ClosedSubspaces B S hS U.1) (op V) =
      definingIdealAt B S hS X Z (op ((smallEtalePostcomp B S hS φ hφ).obj V)) := by
  rw [definingIdealAt_preimage, definingIdealAt_eq_ker, smallEtalePostcomp_obj_hom]
  rfl

/-- The étale restriction of the defining ideal sheaf of `Z ⊆ X` along `φ : U ⟶ X`, as a family
of submodules of `𝒪_U` indexed by the étale charts of `U`: its sections over a chart `V` are the
defining ideal of `Z` at the postcomposed chart `V ⟶ U ⟶ X`.

This is the étale restriction of `AlgebraicGeometry.Space.definingIdealSheaf` taken inside the
submodules of `𝒪_U`, which is possible because restriction along
`AlgebraicGeometry.Space.smallEtalePostcomp` carries `𝒪_X` to `𝒪_U` with no change of
scalars. -/
noncomputable def etaleRestrictionDefiningIdeal (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (Z : ClosedSubspaces B S hS X.1) :
    (SheafOfModules.unit (structureRingSheaf B S hS U)).val.Submodule where
  obj V := definingIdealAt B S hS X Z (op ((smallEtalePostcomp B S hS φ hφ).obj V.unop))
  map f := (definingIdealSheaf B S hS X Z).map ((smallEtalePostcomp B S hS φ hφ).op.map f)

/-- **The étale restriction of the defining ideal sheaf is the defining ideal sheaf of the
inverse image, chartwise.** This is the chartwise equality of ideals, assembled over all étale
charts of `U` into an equality of families of submodules of `𝒪_U`. -/
theorem etaleRestrictionDefiningIdeal_eq (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (Z : ClosedSubspaces B S hS X.1) :
    etaleRestrictionDefiningIdeal B S hS φ hφ Z =
      (definingIdealSheaf B S hS U (⟨Z.1.preimage φ.hom,
        isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
        ClosedSubspaces B S hS U.1)).toSubmodule :=
  PresheafOfModules.Submodule.ext fun V ↦
    (definingIdealAt_preimage_eq_definingIdealAt_postcomp B S hS φ hφ Z V.unop).symm

/-- The étale restriction of the defining ideal sheaf of `Z ⊆ X`, as a sheaf submodule of `𝒪_U`:
membership is local because it is membership in the defining ideal sheaf of `φ⁻¹(Z)`. -/
noncomputable def etaleRestrictionDefiningIdealSheaf (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (Z : ClosedSubspaces B S hS X.1) :
    (SheafOfModules.unit (structureRingSheaf B S hS U)).Submodule where
  toSubmodule := etaleRestrictionDefiningIdeal B S hS φ hφ Z
  isSheaf := by
    rw [etaleRestrictionDefiningIdeal_eq]
    exact (definingIdealSheaf B S hS U (⟨Z.1.preimage φ.hom,
      isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
      ClosedSubspaces B S hS U.1)).isSheaf

/-- **Stacks 04CO, at the level of sheaf submodules of `𝒪_U`.** The étale restriction of the
defining ideal sheaf of `Z ⊆ X` *is* the defining ideal sheaf of the inverse image `φ⁻¹(Z)`. -/
theorem etaleRestrictionDefiningIdealSheaf_eq (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (Z : ClosedSubspaces B S hS X.1) :
    etaleRestrictionDefiningIdealSheaf B S hS φ hφ Z =
      definingIdealSheaf B S hS U (⟨Z.1.preimage φ.hom,
        isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
        ClosedSubspaces B S hS U.1) :=
  SheafOfModules.Submodule.ext (etaleRestrictionDefiningIdeal_eq B S hS φ hφ Z)

/-- **Stacks 04CO, as an equality of `𝒪_U`-modules.** The étale restriction of the defining ideal
sheaf of `Z ⊆ X` along an étale `φ : U ⟶ X` is the defining ideal sheaf of `φ⁻¹(Z)`.

Étale restriction of modules is restriction of sections along
`AlgebraicGeometry.Space.smallEtalePostcomp`, so the restriction of the sheaf of modules attached
to a sheaf submodule of `𝒪_X` is the sheaf of modules attached to the restricted family of
submodules; the restricted family is the defining ideal sheaf of `φ⁻¹(Z)` by
`AlgebraicGeometry.Space.etaleRestrictionDefiningIdealSheaf_eq`. -/
theorem etaleModulePullback_definingIdealSheaf_eq (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (Z : ClosedSubspaces B S hS X.1) :
    (etaleModulePullback.{u, u} B S hS φ hφ).obj
        (definingIdealSheaf B S hS X Z).toSheafOfModules =
      (definingIdealSheaf B S hS U (⟨Z.1.preimage φ.hom,
        isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
        ClosedSubspaces B S hS U.1)).toSheafOfModules := by
  rw [← etaleRestrictionDefiningIdealSheaf_eq B S hS φ hφ Z]
  rfl

/-- **Stacks 04CO.** The étale restriction of the defining ideal sheaf of a closed subspace
`Z ⊆ X` along an étale `φ : U ⟶ X` is the defining ideal sheaf of the inverse image `φ⁻¹(Z)`.

Over every étale chart of `U` the two sheaves have the same sections, by
`AlgebraicGeometry.Space.definingIdealAt_preimage_eq_definingIdealAt_postcomp`, and this
isomorphism is the identity on the underlying regular functions there. -/
@[stacks 04CO "the ideal sheaf of the inverse image is the restriction of the ideal sheaf"]
noncomputable def etaleIdealSheafRestrictionIso (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (Z : ClosedSubspaces B S hS X.1) :
    (etaleModulePullback.{u, u} B S hS φ hφ).obj
        (definingIdealSheaf B S hS X Z).toSheafOfModules ≅
      (definingIdealSheaf B S hS U (⟨Z.1.preimage φ.hom,
        isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
        ClosedSubspaces B S hS U.1)).toSheafOfModules :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun V ↦ LinearEquiv.toModuleIso (LinearEquiv.ofEq _ _
        (definingIdealAt_preimage_eq_definingIdealAt_postcomp B S hS φ hφ Z V.unop).symm))
      (fun _ _ _ ↦ rfl))

/-- The comparison isomorphism of Stacks 04CO is the identity on the underlying regular
functions over every étale chart of `U`. -/
theorem etaleIdealSheafRestrictionIso_hom_apply_coe (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (Z : ClosedSubspaces B S hS X.1) (V : SmallEtale B S hS U.1)
    (s : ToType (((etaleModulePullback.{u, u} B S hS φ hφ).obj
      (definingIdealSheaf B S hS X Z).toSheafOfModules).val.obj (op V))) :
    (((etaleIdealSheafRestrictionIso B S hS φ hφ Z).hom.val.app (op V)).hom s).1 = s.1 :=
  rfl

/-- The inverse of the comparison isomorphism of Stacks 04CO is likewise the identity on the
underlying regular functions over every étale chart of `U`. -/
theorem etaleIdealSheafRestrictionIso_inv_apply_coe (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (Z : ClosedSubspaces B S hS X.1) (V : SmallEtale B S hS U.1)
    (s : ToType ((definingIdealSheaf B S hS U (⟨Z.1.preimage φ.hom,
      isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
      ClosedSubspaces B S hS U.1)).toSheafOfModules.val.obj (op V))) :
    (((etaleIdealSheafRestrictionIso B S hS φ hφ Z).inv.val.app (op V)).hom s).1 = s.1 :=
  rfl

/-- **The identifications of ideal sheaves compose.**  For étale morphisms `ψ : V ⟶ U` and
`φ : U ⟶ X` with étale composite, restricting `𝓘_Z` along `φ` and then along `ψ` and identifying
at each stage is the same as restricting along `ψ ≫ φ` in one step and identifying once, the two
iterated restrictions being compared by `AlgebraicGeometry.Space.etaleModulePullbackComp`.

This is the step-three ingredient of the functoriality in the étale source of Stacks 04CO.  It
holds on the nose: the two closed subspaces `ψ⁻¹(φ⁻¹(Z))` and `(ψ ≫ φ)⁻¹(Z)` are equal, all
three identifications are the identity on underlying regular functions, and
`AlgebraicGeometry.Space.etaleModulePullbackComp` is likewise the identity on sections by
`AlgebraicGeometry.Space.etaleModulePullbackComp_hom_app_val_app`. -/
theorem etaleIdealSheafRestrictionIso_comp {V : AlgebraicSpaces B S hS} (ψ : V ⟶ U) (φ : U ⟶ X)
    (hψ : IsEtale B S hS ψ.hom) (hφ : IsEtale B S hS φ.hom)
    (hψφ : IsEtale B S hS (ψ ≫ φ).hom) (Z : ClosedSubspaces B S hS X.1) :
    (etaleModulePullback.{u, u} B S hS ψ hψ).map
          (etaleIdealSheafRestrictionIso B S hS φ hφ Z).hom ≫
        (etaleIdealSheafRestrictionIso B S hS ψ hψ (⟨Z.1.preimage φ.hom,
          isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
          ClosedSubspaces B S hS U.1)).hom =
      (etaleModulePullbackComp B S hS ψ φ hψ hφ hψφ).hom.app
          (definingIdealSheaf B S hS X Z).toSheafOfModules ≫
        (etaleIdealSheafRestrictionIso B S hS (ψ ≫ φ) hψφ Z).hom :=
  rfl

end AlgebraicGeometry.Space

end
