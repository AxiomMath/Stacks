module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Sections of a module on an open, through the inclusion of the open subscheme

An open `V` of a scheme `Y` is a scheme in its own right, and a module `M` on `Y` restricts
along the inclusion `V.ι` to a module on it. The global sections of that restriction are the
sections of `M` over `V`: the two carriers are the same abelian group and the two scalar actions
agree. This file packages that identification as an isomorphism of abelian groups, as a
`Γ(Y, V)`-linear map, and as an isomorphism of `Γ(Y, V)`-modules — the analogue, for the
inclusion of an open subscheme, of `AlgebraicGeometry.affineSectionsIso` and
`AlgebraicGeometry.affineSectionsLinearEquiv` for `AlgebraicGeometry.IsAffineOpen.fromSpec`.

## Main definitions

* `AlgebraicGeometry.openSectionsIso`: the isomorphism `Γ(M.restrict V.ι, ⊤) ≅ Γ(M, V)` of
  abelian groups.
* `AlgebraicGeometry.openSectionsLinearMap`: the same map as a `Γ(Y, V)`-linear map, the scalars
  on its source restricted along `AlgebraicGeometry.Scheme.Opens.topIso`.
* `AlgebraicGeometry.openSectionsModuleIso`: the same map as an isomorphism of
  `Γ(Y, V)`-modules.

## Main results

* `AlgebraicGeometry.smul_restrictAppIso_top_hom`: the `Γ(V, ⊤)`-action that
  `AlgebraicGeometry.Scheme.Modules.restrictFunctor` produces and the `Γ(Y, V.ι ''ᵁ ⊤)`-action
  of `M` are the same action, the scalar carried over unchanged with no ring map intervening.
* `AlgebraicGeometry.openSectionsIso_hom_smul`: `openSectionsIso` is semilinear over
  `AlgebraicGeometry.Scheme.Opens.topIso`.

## Implementation notes

`Γ(V, ⊤)` is `Γ(Y, V.ι ''ᵁ ⊤)` and `Γ(M.restrict V.ι, ⊤)` is `Γ(M, V.ι ''ᵁ ⊤)` definitionally,
`AlgebraicGeometry.Scheme.Modules.restrictAppIso` is `Iso.refl`, and evaluation at the top open
adds nothing. Those `rfl`s do not survive instance synthesis, which does not unfold
`AlgebraicGeometry.Scheme.Opens.toScheme`: a scalar of `Γ(V, ⊤)` acting on `Γ(M, V.ι ''ᵁ ⊤)` has
to be put in the second spelling by hand, which is what the `show` in
`smul_restrictAppIso_top_hom` does.

The `Γ(V, ⊤)`-action on `Γ(M.restrict V.ι, ⊤)` is restriction of scalars along
`(V.ι.appIso ⊤).inv`, and that this is the identity is propositional rather than definitional,
since `AlgebraicGeometry.Scheme.Hom.appIso` is built from `CategoryTheory.inv`, hence from
`Classical.choose`. There is no `algebraMap` between the two actions, so the map out of these
sections is linear rather than semilinear.

The one genuine transport is the equality `V.ι ''ᵁ ⊤ = V` of opens
(`AlgebraicGeometry.Scheme.Opens.ι_image_top`), which makes `openSectionsIso` semilinear over
the comparison `AlgebraicGeometry.Scheme.Opens.topIso` of the two rings of functions;
`openSectionsLinearMap` absorbs that comparison into a restriction of scalars.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

variable {Y : Scheme.{u}} (M : Y.Modules) (V : Y.Opens)

/-- The two scalar actions on the global sections of a restriction agree: a function on the open
subscheme `V` acts on the global sections of `M.restrict V.ι` as the same function on `Y`, read
on `V.ι ''ᵁ ⊤`, acts on the sections of `M` there. -/
theorem smul_restrictAppIso_top_hom (r : Γ(↑V, ⊤)) (x : Γ(M.restrict V.ι, ⊤)) :
    (M.restrictAppIso V.ι ⊤).hom (r • x) =
      (show Γ(Y, V.ι ''ᵁ ⊤) from r) • (M.restrictAppIso V.ι ⊤).hom x := by
  rw [Scheme.Modules.smul_restrictAppIso_hom_apply, Scheme.Opens.ι_appIso]
  rfl

/-- Evaluating a sheaf of modules at the top open adds nothing to the module structure that
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` produces: the two are the same object of the
same category of modules, by `rfl`. -/
theorem evaluation_top_restrictFunctor_obj :
    (SheafOfModules.evaluation (↑V : Scheme).ringCatSheaf (op ⊤)).obj
        ((Scheme.Modules.restrictFunctor V.ι).obj M) =
      ModuleCat.of Γ(↑V, ⊤) Γ(M.restrict V.ι, ⊤) :=
  rfl

/-- The global sections of the restriction of `M` to the open subscheme `V` agree with the
sections of `M` over `V`, as abelian groups. -/
def openSectionsIso : Γ(M.restrict V.ι, ⊤) ≅ Γ(M, V) :=
  M.restrictAppIso V.ι ⊤ ≪≫ M.presheaf.mapIso (eqToIso V.ι_image_top).symm.op

/-- `AlgebraicGeometry.openSectionsIso` on elements: restrict along `V.ι`, then transport along
the equality `V.ι ''ᵁ ⊤ = V` of opens. -/
theorem openSectionsIso_hom_apply (x : Γ(M.restrict V.ι, ⊤)) :
    (openSectionsIso M V).hom x =
      M.presheaf.map (eqToHom V.ι_image_top.symm).op ((M.restrictAppIso V.ι ⊤).hom x) := by
  simp [openSectionsIso]

/-- `AlgebraicGeometry.openSectionsIso` is semilinear over
`AlgebraicGeometry.Scheme.Opens.topIso`: the two actions agree on the nose, and the comparison
of rings is the transport along the equality `V.ι ''ᵁ ⊤ = V` of opens. -/
theorem openSectionsIso_hom_smul (r : Γ(↑V, ⊤)) (x : Γ(M.restrict V.ι, ⊤)) :
    (openSectionsIso M V).hom (r • x) =
      (Scheme.Opens.topIso V).hom r • (openSectionsIso M V).hom x := by
  rw [openSectionsIso_hom_apply, openSectionsIso_hom_apply, smul_restrictAppIso_top_hom,
    M.map_smul]
  rfl

/-- `AlgebraicGeometry.Scheme.Opens.topIso` is an isomorphism, read on elements. -/
theorem topIso_hom_inv_apply (r : Γ(Y, V)) :
    (Scheme.Opens.topIso V).hom ((Scheme.Opens.topIso V).inv r) = r := by
  rw [← CommRingCat.comp_apply, (Scheme.Opens.topIso V).inv_hom_id, CommRingCat.id_apply]

/-- A `Γ(Y, V)`-linear map out of the global sections of a restriction: the global sections of
`M.restrict V.ι`, with their scalars restricted along `AlgebraicGeometry.Scheme.Opens.topIso`,
map `Γ(Y, V)`-linearly onto the sections of `M` over `V`. -/
def openSectionsLinearMap :
    (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).obj
        (ModuleCat.of Γ(↑V, ⊤) Γ(M.restrict V.ι, ⊤)) →ₗ[Γ(Y, V)] Γ(M, V) where
  toFun := ConcreteCategory.hom (openSectionsIso M V).hom
  map_add' := map_add (ConcreteCategory.hom (openSectionsIso M V).hom)
  map_smul' r x := by
    rw [ModuleCat.restrictScalars.smul_def, openSectionsIso_hom_smul, topIso_hom_inv_apply,
      RingHom.id_apply]

/-- `AlgebraicGeometry.openSectionsLinearMap` is `AlgebraicGeometry.openSectionsIso` on
elements. -/
@[simp]
theorem openSectionsLinearMap_apply (x : Γ(M.restrict V.ι, ⊤)) :
    openSectionsLinearMap M V x = (openSectionsIso M V).hom x :=
  rfl

/-- The global sections of a restriction, as a module over the functions on the open: the global
sections of `M.restrict V.ι`, with their scalars restricted along
`AlgebraicGeometry.Scheme.Opens.topIso`, are the sections of `M` over `V`. -/
def openSectionsModuleIso :
    (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).obj
        (ModuleCat.of Γ(↑V, ⊤) Γ(M.restrict V.ι, ⊤)) ≅
      ModuleCat.of Γ(Y, V) Γ(M, V) :=
  LinearEquiv.toModuleIso
    (X₁ := (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).obj
      (ModuleCat.of Γ(↑V, ⊤) Γ(M.restrict V.ι, ⊤)))
    (X₂ := ModuleCat.of Γ(Y, V) Γ(M, V))
    (LinearEquiv.ofBijective (openSectionsLinearMap M V)
      (ConcreteCategory.bijective_of_isIso (openSectionsIso M V).hom))

/-- `AlgebraicGeometry.openSectionsModuleIso` is `AlgebraicGeometry.openSectionsIso` on
elements. -/
@[simp]
theorem openSectionsModuleIso_hom_apply (x : Γ(M.restrict V.ι, ⊤)) :
    (openSectionsModuleIso M V).hom x = (openSectionsIso M V).hom x :=
  rfl

end AlgebraicGeometry

end
