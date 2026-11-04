module

public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Sections of a module over an open, and the two restrictions of scalars that compare them

The module docstring of `StacksFrontier.AlgebraicGeometry.ConormalAffineShape.Shape` records the
one kind of step separating the sheaf-level passage to the affine model from the part (2)
assertions of [Stacks, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3): the tag's statements
are isomorphisms of `Γ(X, V)`-modules, while everything obtained from
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` is an isomorphism of
`Γ(V.toScheme, ⊤)`-modules, and the two rings are identified only by
`AlgebraicGeometry.Scheme.Opens.topIso`, not definitionally. It names two missing
restriction-of-scalars comparisons. This file supplies them.

## Main definitions

* `Stacks.Conormal.CotangentAppIso.sectionsCongr`: for `M : X.Modules` and equal opens
  `V = V'`, the sections over `V` are the restriction of scalars along `X.presheaf.map` of that
  equality of the sections over `V'`.
* `Stacks.Conormal.CotangentAppIso.restrictFunctorSectionsIso`: the sections of
  `(Scheme.Modules.restrictFunctor V.ι).obj M` over an open `W` of `V.toScheme` are the sections
  of `M` over `V.ι ''ᵁ W`, with **no** change of scalars — the two rings are the same and the
  action is the same, because `AlgebraicGeometry.Scheme.Opens.ι_appIso` is `Iso.refl`.
* `Stacks.Conormal.CotangentAppIso.sectionsRestrictTopIso`: **the first comparison.** For
  `M : X.Modules` and an open `V`, the `Γ(X, V)`-module `Γ(M, V)` is the restriction of scalars
  along `V.topIso.inv` of the global sections of `M ∣_ V`.
* `Stacks.Conormal.CotangentAppIso.isoSpecPushforwardTopSectionsIso`: **the second comparison.**
  For an affine open `V` and a module `Q` on `Spec Γ(X, V)`, the restriction of scalars along
  `V.topIso.inv` of the global sections of the pushforward of `Q` along
  `AlgebraicGeometry.IsAffineOpen.isoSpec`'s inverse is
  `AlgebraicGeometry.moduleSpecΓFunctor` of `Q` — which is the form the affine model's answer
  is stated in.

## Main results

* `Stacks.Conormal.CotangentAppIso.pushforward_sections_eq`: the sections of a module
  pushforward over an open **are** the restriction of scalars along `f.app V` of the sections
  over the preimage, by `rfl`.
* `Stacks.Conormal.CotangentAppIso.moduleSpecΓFunctor_obj_eq`: `moduleSpecΓFunctor` **is** the
  restriction of scalars along `(Scheme.ΓSpecIso R).inv` of the global sections, by `rfl`.
* `Stacks.Conormal.CotangentAppIso.sectionsRestrictTopIso_hom_apply`: the underlying map of the
  first comparison is the restriction map of `M` along `V.ι ''ᵁ ⊤ = V`. Its two companions,
  `restrictFunctorSectionsIso_hom_apply` and `isoSpecPushforwardTopSectionsIso_hom_apply`, say
  that the other two comparisons are the identity on sections: only the scalars move.

## Route, and two definitional facts

Both `pushforward_sections_eq` and `moduleSpecΓFunctor_obj_eq` hold by `rfl`. The second of the
two comparisons that `ConormalAffineShape.Shape` records as missing is therefore almost free: it
is `ModuleCat.restrictScalarsComp'App` together with
`AlgebraicGeometry.IsAffineOpen.isoSpec_inv_appTop`, and no transport of sections is involved at
all.

The first comparison is the one with real content, and it is *not* `rfl`: the module structure of
`Γ((Scheme.Modules.restrictFunctor V.ι).obj M, W)` is the restriction of scalars of
`Γ(M, V.ι ''ᵁ W)` along `(V.ι.appIso W).inv`, and at this pin the `inv` field of
`AlgebraicGeometry.Scheme.Hom.appIso` is sealed, so the elaborator reports "definitions were not
unfolded because their definition is not exposed: inv" and the objects are not interchangeable.
What *is* `rfl` is the identification of that module with
`(ModuleCat.restrictScalars ((V.ι.appIso W).inv).hom).obj (Γ(M, V.ι ''ᵁ W))`, keeping `appIso`
abstract. `AlgebraicGeometry.Scheme.Opens.ι_appIso` then rewrites `appIso` to `Iso.refl` inside
that expression, and `ModuleCat.restrictScalarsId'App` discharges it. So the sealed field is
routed around rather than unfolded, and `Scheme.Modules.restrictAppIso` — the bridge
`ConormalAffineShape.Shape` proposes — is not needed: it is an isomorphism of abelian groups
(`Γ(M, U)` for a sheaf of modules is `AddCommGrp`-valued), and the content here is the module
structure, which that isomorphism cannot see.

## Universe situation

A single universe `u`: `Scheme.{u}` with `SheafOfModules.{u}`, as everywhere in this cluster.

## What is not done

* **No clause of [Stacks, Tag 01R3] is discharged and no `stacks` attribute is attached.** Every
  statement here is about an arbitrary sheaf of modules on an arbitrary scheme; nothing mentions
  immersions, ideal sheaves, the conormal sheaf or `Ideal.Cotangent`.
* **Nothing for a general open immersion.** `restrictFunctorSectionsIso` is stated for
  `AlgebraicGeometry.Scheme.Opens.ι` only, since that is where `ι_appIso = Iso.refl` holds; for a
  general open immersion the change of scalars along `appIso` is genuinely there.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Conormal.CotangentAppIso

variable {X : Scheme.{u}}

/-- **The sections of a module pushforward are a restriction of scalars**, on the nose: over an
open `V` of the target they are the sections over `f ⁻¹ᵁ V`, with the scalars of `V` acting
through `f.app V`. -/
theorem pushforward_sections_eq {A B : Scheme.{u}} (f : A ⟶ B) (P : A.Modules) (V : B.Opens) :
    ((Scheme.Modules.pushforward f).obj P).val.obj (.op V) =
      (ModuleCat.restrictScalars (f.app V).hom).obj (P.val.obj (.op (f ⁻¹ᵁ V))) :=
  rfl

/-- **The global-sections functor on an affine scheme is a restriction of scalars**, on the nose:
`AlgebraicGeometry.moduleSpecΓFunctor` is the sections over `⊤` with `R` acting through
`AlgebraicGeometry.Scheme.ΓSpecIso`. -/
theorem moduleSpecΓFunctor_obj_eq {R : CommRingCat.{u}} (N : (Spec R).Modules) :
    (moduleSpecΓFunctor (R := R)).obj N =
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).obj (N.val.obj (.op ⊤)) :=
  rfl

/-- **Transport of sections along an equality of opens.** For equal opens `V = V'` of `X`, the
`Γ(X, V)`-module of sections of `M` over `V` is the restriction of scalars, along the restriction
map of the structure sheaf, of the sections over `V'`.

The equality is discharged by `subst`, after which the restriction map of the structure sheaf is
the identity and `ModuleCat.restrictScalarsId'App` applies. It cannot be done by `rw`, since the
equality of opens occurs in the type of the module being restricted. -/
noncomputable def sectionsCongr (M : X.Modules) {V V' : X.Opens} (h : V = V') :
    M.val.obj (.op V) ≅
      (ModuleCat.restrictScalars (X.presheaf.map (eqToHom h.symm).op).hom).obj
        (M.val.obj (.op V')) := by
  subst h
  exact (ModuleCat.restrictScalarsId'App _ (by simp; rfl) _).symm

/-- `sectionsCongr` is the restriction map of `M` along the equality of opens. -/
theorem sectionsCongr_hom_apply (M : X.Modules) {V V' : X.Opens} (h : V = V')
    (x : M.val.obj (.op V)) :
    (sectionsCongr M h).hom.hom x = (M.val.map (eqToHom h.symm).op).hom x := by
  subst h
  rw [show (eqToHom (rfl : V = V)).op = 𝟙 (Opposite.op V) from rfl,
    PresheafOfModules.map_id]
  rfl

/-- **The sections of a restriction to an open subscheme, with no change of scalars.** For
`M : X.Modules`, an open `V` of `X` and an open `W` of `V.toScheme`, the sections of
`(Scheme.Modules.restrictFunctor V.ι).obj M` over `W` are the sections of `M` over `V.ι ''ᵁ W`.

The two rings `Γ(V.toScheme, W)` and `Γ(X, V.ι ''ᵁ W)` are the same, and the two module
structures differ by `(V.ι.appIso W).inv`, which is the identity by
`AlgebraicGeometry.Scheme.Opens.ι_appIso`. The `inv` field of
`AlgebraicGeometry.Scheme.Hom.appIso` is sealed at this pin, so the identification is *not*
`rfl`; what is `rfl` is the presentation of the left-hand side as
`ModuleCat.restrictScalars ((V.ι.appIso W).inv).hom` of the right-hand side, with `appIso`
left abstract, and the rewrite happens inside that. -/
noncomputable def restrictFunctorSectionsIso (M : X.Modules) (V : X.Opens)
    (W : V.toScheme.Opens) :
    ((Scheme.Modules.restrictFunctor V.ι).obj M).val.obj (.op W) ≅
      M.val.obj (.op (V.ι ''ᵁ W)) :=
  ModuleCat.restrictScalarsId'App ((V.ι.appIso W).inv).hom (by simp; rfl) _

/-- `restrictFunctorSectionsIso` is the identity on sections. -/
theorem restrictFunctorSectionsIso_hom_apply (M : X.Modules) (V : X.Opens)
    (W : V.toScheme.Opens)
    (x : ((Scheme.Modules.restrictFunctor V.ι).obj M).val.obj (.op W)) :
    (restrictFunctorSectionsIso M V W).hom.hom x = x :=
  rfl

/-- **The first restriction-of-scalars comparison.** For `M : X.Modules` and an open `V` of `X`,
the `Γ(X, V)`-module of sections of `M` over `V` is the restriction of scalars along
`AlgebraicGeometry.Scheme.Opens.topIso`'s inverse of the *global* sections of the restriction of
`M` to `V`.

This is the module-level analogue of `AlgebraicGeometry.Scheme.Opens.topIso`, and the comparison
`StacksFrontier.AlgebraicGeometry.ConormalAffineShape.Shape` records as absent. Its underlying
map is the restriction map of `M` along `V.ι ''ᵁ ⊤ = V`, and its linearity is the semilinearity
of that restriction map, which is built into `PresheafOfModules.map`. -/
noncomputable def sectionsRestrictTopIso (M : X.Modules) (V : X.Opens) :
    M.val.obj (.op V) ≅
      (ModuleCat.restrictScalars V.topIso.inv.hom).obj
        (((Scheme.Modules.restrictFunctor V.ι).obj M).val.obj (.op ⊤)) :=
  sectionsCongr M V.ι_image_top.symm ≪≫
    (ModuleCat.restrictScalars V.topIso.inv.hom).mapIso
      (restrictFunctorSectionsIso M V ⊤).symm

/-- **The underlying map of the first comparison is the restriction map of `M` along
`V.ι ''ᵁ ⊤ = V`**, the second factor of `sectionsRestrictTopIso` being the identity on
sections. This is what a generator formula has to be pushed through. -/
theorem sectionsRestrictTopIso_hom_apply (M : X.Modules) (V : X.Opens)
    (x : M.val.obj (.op V)) :
    (sectionsRestrictTopIso M V).hom.hom x =
      (M.val.map (eqToHom V.ι_image_top).op).hom x :=
  sectionsCongr_hom_apply M V.ι_image_top.symm x

/-- **The second restriction-of-scalars comparison.** For an affine open `V` of `X` and a module
`Q` on `Spec Γ(X, V)`, the restriction of scalars along `V.topIso.inv` of the global sections of
the pushforward of `Q` along `(IsAffineOpen.isoSpec hV).inv` is
`AlgebraicGeometry.moduleSpecΓFunctor` of `Q`.

The right-hand side is the shape in which `Stacks.Conormal.AffineModel` states its answer, so
this is the step that carries an affine computation on `Spec Γ(X, V)` into `ModuleCat Γ(X, V)`.
No transport of sections occurs: `hV.isoSpec.inv ⁻¹ᵁ ⊤ = ⊤` by `rfl`, and the content is the
equality of ring maps `V.topIso.inv ≫ hV.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(X, V)).inv`,
which is `AlgebraicGeometry.IsAffineOpen.isoSpec_inv_appTop`. -/
noncomputable def isoSpecPushforwardTopSectionsIso (V : X.Opens) (hV : IsAffineOpen V)
    (Q : (Spec Γ(X, V)).Modules) :
    (ModuleCat.restrictScalars V.topIso.inv.hom).obj
        (((Scheme.Modules.pushforward hV.isoSpec.inv).obj Q).val.obj (.op ⊤)) ≅
      (moduleSpecΓFunctor (R := Γ(X, V))).obj Q :=
  (ModuleCat.restrictScalarsComp'App V.topIso.inv.hom hV.isoSpec.inv.appTop.hom
    (Scheme.ΓSpecIso Γ(X, V)).inv.hom (by
      have h : V.topIso.inv ≫ hV.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(X, V)).inv := by
        rw [hV.isoSpec_inv_appTop, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      rw [← CommRingCat.hom_comp, h]) _).symm

/-- `isoSpecPushforwardTopSectionsIso` is the identity on sections: only the scalars move. -/
theorem isoSpecPushforwardTopSectionsIso_hom_apply (V : X.Opens) (hV : IsAffineOpen V)
    (Q : (Spec Γ(X, V)).Modules)
    (x : ((Scheme.Modules.pushforward hV.isoSpec.inv).obj Q).val.obj (.op ⊤)) :
    (isoSpecPushforwardTopSectionsIso V hV Q).hom.hom x = x :=
  rfl

end Stacks.Conormal.CotangentAppIso

end
