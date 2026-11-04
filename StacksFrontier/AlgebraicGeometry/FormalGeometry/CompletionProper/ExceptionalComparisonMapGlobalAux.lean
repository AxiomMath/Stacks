module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ExceptionalComparisonMapFormalAux
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The theorem on formal functions for Stacks 088B over an arbitrary Noetherian base

Let `f : X ⟶ Y` be a proper morphism onto a Noetherian scheme, let `𝒥 ⊆ 𝒪_Y` be a quasi-coherent
sheaf of ideals, write `ℐ = 𝒥.comap f`, and let `𝓕` be a coherent `𝒪_X`-module. The comparison
morphism of inverse systems

`c : (f_*𝓕)^ ⟶ f_*(𝓕^)`,     `c_n : (f_*𝓕) / 𝒥 ⁿ⁺¹ (f_*𝓕) ⟶ f_*(𝓕 / ℐ ⁿ⁺¹𝓕)`

of `StacksDraft.AlgebraicGeometry.FormalGeometry.CompletionProper`
`.ExceptionalComparisonMapPushforwardAux` is the map Stacks 088B wants to be an isomorphism on
inverse limits. `.ExceptionalComparisonMapFormalAux` proves this **over an affine base**, in the
form of an isomorphism on the limits of the modules of global sections. **This file globalises
that statement**: `limMap c` is an isomorphism of `𝒪_Y`-modules over an arbitrary Noetherian
base.

Invertibility of a morphism of sheaves of modules is local, and the affine opens of `Y` form a
basis of its topology, so `Stacks.Coherent.isIso_limMap_of_isIso_affineSections` reduces the
statement to the limit of the sections over each affine open `U ⊆ Y`. Over such a `U` the
statement is the theorem on formal functions for the restriction of `f` over `U`, and the whole
work of this file is to run the argument of the affine case over `U` rather than over `⊤`:

* the sections over `U` of the limit of the completion of `f_*𝓕` are the `𝒥(U)`-adic completion
  of `Γ(U, f_*𝓕)`, which is `Stacks.Algebraization.completionSectionsEquiv` — already stated for
  an arbitrary affine open; and
* the limit of the sections `Γ(U, f_*(𝓕 / ℐ ⁿ𝓕)) = Γ(f⁻¹U, 𝓕 / ℐ ⁿ𝓕)` is the `𝒥(U)`-adic
  completion of `Γ(f⁻¹U, 𝓕)`, which is the theorem on formal functions
  [Stacks, Tag 02OC] in degree zero **for the open subscheme `f⁻¹U` over `Spec Γ(Y, U)`**.

The second input is the content of this file. `Stacks.Coherent.preimageToSpec` is the structure
morphism `f⁻¹U ⟶ Spec Γ(Y, U)`; it is proper, because it is the restriction `f ∣_ U` followed by
the identification of `U` with the spectrum of its functions
(`AlgebraicGeometry.IsAffineOpen.isoSpec`), and the ideal sheaf that the theorem on formal
functions attaches to the ideal `𝒥(U)` along it is the inverse-image ideal sheaf `ℐ|_(f⁻¹U)`
(`Stacks.Coherent.baseIdealSheaf_preimageToSpec`). Its degree-zero cohomology over the base of a
restricted module is `Γ(U, f_*-)` (`Stacks.Coherent.preimageSectionsEquiv`), and the terms of the
completion restrict to the terms of the completion of the restriction
(`Stacks.Algebraization.restrictIdealPowerQuotientIso`). With those three identifications the
proof of the affine case applies verbatim.

## Main definitions

* `Stacks.Coherent.preimageToSpec` — the structure morphism of the preimage of an affine open
  `U` over the spectrum of the ring of functions on `U`.
* `Stacks.Coherent.preimageSectionsAddEquiv` and `Stacks.Coherent.preimageSectionsEquiv` — the
  sections over `⊤` of the restriction of a module to `f⁻¹U`, identified with the sections over
  `U` of its direct image, additively and then as `Γ(Y, U)`-modules through degree-zero
  cohomology over the base.
* `Stacks.Coherent.cohomologyOverBaseEquivOfIso` — degree-zero cohomology over the base,
  transported along an isomorphism of modules.

## Main results

* `Stacks.Coherent.baseRingHom_preimageToSpec`, `Stacks.Coherent.appTop_preimageToSpec` and
  `Stacks.Coherent.baseRingHom_comp_map` — the ring map through which the functions on `U` act
  on the preimage of `U`, in the three forms the three uses need.
* `Stacks.Coherent.baseIdealSheaf_preimageToSpec` — the ideal sheaf attached to `𝒥(U)` along
  that structure morphism is the inverse-image ideal sheaf.
* `Stacks.Coherent.preimageSectionsEquiv_naturality` — the identification of sections is natural
  in the module.
* `Stacks.Coherent.restrictIdealPowerQuotientIso_drop` — the identification of the restricted
  ideal-power quotients is compatible with the exponent-lowering maps of the tower.
* `Stacks.Coherent.exists_cohomologyTowerEquiv_affineOpen` — [Stacks, Tag 02OC] in degree zero
  for `f⁻¹U` over `Spec Γ(Y, U)`.
* `Stacks.Coherent.exists_pushforwardCompletionSectionsEquiv_affineOpen` — **the theorem on
  formal functions as a statement about sections over `U`**: the `𝒥(U)`-adic completion of
  `Γ(U, f_*𝓕)` is the limit of the sections over `U` of the direct images of the terms of the
  completion of `𝓕`.
* `Stacks.Coherent.isIso_limMap_affineSections_pushforwardCompletionComparison_affineOpen` — the
  comparison map of Stacks 088B is an isomorphism on the limits of the sections over any affine
  open of the base.
* `Stacks.Coherent.isIso_limMap_pushforwardCompletionComparison` — **the theorem on formal
  functions for the comparison map of Stacks 088B over an arbitrary Noetherian base.**

## Implementation notes

`Stacks.Coherent.preimageToSpec` is built as `(f⁻¹U).toSpecΓ ≫ Spec.map (f.app U)` rather than as
`f ∣_ U` followed by `AlgebraicGeometry.IsAffineOpen.isoSpec`: in that shape its map on global
functions is `AlgebraicGeometry.Scheme.ΓSpecIso_naturality` away from
`f.app U ≫ (f⁻¹U).topIso.inv`, which is the form the module structures need, while
`AlgebraicGeometry.Scheme.Opens.toSpecΓ_naturality` identifies it with the other shape, which is
the form properness comes from.

`Γ((f⁻¹U).toScheme, W)` and `Γ(X, (f⁻¹U).ι ''ᵁ W)` are definitionally equal, and so are
`Γ(f_*M, U)` and `Γ(M, f⁻¹U)`, but the two spellings of a scalar action are not
interchangeable for `rw`: the module structure on the sections of a restriction goes through
`(ι.appIso W).inv`, whose definition the module system does not expose, so the unfolding
`AlgebraicGeometry.Scheme.Opens.ι_appIso` has to be performed by hand. Every scalar action is
therefore moved across the identification by the official lemmas
`AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_hom_apply` and
`AlgebraicGeometry.Scheme.Modules.map_smul`, and the comparison of sections is assembled as an
`AddEquiv` first (`Stacks.Coherent.preimageSectionsAddEquiv`), where all types are at the
restricted spelling, and only then promoted to a linear equivalence; this keeps the one step
that mixes the spellings — the equality of the two ring maps — inside a single `exact`.

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf`, and the two
presentations carry separately declared instances, so a `rw` by a lemma stated at one spelling
does not fire on a goal at the other. Both
`Stacks.Algebraization.cokernel_π_comp_restrictIdealPowerQuotientIso` and
`Stacks.Algebraization.idealPowerQuotientDrop_π` are needed here, and they are stated at the two
different spellings; the former is restated by a `have` at the spelling the goal uses, as in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/ExceptionalComparisonMapFormalAux`
`.lean`, and used by `exact` rather than rewritten.

The appLE calculus of `AlgebraicGeometry.Scheme.Hom.comp_appLE` reuses the inequality proof of
the composite for the factor, so its output is not type-correct at the transparency a rewrite
motive is built at and `AlgebraicGeometry.Scheme.Opens.ι_appLE` can never fire afterwards;
`Stacks.Coherent.appLE_ι_comp` therefore decomposes the composite with
`AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE`, whose inequality proofs are supplied here.

No Stacks attribute is attached: the tags 02OC and 088B are registered elsewhere, and
the statement proved here is one input of Stacks 088B rather than that tag's own claim.

## References

* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Coherent

section Preimage

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.affineOpens)

/-- The structure morphism of the preimage of an affine open `U` over the spectrum of the ring
of functions on `U`. -/
public def preimageToSpec : (f ⁻¹ᵁ U.1).toScheme ⟶ Spec (.of (Γ(Y, U.1) : Type u)) :=
  (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (f.app U.1)

/-- The structure morphism is the restriction of `f` over `U` followed by the identification of
`U` with the spectrum of its functions. -/
public lemma preimageToSpec_eq :
    preimageToSpec f U = (f ∣_ U.1) ≫ U.2.isoSpec.hom :=
  (Scheme.Opens.toSpecΓ_naturality f U.1).trans
    (congrArg ((f ∣_ U.1) ≫ ·) U.2.isoSpec_hom.symm)

/-- The preimage of an affine open under a proper morphism is proper over the spectrum of the
ring of functions on that open. -/
public instance isProper_preimageToSpec [IsProper f] : IsProper (preimageToSpec f U) := by
  rw [preimageToSpec_eq]
  exact MorphismProperty.RespectsIso.postcomp (P := @IsProper) U.2.isoSpec.hom (f ∣_ U.1)
    inferInstance

/-- **The ring map through which the functions on `U` act on the preimage of `U`**: the map on
sections of `f` over `U`, followed by the identification of the functions on `f ⁻¹ᵁ U` with the
functions on the open subscheme it defines. -/
public lemma baseRingHom_preimageToSpec :
    (Scheme.ΓSpecIso Γ(Y, U.1)).inv ≫ (preimageToSpec f U).appTop =
      f.app U.1 ≫ (f ⁻¹ᵁ U.1).topIso.inv := by
  rw [preimageToSpec, Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop,
    Scheme.ΓSpecIso_naturality_assoc]
  show (Scheme.ΓSpecIso Γ(Y, U.1)).inv ≫ (Scheme.ΓSpecIso Γ(Y, U.1)).hom ≫
      f.app U.1 ≫ (f ⁻¹ᵁ U.1).topIso.inv = _
  rw [Iso.inv_hom_id_assoc]

/-- The structure map, through the restriction of `f` over `U`. -/
public lemma appTop_preimageToSpec :
    (Scheme.ΓSpecIso Γ(Y, U.1)).inv ≫ (preimageToSpec f U).appTop =
      U.1.topIso.inv ≫ (f ∣_ U.1).appTop := by
  rw [preimageToSpec_eq, Scheme.Hom.comp_appTop, U.2.isoSpec_hom_appTop, ← Category.assoc,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The ring map of the structure morphism, read through the identification of the functions on
the open subscheme `f ⁻¹ᵁ U` with the sections of `𝒪_X` over `f ⁻¹ᵁ U`. -/
public lemma topIso_hom_baseRingHom_preimageToSpec (a : Γ(Y, U.1)) :
    (f ⁻¹ᵁ U.1).topIso.hom (Stacks.Cohomology.FormalFunctions.baseRingHom
        (Γ(Y, U.1) : Type u) (preimageToSpec f U) a) = f.app U.1 a := by
  show (f ⁻¹ᵁ U.1).topIso.hom
      (((Scheme.ΓSpecIso Γ(Y, U.1)).inv ≫ (preimageToSpec f U).appTop).hom a) = _
  rw [baseRingHom_preimageToSpec]
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]

/-- Transporting sections along an equality of opens, in both directions, is the identity. -/
public lemma map_eqToHom_op_map_eqToHom_op (N : X.Modules) {W W' : X.Opens} (h : W = W')
    (h' : W' = W) (z : Γ(N, W)) :
    N.presheaf.map (eqToHom h).op (N.presheaf.map (eqToHom h').op z) = z := by
  subst h
  simp

/-- The scalar action on the sections of a restriction to an open subscheme is the action on the
sections over the image of that open, the two rings of functions being identified by
`AlgebraicGeometry.Scheme.Opens.ι_appIso`. -/
public lemma restrictAppIso_hom_smul (N : X.Modules)
    (r : Γ((f ⁻¹ᵁ U.1).toScheme, (⊤ : (f ⁻¹ᵁ U.1).toScheme.Opens)))
    (y : Γ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj N,
      (⊤ : (f ⁻¹ᵁ U.1).toScheme.Opens))) :
    (N.restrictAppIso (f ⁻¹ᵁ U.1).ι ⊤).hom (r • y) =
      ((f ⁻¹ᵁ U.1).ι.appIso ⊤).inv r • (N.restrictAppIso (f ⁻¹ᵁ U.1).ι ⊤).hom y :=
  Scheme.Modules.smul_restrictAppIso_hom_apply (f ⁻¹ᵁ U.1).ι N ⊤ r y

/-- The identification of the functions on the open subscheme with the sections of `𝒪_X` over
the open is the identity on elements. -/
public lemma appIso_inv_apply (r : Γ((f ⁻¹ᵁ U.1).toScheme, (⊤ : (f ⁻¹ᵁ U.1).toScheme.Opens))) :
    ((f ⁻¹ᵁ U.1).ι.appIso ⊤).inv r = r := by
  rw [Scheme.Opens.ι_appIso, Iso.refl_inv]
  exact CategoryTheory.id_apply r

/-- The ring map of the structure morphism, read through both identifications of the functions
on the open subscheme `f ⁻¹ᵁ U` with the sections of `𝒪_X` over `f ⁻¹ᵁ U`. -/
public lemma map_appIso_inv_baseRingHom (a : Γ(Y, U.1)) :
    X.presheaf.map (eqToHom ((f ⁻¹ᵁ U.1).ι_image_top).symm).op
        (((f ⁻¹ᵁ U.1).ι.appIso ⊤).inv (Stacks.Cohomology.FormalFunctions.baseRingHom
          (Γ(Y, U.1) : Type u) (preimageToSpec f U) a)) = f.app U.1 a :=
  (congrArg (X.presheaf.map (eqToHom ((f ⁻¹ᵁ U.1).ι_image_top).symm).op)
      (appIso_inv_apply f U _)).trans (topIso_hom_baseRingHom_preimageToSpec f U a)

/-- **The sections of a restriction to the preimage of `U`, as the sections of the direct image
over `U`.** -/
public def preimageSectionsAddEquiv (N : X.Modules) :
    Γ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj N,
        (⊤ : (f ⁻¹ᵁ U.1).toScheme.Opens)) ≃+ Γ(N, f ⁻¹ᵁ U.1) where
  toFun z := N.presheaf.map (eqToHom ((f ⁻¹ᵁ U.1).ι_image_top).symm).op
    ((N.restrictAppIso (f ⁻¹ᵁ U.1).ι ⊤).hom z)
  invFun w := (N.restrictAppIso (f ⁻¹ᵁ U.1).ι ⊤).inv
    (N.presheaf.map (eqToHom ((f ⁻¹ᵁ U.1).ι_image_top)).op w)
  map_add' z w := by
    dsimp only
    rw [map_add, map_add]
  left_inv z := by
    dsimp only
    rw [map_eqToHom_op_map_eqToHom_op, Iso.hom_inv_id_apply]
  right_inv w := by
    dsimp only
    rw [Iso.inv_hom_id_apply, map_eqToHom_op_map_eqToHom_op]

/-- The computation of `Stacks.Coherent.preimageSectionsAddEquiv` on a scalar multiple. -/
public lemma preimageSectionsAddEquiv_smul (N : X.Modules) (a : Γ(Y, U.1))
    (z : Γ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj N,
      (⊤ : (f ⁻¹ᵁ U.1).toScheme.Opens))) :
    preimageSectionsAddEquiv f U N (Stacks.Cohomology.FormalFunctions.baseRingHom
        (Γ(Y, U.1) : Type u) (preimageToSpec f U) a • z) =
      f.app U.1 a • preimageSectionsAddEquiv f U N z := by
  show N.presheaf.map (eqToHom ((f ⁻¹ᵁ U.1).ι_image_top).symm).op
      ((N.restrictAppIso (f ⁻¹ᵁ U.1).ι ⊤).hom (_ • z)) = _
  rw [restrictAppIso_hom_smul, Scheme.Modules.map_smul, map_appIso_inv_baseRingHom]
  rfl

/-- **Degree-zero cohomology over the base of the preimage of an affine open is the module of
sections of the direct image over that open.** -/
public def preimageSectionsEquiv (N : X.Modules) :
    Stacks.Cohomology.FormalFunctions.cohomologyOverBase (Γ(Y, U.1) : Type u)
        (preimageToSpec f U) 0
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj N) ≃ₗ[Γ(Y, U.1)]
      (Stacks.Algebraization.affineSectionFunctor U).obj ((Scheme.Modules.pushforward f).obj N) :=
  letI e := ((Stacks.Cohomology.FormalFunctions.moduleGlobalSectionsRightDerivedZeroIso
    (f ⁻¹ᵁ U.1).toScheme).app
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj N)).toLinearEquiv
  letI φ := e.toAddEquiv.trans (preimageSectionsAddEquiv f U N)
  { toFun := φ
    map_add' := φ.map_add
    invFun := φ.symm
    left_inv := φ.left_inv
    right_inv := φ.right_inv
    map_smul' := fun a x => by
      refine Eq.trans (congrArg (preimageSectionsAddEquiv f U N)
        (e.map_smul (Stacks.Cohomology.FormalFunctions.baseRingHom
          (Γ(Y, U.1) : Type u) (preimageToSpec f U) a) x)) ?_
      exact preimageSectionsAddEquiv_smul f U N a (e x) }

/-- The restriction to an open subscheme acts on sections as the morphism itself. -/
public lemma restrictAppIso_hom_app {N M : X.Modules} (φ : N ⟶ M)
    (z : Γ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj N,
      (⊤ : (f ⁻¹ᵁ U.1).toScheme.Opens))) :
    (M.restrictAppIso (f ⁻¹ᵁ U.1).ι ⊤).hom
        (((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).map φ).app ⊤ z) =
      φ.app ((f ⁻¹ᵁ U.1).ι ''ᵁ ⊤) ((N.restrictAppIso (f ⁻¹ᵁ U.1).ι ⊤).hom z) :=
  rfl

/-- `Stacks.Coherent.preimageSectionsAddEquiv` is natural in the module. -/
public lemma preimageSectionsAddEquiv_app {N M : X.Modules} (φ : N ⟶ M)
    (z : Γ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj N,
      (⊤ : (f ⁻¹ᵁ U.1).toScheme.Opens))) :
    preimageSectionsAddEquiv f U M
        (((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).map φ).app ⊤ z) =
      ((Scheme.Modules.pushforward f).map φ).app U.1
        (preimageSectionsAddEquiv f U N z) := by
  show M.presheaf.map (eqToHom ((f ⁻¹ᵁ U.1).ι_image_top).symm).op
      ((M.restrictAppIso (f ⁻¹ᵁ U.1).ι ⊤).hom _) = _
  rw [restrictAppIso_hom_app]
  have h := congr($(φ.mapPresheaf.naturality
    (eqToHom ((f ⁻¹ᵁ U.1).ι_image_top).symm).op) ((N.restrictAppIso (f ⁻¹ᵁ U.1).ι ⊤).hom z))
  simp only [Scheme.Modules.mapPresheaf_app, ConcreteCategory.comp_apply] at h
  exact h.symm

/-- **`Stacks.Coherent.preimageSectionsEquiv` is natural in the module.** -/
public lemma preimageSectionsEquiv_naturality {N M : X.Modules} (φ : N ⟶ M)
    (x : Stacks.Cohomology.FormalFunctions.cohomologyOverBase (Γ(Y, U.1) : Type u)
      (preimageToSpec f U) 0 ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj N)) :
    preimageSectionsEquiv f U M
        ((Stacks.Cohomology.FormalFunctions.cohomologyOverBaseMap (Γ(Y, U.1) : Type u)
          (preimageToSpec f U) 0
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).map φ)).hom x) =
      ((Stacks.Algebraization.affineSectionFunctor U).map
        ((Scheme.Modules.pushforward f).map φ)).hom (preimageSectionsEquiv f U N x) := by
  have h := congr($((Stacks.Cohomology.FormalFunctions.moduleGlobalSectionsRightDerivedZeroIso
    (f ⁻¹ᵁ U.1).toScheme).hom.naturality
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).map φ)) x)
  simp only at h
  refine Eq.trans (congrArg (preimageSectionsAddEquiv f U M) h) ?_
  exact preimageSectionsAddEquiv_app f U φ _

/-- The map on sections of the composite `f ⁻¹ᵁ U ⟶ X ⟶ Y` over an open of the preimage. -/
public lemma appLE_ι_comp (W : (f ⁻¹ᵁ U.1).toScheme.Opens) :
    ((f ⁻¹ᵁ U.1).ι ≫ f).appLE U.1 W (by simp) =
      f.appLE U.1 ((f ⁻¹ᵁ U.1).ι ''ᵁ W) ((f ⁻¹ᵁ U.1).ι_image_le W) := by
  rw [← Scheme.Hom.appLE_comp_appLE (f ⁻¹ᵁ U.1).ι f U.1 (f ⁻¹ᵁ U.1) W le_rfl (by simp),
    Scheme.Opens.ι_appLE]
  exact Scheme.Hom.appLE_map f _ _

/-- The structure map followed by restriction to an open of the preimage is the map on sections
of `f` over `U`. -/
public lemma baseRingHom_comp_map (W : (f ⁻¹ᵁ U.1).toScheme.Opens) :
    ((Scheme.ΓSpecIso Γ(Y, U.1)).inv ≫ (preimageToSpec f U).appTop) ≫
        (f ⁻¹ᵁ U.1).toScheme.presheaf.map (homOfLE (le_top (a := W))).op =
      ((f ⁻¹ᵁ U.1).ι ≫ f).appLE U.1 W (by simp) := by
  have h1 : (f ∣_ U.1).appTop ≫
        (f ⁻¹ᵁ U.1).toScheme.presheaf.map (homOfLE (le_top (a := W))).op =
      (f ∣_ U.1).appLE ⊤ W
        (le_top.trans (le_of_eq ((f ∣_ U.1).preimage_top).symm)) := rfl
  have h2 := morphismRestrict_appLE f U.1 ⊤ W
    (le_top.trans (le_of_eq ((f ∣_ U.1).preimage_top).symm))
  rw [appTop_preimageToSpec, Category.assoc, h1, h2, Scheme.Opens.topIso_inv, appLE_ι_comp]
  exact Scheme.Hom.map_appLE f _ _

/-- **The ideal sheaf that the theorem on formal functions attaches to the ideal of `𝒥` on `U`
is the inverse-image ideal sheaf on the preimage of `U`.** -/
public lemma baseIdealSheaf_preimageToSpec (J : Y.IdealSheafData) :
    Stacks.Cohomology.FormalFunctions.baseIdealSheaf (Γ(Y, U.1) : Type u) (J.ideal U)
        (preimageToSpec f U) = (J.comap f).comap (f ⁻¹ᵁ U.1).ι := by
  refine Scheme.IdealSheafData.ext (funext fun W => ?_)
  rw [Stacks.Cohomology.FormalFunctions.baseIdealSheaf_ideal,
    Stacks.Cohomology.FormalFunctions.baseIdeal, Ideal.map_map,
    ← Scheme.IdealSheafData.comap_comp,
    Stacks.IdealSheaf.ideal_comap_appLE J ((f ⁻¹ᵁ U.1).ι ≫ f) U W (by simp)]
  exact congrArg (fun φ : Γ(Y, U.1) ⟶ Γ((f ⁻¹ᵁ U.1).toScheme, W.1) =>
    Ideal.map φ.hom (J.ideal U)) (baseRingHom_comp_map f U W.1)

end Preimage

/-! ### Restriction of the tower of ideal-power quotients -/

/-- **The identification of the restricted ideal-power quotients is compatible with the
exponent-lowering maps.** Both composites agree after the quotient projection, which is an
epimorphism. -/
public lemma restrictIdealPowerQuotientIso_drop {X Z : Scheme.{u}} (g : Z ⟶ X)
    [IsOpenImmersion g] (I : X.IdealSheafData) {m n : ℕ} (h : m ≤ n) (M : X.Modules)
    [M.IsQuasicoherent] :
    Stacks.Algebraization.idealPowerQuotientDrop (I.comap g) h
          ((Scheme.Modules.restrictFunctor g).obj M) ≫
        (Stacks.Algebraization.restrictIdealPowerQuotientIso g I m M).hom =
      (Stacks.Algebraization.restrictIdealPowerQuotientIso g I n M).hom ≫
        (Scheme.Modules.restrictFunctor g).map
          (Stacks.Algebraization.idealPowerQuotientDrop I h M) := by
  have : Epi (cokernel.π (C := Z.Modules)
      (Stacks.Algebraization.idealPowerMultiple (I.comap g) n
        ((Scheme.Modules.restrictFunctor g).obj M)).ι) :=
    Stacks.Algebraization.epi_cokernel_π_submodule_ι _
  have key : ∀ k : ℕ, cokernel.π (C := Z.Modules)
        (Stacks.Algebraization.idealPowerMultiple (I.comap g) k
          ((Scheme.Modules.restrictFunctor g).obj M)).ι ≫
        (Stacks.Algebraization.restrictIdealPowerQuotientIso g I k M).hom =
      (Scheme.Modules.restrictFunctor g).map (cokernel.π (C := X.Modules)
        (Stacks.Algebraization.idealPowerMultiple I k M).ι) := fun k =>
    Stacks.Algebraization.cokernel_π_comp_restrictIdealPowerQuotientIso g I k M
  refine (cancel_epi (C := Z.Modules) (cokernel.π (C := Z.Modules)
    (Stacks.Algebraization.idealPowerMultiple (I.comap g) n
      ((Scheme.Modules.restrictFunctor g).obj M)).ι)).1 ?_
  rw [← Category.assoc, ← Category.assoc, Stacks.Algebraization.idealPowerQuotientDrop_π,
    key m, key n, ← Functor.map_comp, Stacks.Algebraization.idealPowerQuotientDrop_π]

/-! ### The theorem on formal functions over the preimage of an affine open -/

/-- **The theorem on formal functions in degree zero over the preimage of an affine open**, in
the tower form. The ideal sheaf of the statement is the inverse-image ideal sheaf restricted to
the preimage, by `Stacks.Coherent.baseIdealSheaf_preimageToSpec`. -/
public lemma exists_cohomologyTowerEquiv_affineOpen {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (J : Y.IdealSheafData) (U : Y.affineOpens) (F : X.Modules)
    [F.IsCoherent] :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∃ e : AdicCompletion (J.ideal U)
          (Stacks.Cohomology.FormalFunctions.cohomologyOverBase (Γ(Y, U.1) : Type u)
            (preimageToSpec f U) 0
            ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj F)) ≃ₗ[Γ(Y, U.1)]
          Stacks.IntertwinedFiltration.towerLimit
            (fun n => Stacks.Cohomology.FormalFunctions.cohomologyOverBase
              (Γ(Y, U.1) : Type u) (preimageToSpec f U) 0
              (Stacks.Algebraization.idealPowerQuotient
                ((J.comap f).comap (f ⁻¹ᵁ U.1).ι) n
                ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj F)))
            (fun _ _ h => (Stacks.Cohomology.FormalFunctions.cohomologyOverBaseMap
              (Γ(Y, U.1) : Type u) (preimageToSpec f U) 0
              (Stacks.Algebraization.idealPowerQuotientDrop
                ((J.comap f).comap (f ⁻¹ᵁ U.1).ι) h
                ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj F))).hom),
      ∀ (n : ℕ) (x : Stacks.Cohomology.FormalFunctions.cohomologyOverBase
          (Γ(Y, U.1) : Type u) (preimageToSpec f U) 0
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj F)),
        Stacks.IntertwinedFiltration.towerLimit.proj n (e (AdicCompletion.of _ _ x)) =
          (Stacks.Cohomology.FormalFunctions.cohomologyOverBaseMap (Γ(Y, U.1) : Type u)
            (preimageToSpec f U) 0
            (cokernel.π (C := (f ⁻¹ᵁ U.1).toScheme.Modules)
              (Stacks.Algebraization.idealPowerMultiple
                ((J.comap f).comap (f ⁻¹ᵁ U.1).ι) n
                ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj F)).ι)).hom x := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNoetherianRing (Γ(Y, U.1) : Type u) :=
    IsLocallyNoetherian.component_noetherian U
  have : ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj F).IsCoherent :=
    Stacks.Algebraization.isCoherent_restrict_of_isOpenImmersion _ F
  rw [show (J.comap f).comap (f ⁻¹ᵁ U.1).ι =
      Stacks.Cohomology.FormalFunctions.baseIdealSheaf (Γ(Y, U.1) : Type u) (J.ideal U)
        (preimageToSpec f U) from (baseIdealSheaf_preimageToSpec f U J).symm]
  obtain ⟨c, e, he⟩ := Stacks.Cohomology.FormalFunctions.exists_formalFunctionsEquiv_of_02O8
    (Γ(Y, U.1) : Type u) (preimageToSpec f U) (isProper_preimageToSpec f U) (J.ideal U)
    ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj F)
    (AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent ‹_›) 0
    Stacks.FormalFunctions.isReesFinite_cohomologyIdealPowerSystem
  exact ⟨e, he⟩



/-! ### Cohomology over the base along an isomorphism of modules -/

/-- An isomorphism of modules induces an `A`-linear isomorphism of their degree-zero cohomology
over the base. -/
public def cohomologyOverBaseEquivOfIso {Z : Scheme.{u}} (A : Type u) [CommRing A]
    (g : Z ⟶ Spec (.of A)) {N M : Z.Modules} (α : N ≅ M) :
    Stacks.Cohomology.FormalFunctions.cohomologyOverBase A g 0 N ≃ₗ[A]
      Stacks.Cohomology.FormalFunctions.cohomologyOverBase A g 0 M :=
  ((ModuleCat.restrictScalars (Stacks.Cohomology.FormalFunctions.baseRingHom A g)).mapIso
    (((AlgebraicGeometry.moduleGlobalSections Z).rightDerived 0).mapIso α)).toLinearEquiv

/-- `Stacks.Coherent.cohomologyOverBaseEquivOfIso` is the map on cohomology of the isomorphism. -/
public lemma cohomologyOverBaseEquivOfIso_apply {Z : Scheme.{u}} (A : Type u) [CommRing A]
    (g : Z ⟶ Spec (.of A)) {N M : Z.Modules} (α : N ≅ M)
    (x : Stacks.Cohomology.FormalFunctions.cohomologyOverBase A g 0 N) :
    cohomologyOverBaseEquivOfIso A g α x =
      (Stacks.Cohomology.FormalFunctions.cohomologyOverBaseMap A g 0 α.hom).hom x :=
  rfl

/-- Degree-zero cohomology over the base is functorial: the map of a composite is the
composite of the maps. -/
private lemma cohomologyOverBaseMap_comp_apply {Z : Scheme.{u}} (A : Type u) [CommRing A]
    (g : Z ⟶ Spec (.of A)) {N M P : Z.Modules} (a : N ⟶ M) (b : M ⟶ P)
    (y : Stacks.Cohomology.FormalFunctions.cohomologyOverBase A g 0 N) :
    (Stacks.Cohomology.FormalFunctions.cohomologyOverBaseMap A g 0 b).hom
        ((Stacks.Cohomology.FormalFunctions.cohomologyOverBaseMap A g 0 a).hom y) =
      (Stacks.Cohomology.FormalFunctions.cohomologyOverBaseMap A g 0 (a ≫ b)).hom y := by
  simp only [Stacks.Cohomology.FormalFunctions.cohomologyOverBaseMap, Functor.map_comp]
  rfl

/-- A composite of module maps that equals a map acts on elements as that map. -/
private lemma hom_comp_apply_congr {R : Type*} [Ring R] {L M N : ModuleCat R} {a : L ⟶ M}
    {b : M ⟶ N} {c : L ⟶ N} (h : a ≫ b = c) (x : L) : b.hom (a.hom x) = c.hom x := by
  rw [← h]
  rfl

/-- A functor into modules sends a composite to the composite of the induced linear maps. -/
private lemma map_hom_comp_apply {C : Type*} [Category C] {R : Type*} [Ring R]
    (G : C ⥤ ModuleCat R) {a b c : C} (f : a ⟶ b) (g : b ⟶ c) (x : G.obj a) :
    (G.map g).hom ((G.map f).hom x) = (G.map (f ≫ g)).hom x := by
  rw [G.map_comp]
  rfl

/-! ### The theorem on formal functions as a statement about sections over an affine open -/

/-- **The theorem on formal functions in the form the globalisation of Stacks 088B needs.** The
`𝒥(U)`-adic completion of `Γ(U, f_*𝓕)` is the limit of the sections over `U` of the direct
images of the terms of the completion of `𝓕`, by the comparison assembled from the
projections. -/
public lemma exists_pushforwardCompletionSectionsEquiv_affineOpen
    {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y) [IsProper f]
    (J : Y.IdealSheafData) (U : Y.affineOpens) (F : X.Modules) [F.IsCoherent] :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∃ e : AdicCompletion (J.ideal U)
            ((Stacks.Algebraization.affineSectionFunctor U).obj
              ((Scheme.Modules.pushforward f).obj F)) ≃ₗ[Γ(Y, U.1)]
          (limit (((Stacks.Algebraization.completionFunctor X (J.comap f)).obj
              ⟨F, inferInstance⟩).obj ⋙ Scheme.Modules.pushforward f ⋙
              Stacks.Algebraization.affineSectionFunctor U) : ModuleCat Γ(Y, U.1)),
      ∀ (n : ℕ) (x : (Stacks.Algebraization.affineSectionFunctor U).obj
          ((Scheme.Modules.pushforward f).obj F)),
        (limit.π (((Stacks.Algebraization.completionFunctor X (J.comap f)).obj
              ⟨F, inferInstance⟩).obj ⋙ Scheme.Modules.pushforward f ⋙
            Stacks.Algebraization.affineSectionFunctor U) (op n)).hom
            (e (AdicCompletion.of _ _ x)) =
          ((Stacks.Algebraization.affineSectionFunctor U).map
            ((Scheme.Modules.pushforward f).map
              (Stacks.Algebraization.completionProjection X (J.comap f)
                ⟨F, inferInstance⟩ n))).hom x := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have : ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj F).IsCoherent :=
    Stacks.Algebraization.isCoherent_restrict_of_isOpenImmersion _ F
  obtain ⟨e₀, he₀⟩ := exists_cohomologyTowerEquiv_affineOpen f J U F
  -- the comparison of the `(k + 1)`-st tower term with the `k`-th term of the completion
  have h1 : ∀ (k l : ℕ) (hkl : k ≤ l)
      (y : Stacks.Cohomology.FormalFunctions.cohomologyOverBase (Γ(Y, U.1) : Type u)
        (preimageToSpec f U) 0 (Stacks.Algebraization.idealPowerQuotient
          ((J.comap f).comap (f ⁻¹ᵁ U.1).ι) l
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj F))),
      cohomologyOverBaseEquivOfIso (Γ(Y, U.1) : Type u) (preimageToSpec f U)
          (Stacks.Algebraization.restrictIdealPowerQuotientIso (f ⁻¹ᵁ U.1).ι (J.comap f) k F)
          ((Stacks.Cohomology.FormalFunctions.cohomologyOverBaseMap (Γ(Y, U.1) : Type u)
            (preimageToSpec f U) 0 (Stacks.Algebraization.idealPowerQuotientDrop
              ((J.comap f).comap (f ⁻¹ᵁ U.1).ι) hkl
              ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj F))).hom y) =
        (Stacks.Cohomology.FormalFunctions.cohomologyOverBaseMap (Γ(Y, U.1) : Type u)
          (preimageToSpec f U) 0 ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).map
            (Stacks.Algebraization.idealPowerQuotientDrop (J.comap f) hkl F))).hom
          (cohomologyOverBaseEquivOfIso (Γ(Y, U.1) : Type u) (preimageToSpec f U)
            (Stacks.Algebraization.restrictIdealPowerQuotientIso (f ⁻¹ᵁ U.1).ι
              (J.comap f) l F) y) := by
    intro k l hkl y
    rw [cohomologyOverBaseEquivOfIso_apply, cohomologyOverBaseEquivOfIso_apply,
      cohomologyOverBaseMap_comp_apply, cohomologyOverBaseMap_comp_apply,
      restrictIdealPowerQuotientIso_drop]
  -- the comparison of the `(k + 1)`-st tower term with the quotient projection
  have h2 : ∀ (k : ℕ) (y : Stacks.Cohomology.FormalFunctions.cohomologyOverBase
      (Γ(Y, U.1) : Type u) (preimageToSpec f U) 0
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj F)),
      cohomologyOverBaseEquivOfIso (Γ(Y, U.1) : Type u) (preimageToSpec f U)
          (Stacks.Algebraization.restrictIdealPowerQuotientIso (f ⁻¹ᵁ U.1).ι (J.comap f) k F)
          ((Stacks.Cohomology.FormalFunctions.cohomologyOverBaseMap (Γ(Y, U.1) : Type u)
            (preimageToSpec f U) 0 (cokernel.π (C := (f ⁻¹ᵁ U.1).toScheme.Modules)
              (Stacks.Algebraization.idealPowerMultiple ((J.comap f).comap (f ⁻¹ᵁ U.1).ι) k
                ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj F)).ι)).hom y) =
        (Stacks.Cohomology.FormalFunctions.cohomologyOverBaseMap (Γ(Y, U.1) : Type u)
          (preimageToSpec f U) 0 ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).map
            (cokernel.π (C := X.Modules)
              (Stacks.Algebraization.idealPowerMultiple (J.comap f) k F).ι))).hom y := by
    intro k y
    rw [cohomologyOverBaseEquivOfIso_apply, cohomologyOverBaseMap_comp_apply]
    exact congrArg (fun t => (Stacks.Cohomology.FormalFunctions.cohomologyOverBaseMap
      (Γ(Y, U.1) : Type u) (preimageToSpec f U) 0 t).hom y)
      (Stacks.Algebraization.cokernel_π_comp_restrictIdealPowerQuotientIso _ _ k F)
  have hT : IsTowerTransitive (A := (Γ(Y, U.1) : Type u))
      (P := fun n => Stacks.Cohomology.FormalFunctions.cohomologyOverBase
        (Γ(Y, U.1) : Type u) (preimageToSpec f U) 0
        (Stacks.Algebraization.idealPowerQuotient ((J.comap f).comap (f ⁻¹ᵁ U.1).ι) n
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj F)))
      (fun _ _ h => (Stacks.Cohomology.FormalFunctions.cohomologyOverBaseMap
        (Γ(Y, U.1) : Type u) (preimageToSpec f U) 0
        (Stacks.Algebraization.idealPowerQuotientDrop ((J.comap f).comap (f ⁻¹ᵁ U.1).ι) h
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj F))).hom) := by
    intro m n k h h' x
    dsimp only
    rw [cohomologyOverBaseMap_comp_apply, idealPowerQuotientDrop_comp]
  have hθ : IsShiftCompatible (A := (Γ(Y, U.1) : Type u))
      (P := fun n => Stacks.Cohomology.FormalFunctions.cohomologyOverBase
        (Γ(Y, U.1) : Type u) (preimageToSpec f U) 0
        (Stacks.Algebraization.idealPowerQuotient ((J.comap f).comap (f ⁻¹ᵁ U.1).ι) n
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj F)))
      (fun _ _ h => (Stacks.Cohomology.FormalFunctions.cohomologyOverBaseMap
        (Γ(Y, U.1) : Type u) (preimageToSpec f U) 0
        (Stacks.Algebraization.idealPowerQuotientDrop ((J.comap f).comap (f ⁻¹ᵁ U.1).ι) h
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).obj F))).hom)
      ((((Stacks.Algebraization.completionFunctor X (J.comap f)).obj
          ⟨F, inferInstance⟩).obj ⋙ Scheme.Modules.pushforward f ⋙
        Stacks.Algebraization.affineSectionFunctor U))
      (fun n => ((cohomologyOverBaseEquivOfIso (Γ(Y, U.1) : Type u) (preimageToSpec f U)
            (Stacks.Algebraization.restrictIdealPowerQuotientIso (f ⁻¹ᵁ U.1).ι
              (J.comap f) (n + 1) F)).trans
          (preimageSectionsEquiv f U
            (Stacks.Algebraization.idealPowerQuotient (J.comap f) (n + 1) F))).trans
        ((Stacks.Algebraization.affineSectionFunctor U).mapIso
          ((Scheme.Modules.pushforward f).mapIso
            (completionTermIso (J.comap f) ⟨F, inferInstance⟩ n).symm)).toLinearEquiv) := by
    intro m n h x
    simp only [LinearEquiv.trans_apply]
    rw [h1, preimageSectionsEquiv_naturality]
    refine (map_hom_comp_apply (Stacks.Algebraization.affineSectionFunctor U) _ _ _).trans
      (Eq.trans ?_ (map_hom_comp_apply (Stacks.Algebraization.affineSectionFunctor U) _ _ _).symm)
    simp only [Functor.mapIso_hom, Iso.symm_hom, ← Functor.map_comp,
      completionTermIso_inv_naturality]
  have hofx : ∀ x : (Stacks.Algebraization.affineSectionFunctor U).obj
        ((Scheme.Modules.pushforward f).obj F),
      (((AdicCompletion.congr (J.ideal U) (preimageSectionsEquiv f U F)).restrictScalars
          (Γ(Y, U.1) : Type u)).symm) (AdicCompletion.of _ _ x) =
        AdicCompletion.of _ _ ((preimageSectionsEquiv f U F).symm x) := fun _ => rfl
  refine ⟨(((AdicCompletion.congr (J.ideal U)
      (preimageSectionsEquiv f U F)).restrictScalars
      (Γ(Y, U.1) : Type u)).symm.trans e₀).trans (towerEquivLimitShift hT hθ), fun n x => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hofx x,
    limit_π_towerEquivLimitShift hT hθ n, he₀ (n + 1)]
  simp only [LinearEquiv.trans_apply]
  rw [h2, preimageSectionsEquiv_naturality, (preimageSectionsEquiv f U F).apply_symm_apply]
  refine (map_hom_comp_apply (Stacks.Algebraization.affineSectionFunctor U) _ _ _).trans ?_
  simp only [Functor.mapIso_hom, Iso.symm_hom, ← Functor.map_comp,
    cokernelπ_comp_completionTermIso_inv (J.comap f) ⟨F, inferInstance⟩ n]

/-! ### The comparison map on sections over an affine open of an arbitrary Noetherian base -/

/-- **The theorem on formal functions in the form Stacks 088B needs, over an affine open of an
arbitrary Noetherian base.** The comparison `(f_*𝓕)^ ⟶ f_*(𝓕^)` of
`Stacks.Coherent.pushforwardCompletionComparison` becomes an isomorphism after taking the limit
of the sections over any affine open `U` of the base. -/
public theorem isIso_limMap_affineSections_pushforwardCompletionComparison_affineOpen
    {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y) [IsProper f]
    (J : Y.IdealSheafData) (U : Y.affineOpens) (F : X.Modules) [F.IsCoherent] :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : ((Scheme.Modules.pushforward f).obj F).IsCoherent :=
      AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f F
    IsIso (limMap (Functor.whiskerRight (pushforwardCompletionComparison f J F)
      (Stacks.Algebraization.affineSectionFunctor U))) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : ((Scheme.Modules.pushforward f).obj F).IsCoherent :=
    AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f F
  let : IsNoetherianRing (Γ(Y, U.1) : Type u) :=
    IsLocallyNoetherian.component_noetherian U
  have : PreservesLimit (((Stacks.Algebraization.completionFunctor Y J).obj
      ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩).obj)
      (Stacks.Algebraization.affineSectionFunctor U) :=
    Stacks.Algebraization.affineSectionFunctor_preservesLimit _ _
  obtain ⟨eQ, heQ⟩ := exists_pushforwardCompletionSectionsEquiv_affineOpen f J U F
  obtain ⟨eP, hePπ⟩ : ∃ eP : AdicCompletion (J.ideal U)
        ((Stacks.Algebraization.affineSectionFunctor U).obj
          ((Scheme.Modules.pushforward f).obj F)) ≃ₗ[Γ(Y, U.1)]
      (limit (((Stacks.Algebraization.completionFunctor Y J).obj
          ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩).obj ⋙
        Stacks.Algebraization.affineSectionFunctor U) : ModuleCat Γ(Y, U.1)),
      ∀ (k : ℕᵒᵖ) (s : (Stacks.Algebraization.affineSectionFunctor U).obj
        ((Scheme.Modules.pushforward f).obj F)),
        (limit.π (((Stacks.Algebraization.completionFunctor Y J).obj
            ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩).obj ⋙
          Stacks.Algebraization.affineSectionFunctor U) k).hom
            (eP (AdicCompletion.of _ _ s)) =
          ((Stacks.Algebraization.affineSectionFunctor U).map
            (Stacks.Algebraization.completionProjection Y J
              ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩ k.unop)).hom s := by
    refine ⟨(Stacks.Algebraization.completionSectionsEquiv Y J
        ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩
        U).trans
      (preservesLimitIso (Stacks.Algebraization.affineSectionFunctor U)
        (((Stacks.Algebraization.completionFunctor Y J).obj
          ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩).obj)).toLinearEquiv,
      fun k s => ?_⟩
    refine (hom_comp_apply_congr (preservesLimitIso_hom_π _ _ k) _).trans ?_
    erw [Stacks.Algebraization.completionSectionsEquiv_of, map_hom_comp_apply,
      Stacks.Algebraization.completionToLimit_projection]
  refine isIso_of_adicCompletion_equiv (J.ideal U)
    (IsNoetherian.noetherian _) eP eQ _ fun s => ?_
  refine Concrete.limit_ext _ _ _ fun k => ?_
  refine (hom_comp_apply_congr (limMap_π _ k) _).trans ?_
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, hePπ]
  refine Eq.trans ?_ (heQ k.unop s).symm
  refine (map_hom_comp_apply (Stacks.Algebraization.affineSectionFunctor U) _ _ _).trans ?_
  erw [pushforwardCompletionComponent_π]

/-! ### The theorem on formal functions over an arbitrary Noetherian base -/

/-- **The theorem on formal functions for the comparison map of Stacks 088B over an arbitrary
Noetherian base.** For a proper morphism `f : X ⟶ Y` onto a Noetherian scheme, a quasi-coherent
sheaf of ideals `𝒥` on `Y` and a coherent `𝒪_X`-module `𝓕`, the comparison morphism of inverse
systems `(f_*𝓕)^ ⟶ f_*(𝓕^)` of `Stacks.Coherent.pushforwardCompletionComparison` induces an
isomorphism on inverse limits.

Invertibility of a morphism of sheaves of modules is checked on the sections over the affine
opens of `Y`, which form a basis of the topology
(`Stacks.Coherent.isIso_limMap_of_isIso_affineSections`), and over an affine open the statement
is the theorem on formal functions for the restriction of `f` over that open
(`Stacks.Coherent.isIso_limMap_affineSections_pushforwardCompletionComparison_affineOpen`). -/
@[ega "III 4.1.5" "partial"]
public theorem isIso_limMap_pushforwardCompletionComparison
    {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y) [IsProper f]
    (J : Y.IdealSheafData) (F : X.Modules) [F.IsCoherent] :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : ((Scheme.Modules.pushforward f).obj F).IsCoherent :=
      AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f F
    IsIso (limMap (pushforwardCompletionComparison f J F)) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : ((Scheme.Modules.pushforward f).obj F).IsCoherent :=
    AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f F
  exact isIso_limMap_of_isIso_affineSections (pushforwardCompletionComparison f J F)
    fun U => isIso_limMap_affineSections_pushforwardCompletionComparison_affineOpen f J U F

end Stacks.Coherent

end
