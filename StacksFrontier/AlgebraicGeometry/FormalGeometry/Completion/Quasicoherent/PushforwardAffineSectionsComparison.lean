module

public import StacksFrontier.AlgebraicGeometry.CotangentAppIso.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.HigherDirectImageLocalScalar
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.AffineBaseSectionsNatural
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology of an open preimage as sections of a higher direct image over an affine open

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes, let `V ⊆ Y` be an
affine open and write `j : f⁻¹(V) ⟶ X` for the inclusion. For a quasi-coherent module `H` on
`f⁻¹(V)` this file produces an additive equivalence

`H ᵖ(f⁻¹(V), H) ≃+ Γ(V, R ᵖ f_*(j_*H))`,

natural in `H`.

## Main definitions

* `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.cohomologyExtendSectionsEquiv`: the
  comparison.

## Main results

* `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.cohomologyExtendSectionsEquiv_naturality`:
  the comparison commutes with a morphism of modules on `f⁻¹(V)`. This is what a consumer needs:
  it moves the comparison along the multiplication maps of a Rees algebra, which are morphisms
  of modules on `f⁻¹(V)` and not restrictions of morphisms on `X`.

## Implementation notes

The comparison is the composite of three isomorphisms.

* [Stacks, Tag 01XK] over the affine base `V`, for the restricted morphism `f ∣_ V`, in
  natural-number degrees and in its natural form
  (`Stacks.AlgebraicGeometry.HigherDirectImageQcoh.sectionsRightDerivedPushforwardNatIso`). This
  identifies `H ᵖ(f⁻¹(V), H)` with the global sections of `R ᵖ (f ∣_ V)_*H`.
* `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.extendRestrictIso`, which identifies
  `R ᵖ (f ∣_ V)_*` with `𝒢 ↦ (R ᵖ f_*(j_*𝒢))|_V`. This is [Stacks, Tag 01E5].
* `Stacks.Conormal.CotangentAppIso.sectionsRestrictTopIso`, the global sections of a restriction
  to `V` read as the sections over `V`; its underlying map is the restriction map along the
  equality of opens `V.ι ''ᵁ ⊤ = V`, which is the only place that equality intervenes.

**Why the composite is assembled from additive equivalences, with the changes of spelling named.**
The three live in `ModuleCat` over three different rings, so the composite is not a morphism of
modules; and the ends of consecutive factors, while carrying the same addition, do not *spell* it
the same way — one says `ModuleCat.restrictScalars φ |>.obj N`, the next says `N`; one says
`moduleGlobalSections Z |>.obj N`, the next says `N.val.obj (op ⊤)`. Composing the factors as
bare functions and then proving additivity by `map_add` asks the kernel to compare two such
spellings of one addition *at an argument built from a derived functor*, and to do that it
unfolds the derived functor; that does not terminate inside its budget. Naming each change of
spelling as an additive equivalence of two *variables*
(`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.restrictScalarsAddEquiv`,
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.moduleGlobalSectionsAddEquiv`) performs each
comparison once, where there is nothing to unfold, after which every link of the chain matches
its neighbour syntactically and additivity of the composite is `map_add` of a single
`AddEquiv`.

## References

* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 02O9](https://stacks.math.columbia.edu/tag/02O9)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Conormal.CotangentAppIso

universe u

namespace Stacks.AlgebraicGeometry.SchemeHigherDirectImage

/-! ### Reading an isomorphism of modules additively -/

/-- An isomorphism of modules, read as an additive equivalence of the underlying groups.

This is **not** `ModuleCat.Iso.toLinearEquiv` with the scalars forgotten afterwards, and the
difference is the reason it is written out. `ModuleCat.Iso.toLinearEquiv` lands in `≃ₗ[R]`, so
using it here asks for a `Module ↥Γ(Y, V)`-structure on the source of each factor; the sources
are modules over three *different* rings, two of them presented through
`ModuleCat.restrictScalars`, and the instance is not there. Substituting it for the definition
below fails to synthesize that instance and, where it does elaborate, brings back the kernel
timeout this file exists to avoid. Forgetting the scalars at each factor, rather than carrying
them and forgetting at the end, is what makes the chain composable at all. -/
public def addEquivOfModuleCatIso {R : Type u} [Ring R] {M N : ModuleCat.{u} R} (e : M ≅ N) :
    M ≃+ N where
  toFun := e.hom.hom
  invFun := e.inv.hom
  left_inv x := by
    simp
  right_inv x := by
    simp
  map_add' := map_add e.hom.hom

/-- `addEquivOfModuleCatIso e` acts as the underlying map of `e.hom`. -/
@[simp] public theorem addEquivOfModuleCatIso_apply {R : Type u} [Ring R] {M N : ModuleCat.{u} R}
    (e : M ≅ N) (x : M) : addEquivOfModuleCatIso e x = e.hom.hom x := rfl

/-- The inverse of `addEquivOfModuleCatIso e` acts as the underlying map of `e.inv`. -/
@[simp] public theorem addEquivOfModuleCatIso_symm_apply {R : Type u} [Ring R]
    {M N : ModuleCat.{u} R} (e : M ≅ N) (y : N) :
    (addEquivOfModuleCatIso e).symm y = e.inv.hom y := rfl

/-- Two equal morphisms of modules agree on an element. -/
public theorem apply_congr_hom {R : Type u} [Ring R] {M N : ModuleCat.{u} R} {φ ψ : M ⟶ N}
    (h : φ = ψ) (x : M) : φ.hom x = ψ.hom x :=
  congrArg (fun χ : M ⟶ N => χ.hom x) h

/-- A composite of three additive equivalences, on an element. Stated of variable types, so that
the unfolding of `AddEquiv.trans` is performed where there is nothing else to unfold. -/
public theorem addEquiv_trans_trans_apply {A B C D : Type u} [Add A] [Add B]
    [Add C] [Add D] (e₁ : A ≃+ B) (e₂ : B ≃+ C) (e₃ : C ≃+ D) (x : A) :
    (e₁.trans (e₂.trans e₃)) x = e₃ (e₂ (e₁ x)) := rfl

/-- A composite of morphisms of modules, on an element: `ModuleCat.hom_comp` read on `x`.

`ModuleCat.comp_apply` says the same thing through the concrete-category coercion rather than
through `ModuleCat.Hom.hom`. It is restated here, of *variable* modules, because the consumer
below needs the unfolding of the composition performed where the objects are variables: at a
composite of derived functors the kernel does not finish it, and that was one of the three
timeouts this file was stuck on. -/
public theorem comp_apply_hom {R : Type u} [Ring R] {M N P : ModuleCat.{u} R} (φ : M ⟶ N)
    (ψ : N ⟶ P) (x : M) : (φ ≫ ψ).hom x = ψ.hom (φ.hom x) := rfl

/-- **Restriction of scalars does not change the addition.** Stated of a variable module, so
that the comparison of the two spellings is performed here and nowhere else. -/
public def restrictScalarsAddEquiv {R S : Type u} [Ring R] [Ring S] (φ : R →+* S)
    (N : ModuleCat.{u} S) : ((ModuleCat.restrictScalars φ).obj N) ≃+ N :=
  AddEquiv.refl _

/-- `restrictScalarsAddEquiv φ N` is the identity on elements. -/
@[simp] public theorem restrictScalarsAddEquiv_apply {R S : Type u} [Ring R] [Ring S]
    (φ : R →+* S) (N : ModuleCat.{u} S) (x : (ModuleCat.restrictScalars φ).obj N) :
    restrictScalarsAddEquiv φ N x = x := rfl

/-- The inverse of `restrictScalarsAddEquiv φ N` is the identity on elements. -/
@[simp] public theorem restrictScalarsAddEquiv_symm_apply {R S : Type u} [Ring R] [Ring S]
    (φ : R →+* S) (N : ModuleCat.{u} S) (x : N) :
    (restrictScalarsAddEquiv φ N).symm x = x := rfl

/-- **Global sections are the sections over the top open.** Stated of a variable module, for the
same reason as `restrictScalarsAddEquiv`. -/
public def moduleGlobalSectionsAddEquiv (Z : Scheme.{u}) (N : Z.Modules) :
    ((moduleGlobalSections Z).obj N) ≃+ (N.val.obj (op ⊤)) :=
  AddEquiv.refl _

/-- `moduleGlobalSectionsAddEquiv Z N` is the identity on elements. -/
@[simp] public theorem moduleGlobalSectionsAddEquiv_apply (Z : Scheme.{u}) (N : Z.Modules)
    (x : (moduleGlobalSections Z).obj N) : moduleGlobalSectionsAddEquiv Z N x = x := rfl

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (p : ℕ)

/-- The extension to `X` of a module on `f⁻¹(V)`, pushed forward along `f` and derived: the
sheaf on `Y` whose sections over `V` the comparison of this file lands in. -/
public abbrev extendDerived (H : (f ⁻¹ᵁ V).toScheme.Modules) : Y.Modules :=
  ((Scheme.Modules.pushforward f).rightDerived p).obj
    ((Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).obj H)

/-! ### Naturality of the sections of a restriction to an open -/

/-- **The comparison `Γ(M, V) ≅ Γ(M|_V, ⊤)` is natural in `M`.** Both sides are the restriction
map of the ambient module along the equality of opens `V.ι ''ᵁ ⊤ = V`, so this is the naturality
of a morphism of sheaves of modules. -/
public theorem sectionsRestrictTopIso_naturality {M N : Y.Modules} (χ : M ⟶ N)
    (x : M.val.obj (op V)) :
    (sectionsRestrictTopIso N V).hom.hom ((χ.val.app (op V)).hom x) =
      (((Scheme.Modules.restrictFunctor V.ι).map χ).val.app (op ⊤)).hom
        ((sectionsRestrictTopIso M V).hom.hom x) :=
  (sectionsRestrictTopIso_hom_apply N V _).trans
    ((PresheafOfModules.naturality_apply χ.val (eqToHom V.ι_image_top).op x).symm.trans
      (congrArg (fun w : M.val.obj (op (V.ι ''ᵁ ⊤)) => (χ.val.app (op (V.ι ''ᵁ ⊤))).hom w)
        (sectionsRestrictTopIso_hom_apply M V x).symm))

/-- The inverse comparison is natural in `M`, which is the direction the composite below uses. -/
public theorem sectionsRestrictTopIso_inv_naturality {M N : Y.Modules} (χ : M ⟶ N)
    (y : (ModuleCat.restrictScalars V.topIso.inv.hom).obj
      (((Scheme.Modules.restrictFunctor V.ι).obj M).val.obj (op ⊤))) :
    (sectionsRestrictTopIso N V).inv.hom
        ((((Scheme.Modules.restrictFunctor V.ι).map χ).val.app (op ⊤)).hom y) =
      (χ.val.app (op V)).hom ((sectionsRestrictTopIso M V).inv.hom y) := by
  have hy : (sectionsRestrictTopIso M V).hom.hom
      ((sectionsRestrictTopIso M V).inv.hom y) = y :=
    apply_congr_hom (sectionsRestrictTopIso M V).inv_hom_id y
  have hx := sectionsRestrictTopIso_naturality V χ ((sectionsRestrictTopIso M V).inv.hom y)
  refine Eq.trans (congrArg (fun z => (sectionsRestrictTopIso N V).inv.hom
    ((((Scheme.Modules.restrictFunctor V.ι).map χ).val.app (op ⊤)).hom z)) hy.symm) ?_
  refine Eq.trans (congrArg (sectionsRestrictTopIso N V).inv.hom hx.symm) ?_
  exact apply_congr_hom (sectionsRestrictTopIso N V).hom_inv_id
    ((χ.val.app (op V)).hom ((sectionsRestrictTopIso M V).inv.hom y))


/-- **The sections of `M` over `V` as the global sections of `M|_V`**, additively. Stated of a
variable module, so that both changes of spelling — the one across
`ModuleCat.restrictScalars` and the one between `moduleGlobalSections` and the sections over the
top open — are settled here, where there is nothing to unfold. -/
public def sectionsOfRestrictTopEquiv (M : Y.Modules) :
    ((moduleGlobalSections V.toScheme).obj ((Scheme.Modules.restrictFunctor V.ι).obj M)) ≃+
      (M.val.obj (op V)) :=
  (moduleGlobalSectionsAddEquiv V.toScheme ((Scheme.Modules.restrictFunctor V.ι).obj M)).trans
    ((restrictScalarsAddEquiv V.topIso.inv.hom
        (((Scheme.Modules.restrictFunctor V.ι).obj M).val.obj (op ⊤))).symm.trans
      (addEquivOfModuleCatIso (sectionsRestrictTopIso M V)).symm)

/-- `sectionsOfRestrictTopEquiv V M` acts as the inverse of `sectionsRestrictTopIso M V`. -/
public theorem sectionsOfRestrictTopEquiv_apply (M : Y.Modules)
    (w : (moduleGlobalSections V.toScheme).obj ((Scheme.Modules.restrictFunctor V.ι).obj M)) :
    sectionsOfRestrictTopEquiv V M w = (sectionsRestrictTopIso M V).inv.hom w := rfl

/-- `sectionsOfRestrictTopEquiv` is natural in the module. -/
public theorem sectionsOfRestrictTopEquiv_naturality {M N : Y.Modules} (χ : M ⟶ N)
    (w : (moduleGlobalSections V.toScheme).obj ((Scheme.Modules.restrictFunctor V.ι).obj M)) :
    sectionsOfRestrictTopEquiv V N
        ((((moduleGlobalSections V.toScheme).map
          ((Scheme.Modules.restrictFunctor V.ι).map χ)).hom) w) =
      (χ.val.app (op V)).hom (sectionsOfRestrictTopEquiv V M w) := by
  rw [sectionsOfRestrictTopEquiv_apply, sectionsOfRestrictTopEquiv_apply]
  exact sectionsRestrictTopIso_inv_naturality V χ w

section Comparison

variable [QuasiCompact f] [QuasiSeparated f] [IsAffine V.toScheme]

/-- **[Stacks, Tag 01XK] over the affine base `V`**, at a single quasi-coherent module on
`f⁻¹(V)`: cohomology is the global sections of the higher direct image along `f ∣_ V`. -/
@[ega "III 3.4.6" "special case"]
public def affineBaseSectionsIso (H : (f ⁻¹ᵁ V).toScheme.Modules) [H.IsQuasicoherent] :
    (ModuleCat.restrictScalars (f ∣_ V).appTop.hom).obj
        (((moduleGlobalSections (f ⁻¹ᵁ V).toScheme).rightDerived p).obj H) ≅
      (moduleGlobalSections V.toScheme).obj
        (((Scheme.Modules.pushforward (f ∣_ V)).rightDerived p).obj H) :=
  (HigherDirectImageQcoh.sectionsRightDerivedPushforwardNatIso (f ∣_ V) p).app
    ⟨H, inferInstance⟩

/-- **[Stacks, Tag 01E5] on global sections over `V`**: the global sections of `R ᵖ (f ∣_ V)_*H`
are the global sections of the restriction to `V` of `R ᵖ f_*(j_*H)`. -/
public def extendRestrictSectionsIso (H : (f ⁻¹ᵁ V).toScheme.Modules) :
    (moduleGlobalSections V.toScheme).obj
        (((Scheme.Modules.pushforward (f ∣_ V)).rightDerived p).obj H) ≅
      (moduleGlobalSections V.toScheme).obj
        ((Scheme.Modules.restrictFunctor V.ι).obj (extendDerived f V p H)) :=
  (moduleGlobalSections V.toScheme).mapIso ((extendRestrictIso f V p).app H)

/-- **First leg**: cohomology on `f⁻¹(V)` is the global sections of `R ᵖ (f ∣_ V)_*`. -/
public def cohomologyToTopSectionsEquiv (H : (f ⁻¹ᵁ V).toScheme.Modules) [H.IsQuasicoherent] :
    (((moduleGlobalSections (f ⁻¹ᵁ V).toScheme).rightDerived p).obj H) ≃+
      ((moduleGlobalSections V.toScheme).obj
        (((Scheme.Modules.pushforward (f ∣_ V)).rightDerived p).obj H)) :=
  (restrictScalarsAddEquiv (f ∣_ V).appTop.hom
      (((moduleGlobalSections (f ⁻¹ᵁ V).toScheme).rightDerived p).obj H)).symm.trans
    (addEquivOfModuleCatIso (affineBaseSectionsIso f V p H))

/-- The first leg acts as the underlying map of `affineBaseSectionsIso f V p H`. -/
public theorem cohomologyToTopSectionsEquiv_apply (H : (f ⁻¹ᵁ V).toScheme.Modules)
    [H.IsQuasicoherent]
    (z : ((moduleGlobalSections (f ⁻¹ᵁ V).toScheme).rightDerived p).obj H) :
    cohomologyToTopSectionsEquiv f V p H z = (affineBaseSectionsIso f V p H).hom.hom z := rfl

/-- The first leg is natural: this is the naturality of [Stacks, Tag 01XK]. -/
public theorem cohomologyToTopSectionsEquiv_naturality (H H' : (f ⁻¹ᵁ V).toScheme.Modules)
    [H.IsQuasicoherent] [H'.IsQuasicoherent] (ψ : H ⟶ H')
    (z : ((moduleGlobalSections (f ⁻¹ᵁ V).toScheme).rightDerived p).obj H) :
    cohomologyToTopSectionsEquiv f V p H'
        ((((moduleGlobalSections (f ⁻¹ᵁ V).toScheme).rightDerived p).map ψ).hom z) =
      (((moduleGlobalSections V.toScheme).map
        (((Scheme.Modules.pushforward (f ∣_ V)).rightDerived p).map ψ)).hom)
          (cohomologyToTopSectionsEquiv f V p H z) := by
  rw [cohomologyToTopSectionsEquiv_apply, cohomologyToTopSectionsEquiv_apply]
  exact apply_congr_hom
    ((HigherDirectImageQcoh.sectionsRightDerivedPushforwardNatIso (f ∣_ V) p).hom.naturality
      (X := ⟨H, inferInstance⟩) (Y := ⟨H', inferInstance⟩) (ObjectProperty.homMk ψ)) z

omit [QuasiCompact f] [QuasiSeparated f] [IsAffine ↑V] in
/-- The second leg, [Stacks, Tag 01E5] on global sections over `V`, is natural. -/
public theorem extendRestrictSectionsIso_naturality (H H' : (f ⁻¹ᵁ V).toScheme.Modules)
    (ψ : H ⟶ H')
    (y : (moduleGlobalSections V.toScheme).obj
      (((Scheme.Modules.pushforward (f ∣_ V)).rightDerived p).obj H)) :
    (extendRestrictSectionsIso f V p H').hom.hom
        ((((moduleGlobalSections V.toScheme).map
          (((Scheme.Modules.pushforward (f ∣_ V)).rightDerived p).map ψ)).hom) y) =
      (((moduleGlobalSections V.toScheme).map
        ((Scheme.Modules.restrictFunctor V.ι).map
          (((Scheme.Modules.pushforward f).rightDerived p).map
            ((Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).map ψ)))).hom)
        ((extendRestrictSectionsIso f V p H).hom.hom y) :=
  have h : (moduleGlobalSections V.toScheme).map
          (((Scheme.Modules.pushforward (f ∣_ V)).rightDerived p).map ψ) ≫
        (extendRestrictSectionsIso f V p H').hom =
      (extendRestrictSectionsIso f V p H).hom ≫
        (moduleGlobalSections V.toScheme).map
          ((Scheme.Modules.restrictFunctor V.ι).map
            (((Scheme.Modules.pushforward f).rightDerived p).map
              ((Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).map ψ))) :=
    ((moduleGlobalSections V.toScheme).map_comp _ _).symm.trans
      ((congrArg (moduleGlobalSections V.toScheme).map
          ((extendRestrictIso f V p).hom.naturality ψ)).trans
        ((moduleGlobalSections V.toScheme).map_comp _ _))
  (comp_apply_hom _ _ y).symm.trans ((apply_congr_hom h y).trans (comp_apply_hom _ _ y))

/-- **The comparison.** For `V` an affine open of `Y` and `H` a quasi-coherent module on
`f⁻¹(V)`, cohomology in degree `p` is the module of sections over `V` of the `p`-th higher
direct image of the extension of `H` to `X`.

Consecutive legs meet at the *same spelling* of the same module, so the composite is an
`AddEquiv.trans` and nothing in it compares two spellings of one addition. -/
public def cohomologyExtendSectionsEquiv (H : (f ⁻¹ᵁ V).toScheme.Modules) [H.IsQuasicoherent] :
    (((moduleGlobalSections (f ⁻¹ᵁ V).toScheme).rightDerived p).obj H) ≃+
      (extendDerived f V p H).val.obj (op V) :=
  (cohomologyToTopSectionsEquiv f V p H).trans
    ((addEquivOfModuleCatIso (extendRestrictSectionsIso f V p H)).trans
      (sectionsOfRestrictTopEquiv V (extendDerived f V p H)))

/-- The comparison, written out as the composite of its three legs. -/
public theorem cohomologyExtendSectionsEquiv_apply (H : (f ⁻¹ᵁ V).toScheme.Modules)
    [H.IsQuasicoherent]
    (z : ((moduleGlobalSections (f ⁻¹ᵁ V).toScheme).rightDerived p).obj H) :
    cohomologyExtendSectionsEquiv f V p H z =
      sectionsOfRestrictTopEquiv V (extendDerived f V p H)
        ((extendRestrictSectionsIso f V p H).hom.hom
          (cohomologyToTopSectionsEquiv f V p H z)) :=
  (addEquiv_trans_trans_apply (cohomologyToTopSectionsEquiv f V p H)
      (addEquivOfModuleCatIso (extendRestrictSectionsIso f V p H))
      (sectionsOfRestrictTopEquiv V (extendDerived f V p H)) z).trans
    (congrArg (sectionsOfRestrictTopEquiv V (extendDerived f V p H))
      (addEquivOfModuleCatIso_apply (extendRestrictSectionsIso f V p H)
        (cohomologyToTopSectionsEquiv f V p H z)))

/-- **The comparison is natural in the module on `f⁻¹(V)`.** This is what the transport of
[Stacks, Tag 02O8] from an affine chart of the base consumes: the morphisms it moves the
comparison along are the multiplications by local sections of the Rees algebra, which are
morphisms of modules on `f⁻¹(V)` and not restrictions of morphisms on `X`. -/
public theorem cohomologyExtendSectionsEquiv_naturality (H H' : (f ⁻¹ᵁ V).toScheme.Modules)
    [H.IsQuasicoherent] [H'.IsQuasicoherent] (ψ : H ⟶ H')
    (z : ((moduleGlobalSections (f ⁻¹ᵁ V).toScheme).rightDerived p).obj H) :
    cohomologyExtendSectionsEquiv f V p H'
        ((((moduleGlobalSections (f ⁻¹ᵁ V).toScheme).rightDerived p).map ψ).hom z) =
      ((((Scheme.Modules.pushforward f).rightDerived p).map
        ((Scheme.Modules.pushforward (f ⁻¹ᵁ V).ι).map ψ)).val.app (op V)).hom
          (cohomologyExtendSectionsEquiv f V p H z) :=
  by
  rw [cohomologyExtendSectionsEquiv_apply, cohomologyExtendSectionsEquiv_apply,
    cohomologyToTopSectionsEquiv_naturality, extendRestrictSectionsIso_naturality,
    sectionsOfRestrictTopEquiv_naturality]

/-- **The comparison is surjective**, being an equivalence. -/
public theorem cohomologyExtendSectionsEquiv_surjective (H : (f ⁻¹ᵁ V).toScheme.Modules)
    [H.IsQuasicoherent] :
    Function.Surjective (cohomologyExtendSectionsEquiv f V p H) :=
  (cohomologyExtendSectionsEquiv f V p H).surjective

end Comparison

end Stacks.AlgebraicGeometry.SchemeHigherDirectImage

end

end
