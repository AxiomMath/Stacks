module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.CompactOpenInduction.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeMayerVietoris.Basic

/-!
# Quasi-coherence of the direct image along a quasi-compact quasi-separated morphism

Let `f : X ⟶ S` be a quasi-compact quasi-separated morphism of schemes. This file proves that
`f_*` carries quasi-coherent `𝒪_X`-modules to quasi-coherent `𝒪_S`-modules, which is
[Stacks, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC).

The proof is the one of the source. The statement is local on `S`, so one may assume `S` affine;
then `X` is quasi-compact and quasi-separated, and the property

`P W := f_* j_{W,*} j_W^* F` is quasi-coherent

of an open `W` of `X` is established for every quasi-compact open by the induction principle
[Stacks, Tag 08DR] (`Stacks.AlgebraicGeometry.CompactOpenInduction.of_isCompact`), whose
inductive step is exactly degree-`0` relative Mayer–Vietoris:

* for `W` affine open, `W.ι ≫ f` is a morphism of affine schemes, so `P W` is
  [Stacks, Tag 02KG];
* for the union step, `j_{U ⊔ V,*} j_{U ⊔ V}^* F` is the kernel of the difference of the two
  restrictions on `j_{U,*} j_U^* F ⊞ j_{V,*} j_V^* F`
  (`Stacks.AlgebraicGeometry.RelativeMayerVietoris.mayerVietorisIso`), and `f_*` is a right
  adjoint, hence preserves that kernel and the biproduct; quasi-coherence is stable under
  biproducts and kernels.

Taking `W = ⊤` gives `f_* F` up to the isomorphism `F ≅ j_{⊤,*} j_⊤^* F`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeMayerVietoris.isQuasicoherent_biprod`: a biproduct of two
  quasi-coherent modules is quasi-coherent.
* `Stacks.AlgebraicGeometry.RelativeMayerVietoris.topPushRestrictIso`: `F ≅ j_{⊤,*} j_⊤^* F`.
* `Stacks.AlgebraicGeometry.RelativeMayerVietoris.isQuasicoherent_pushforward_sup`: the
  Mayer–Vietoris step.
* `Stacks.AlgebraicGeometry.RelativeMayerVietoris.isQuasicoherent_pushforward_of_isAffine`:
  [Stacks, Tag 01LC] over an affine base.
* `Stacks.AlgebraicGeometry.RelativeMayerVietoris.pushforward_isQuasicoherent`:
  **[Stacks, Tag 01LC]**, the direct image of a quasi-coherent module along a quasi-compact
  quasi-separated morphism is quasi-coherent.

## Implementation notes

Quasi-coherence is a class, and the closure properties used here are instances. Hypotheses that
arrive as ordinary proofs are therefore reinstalled with `letI` immediately before the term that
needs them, rather than being left as `have`s in the context, because an instance in the local
context is not always consulted at the head of a goal whose type is a different spelling of the
same category.

`CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts` is not a global
instance in Mathlib; it is installed locally here, which is what makes
`CategoryTheory.Functor.mapBiprod` available for `f_*`.

## References

* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.RelativeMayerVietoris

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

/-! ### Closure properties with the hypotheses as plain proofs -/

/-- A biproduct of two quasi-coherent modules is quasi-coherent: the biproduct is the coproduct,
and quasi-coherence is stable under colimits. -/
theorem isQuasicoherent_biprod {Y : Scheme.{u}} (M N : Y.Modules) (hM : M.IsQuasicoherent)
    (hN : N.IsQuasicoherent) : (M ⊞ N).IsQuasicoherent := by
  have h : ∀ k : Discrete WalkingPair, ((pair M N).obj k).IsQuasicoherent := by
    rintro ⟨_ | _⟩
    · exact hM
    · exact hN
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso (biprod.isoCoprod M N).symm
    (QuasicoherentColimits.isQuasicoherent_colimit (pair M N) h)

/-- A kernel of a morphism of quasi-coherent modules is quasi-coherent, with the hypotheses taken
as plain proofs. -/
theorem isQuasicoherent_kernel' {Y : Scheme.{u}} {M N : Y.Modules} (φ : M ⟶ N)
    (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent) : (kernel φ).IsQuasicoherent :=
  let := hM
  let := hN
  QcohLimits.isQuasicoherent_kernel φ

/-! ### The whole space -/

variable {X S : Scheme.{u}}

/-- The unit of the restriction–pushforward adjunction at the open `⊤` is an isomorphism: on
sections over `T` it is the restriction map of `F` along `T = ⊤ ⊓ T`. -/
instance isIso_unit_top (F : X.Modules) :
    IsIso ((Scheme.Modules.restrictAdjunction (⊤ : X.Opens).ι).unit.app F) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro T
  have he : T ≤ (⊤ : X.Opens).ι ''ᵁ ((⊤ : X.Opens).ι ⁻¹ᵁ T) := by
    rw [ι_image_preimage]
    exact le_of_eq (top_inf_eq T).symm
  rw [Scheme.Modules.restrictAdjunction_unit_app_app]
  dsimp only [Scheme.Modules.pushforward_obj_obj, Scheme.Modules.restrict_obj, Functor.comp_obj,
    Functor.id_obj]
  exact ⟨F.presheaf.map (homOfLE he).op, by rw [← Functor.map_comp]; exact F.presheaf.map_id _,
    by rw [← Functor.map_comp]; exact F.presheaf.map_id _⟩

/-- `F ≅ j_{⊤,*} j_⊤^* F`: restricting to the whole space and pushing back changes nothing. -/
noncomputable def topPushRestrictIso (F : X.Modules) : F ≅ pushRestrict F ⊤ :=
  asIso ((Scheme.Modules.restrictAdjunction (⊤ : X.Opens).ι).unit.app F)

/-! ### The Mayer–Vietoris step -/

/-- **The inductive step of [Stacks, Tag 01LC].** If `f_* j_{W,*} j_W^* F` is quasi-coherent for
`W = U`, `W = V` and `W = U ⊓ V`, then it is quasi-coherent for `W = U ⊔ V`.

Degree-`0` relative Mayer–Vietoris presents `j_{U ⊔ V,*} j_{U ⊔ V}^* F` as a kernel; `f_*` is a
right adjoint, so it preserves that kernel, and it is additive, so it carries the biproduct to a
biproduct. -/
theorem isQuasicoherent_pushforward_sup (f : X ⟶ S) (F : X.Modules) (U V : X.Opens)
    (hU : ((Scheme.Modules.pushforward f).obj (pushRestrict F U)).IsQuasicoherent)
    (hV : ((Scheme.Modules.pushforward f).obj (pushRestrict F V)).IsQuasicoherent)
    (hI : ((Scheme.Modules.pushforward f).obj (pushRestrict F (U ⊓ V))).IsQuasicoherent) :
    ((Scheme.Modules.pushforward f).obj (pushRestrict F (U ⊔ V))).IsQuasicoherent := by
  have hsrc : ((Scheme.Modules.pushforward f).obj
      (pushRestrict F U ⊞ pushRestrict F V)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
      (Functor.mapBiprod (Scheme.Modules.pushforward f) _ _).symm
      (isQuasicoherent_biprod _ _ hU hV)
  have hker : (kernel ((Scheme.Modules.pushforward f).map (mvDiff F U V))).IsQuasicoherent :=
    isQuasicoherent_kernel' _ hsrc hI
  refine (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    (((Scheme.Modules.pushforward f).mapIso (mayerVietorisIso F U V) ≪≫
      PreservesKernel.iso (Scheme.Modules.pushforward f) (mvDiff F U V)).symm) hker

/-! ### The theorem -/

/-- **[Stacks, Tag 01LC] over an affine base.** For `f : X ⟶ S` quasi-compact and quasi-separated
with `S` affine and `F` a quasi-coherent `𝒪_X`-module, `f_* F` is quasi-coherent. -/
theorem isQuasicoherent_pushforward_of_isAffine (f : X ⟶ S) [IsAffine S] [QuasiCompact f]
    [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent := by
  have h₁ : ∀ W : X.Opens, IsAffineOpen W →
      ((Scheme.Modules.pushforward f).obj (pushRestrict F W)).IsQuasicoherent := by
    intro W hW
    have : IsAffine W.toScheme := hW
    have : (F.restrict W.ι).IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_restrictFunctor W.ι F
    exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.pushforwardComp W.ι f).app (F.restrict W.ι)).symm
      (AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom (W.ι ≫ f) (F.restrict W.ι))
  have htop := CompactOpenInduction.top_of_qcqs_over_affine
    (P := fun W => ((Scheme.Modules.pushforward f).obj (pushRestrict F W)).IsQuasicoherent) h₁
    (fun U V _ _ hU hV hI => isQuasicoherent_pushforward_sup f F U V hU hV hI) f
  exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.pushforward f).mapIso (topPushRestrictIso F)).symm htop

/-- **[Stacks, Tag 01LC].** The direct image of a quasi-coherent module along a quasi-compact
quasi-separated morphism of schemes is quasi-coherent.

The statement is local on the target: over an affine open `V` of `S` the restriction of `f_* F` is
the direct image along `f ∣_ V` of the restriction of `F` to `f ⁻¹ᵁ V`, and `f ∣_ V` is again
quasi-compact and quasi-separated with affine target. -/
@[stacks 01LC]
theorem pushforward_isQuasicoherent (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent := by
  refine QuasicoherentColimits.isQuasicoherent_of_restrict_affineOpens _ fun V => ?_
  obtain ⟨V, hV⟩ := V
  have : IsAffine V.toScheme := hV
  have : (F.restrict (f ⁻¹ᵁ V).ι).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor (f ⁻¹ᵁ V).ι F
  exact (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso
    ((AffinePushforward.restrictPushforwardIso f V).app F).symm
    (isQuasicoherent_pushforward_of_isAffine (f ∣_ V) (F.restrict (f ⁻¹ᵁ V).ι))

end Stacks.AlgebraicGeometry.RelativeMayerVietoris

end
