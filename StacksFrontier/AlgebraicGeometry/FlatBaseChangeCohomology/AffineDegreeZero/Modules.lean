module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineBaseReduction
public import StacksFrontier.AlgebraicGeometry.SectionsColimit.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineIsoCriterion

/-!
# Flat base change for direct images in degree zero

Let
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
be a *cartesian* square of schemes with `g` flat and `f` quasi-compact and quasi-separated, and
let `ℱ` be a quasi-coherent sheaf of modules on `X`.  This file proves that the canonical
base-change morphism `Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` of the
square, `g^* f_* ℱ ⟶ f'_* (g')^* ℱ`, is an isomorphism at `ℱ`.

## Main results

* `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.pushforwardSquareIso_hom_app_app_top`: the
  canonical identification of the two composite direct images around a commutative square is the
  identity on global sections.
* `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.pushforward_unit_comp_pushforwardSquareIso`:
  the defining property of `baseChangeNatTrans` as a mate, as an equation between morphisms of
  modules on `S`.
* `FlatBaseChangeCohomology.baseChangeNatTrans_app_top_pullbackUnitSections`:
  on global sections, `baseChangeNatTrans` carries the pullback of a section along `g` to the
  pullback of that section along `g'`.
* `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_isAffineBases`:
  for a cartesian square with affine bases, `g` flat, `X` quasi-compact and quasi-separated and
  `ℱ` quasi-coherent, the base-change morphism is invertible at `ℱ`.
* `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat`: for a
  cartesian square with `g` flat, `f` quasi-compact and quasi-separated and `ℱ` quasi-coherent,
  the base-change morphism is invertible at `ℱ`.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.SectionsBaseChange

universe u

namespace Stacks.AlgebraicGeometry.FlatBaseChangeCohomology

/-! ### Two `appLE` identities over the whole space -/

section AppLE

variable {X S : Scheme.{u}}

/-- Over the whole space, `AlgebraicGeometry.Scheme.Hom.appLE` is
`AlgebraicGeometry.Scheme.Hom.app`. -/
theorem appLE_top_eq_app (f : X ⟶ S) :
    Scheme.Hom.appLE f ⊤ ⊤ (le_preimage_top f ⊤) = Scheme.Hom.app f ⊤ :=
  Scheme.Hom.appLE_preimage_self f ⊤

/-- Over the whole space, the identity morphism induces the identity on sections. -/
theorem appLE_top_id (S : Scheme.{u}) :
    Scheme.Hom.appLE (𝟙 S) ⊤ ⊤ (le_preimage_top (𝟙 S) ⊤) = 𝟙 Γ(S, (⊤ : S.Opens)) :=
  (Scheme.Hom.appLE_preimage_self (𝟙 S) ⊤).trans (by simp)

/-- The base module structure `baseModule f F ⊤` on the global sections of a module, obtained by
restricting scalars along `f.appLE ⊤ ⊤`, is the intrinsic `Γ(S, ⊤)`-module structure on the
sections of its direct image. -/
theorem baseModule_eq_instModule (f : X ⟶ S) (F : X.Modules) :
    baseModule f F ⊤ = inferInstanceAs (Module ↑Γ(S, (⊤ : S.Opens))
      ↑Γ((Scheme.Modules.pushforward f).obj F, (⊤ : S.Opens))) :=
  Module.ext (by
    funext r a
    change (Scheme.Hom.appLE f ⊤ ⊤ (le_preimage_top f ⊤)).hom r •
        (show Γ(F, (⊤ : X.Opens)) from a)
      = r • (show Γ((Scheme.Modules.pushforward f).obj F, (⊤ : S.Opens)) from a)
    exact (congrArg (fun t : Γ(S, (⊤ : S.Opens)) ⟶ Γ(X, f ⁻¹ᵁ (⊤ : S.Opens)) =>
        (CommRingCat.Hom.hom t) r • (show Γ(F, f ⁻¹ᵁ (⊤ : S.Opens)) from a))
        (appLE_top_eq_app f)).trans
      (SectionsColimit.pushforward_app_smul f F ⊤ r a))

/-- The base module structure `baseModule (𝟙 S) G ⊤` along the identity is the intrinsic one. -/
theorem baseModule_id_eq_instModule (G : S.Modules) :
    baseModule (𝟙 S) G ⊤ =
      inferInstanceAs (Module ↑Γ(S, (⊤ : S.Opens)) ↑Γ(G, (⊤ : S.Opens))) :=
  baseModule_eq_instModule (𝟙 S) G

end AppLE

/-! ### The base-change morphism on global sections -/

section Normalisation

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {g : S' ⟶ S} {g' : X' ⟶ X}

/-- The canonical identification of the two composite direct images around a commutative
square is the identity on global sections. -/
theorem pushforwardSquareIso_hom_app_app_top (w : g' ≫ f = f' ≫ g) (N : X'.Modules) :
    ((AffinePushforward.pushforwardSquareIso w).hom.app N).app (⊤ : S.Opens) =
      𝟙 Γ((Scheme.Modules.pushforward g' ⋙ Scheme.Modules.pushforward f).obj N,
        (⊤ : S.Opens)) := by
  simp only [AffinePushforward.pushforwardSquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardCongr_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app]
  exact (congrArg (fun t => N.presheaf.map t) (Subsingleton.elim _ (𝟙 _))).trans
    (CategoryTheory.Functor.map_id _ _)

/-- The defining property of the base-change morphism as a mate: pushing the unit of
`(g')^* ⊣ (g')_*` forward along `f` and composing with the identification of the two composite
direct images is the same as the unit of `g^* ⊣ g_*` followed by the direct image along `g` of
the base-change morphism. -/
theorem pushforward_unit_comp_pushforwardSquareIso (w : g' ≫ f = f' ≫ g) (F : X.Modules) :
    (Scheme.Modules.pushforward f).map
        ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F) ≫
      (AffinePushforward.pushforwardSquareIso w).hom.app
        ((Scheme.Modules.pullback g').obj F) =
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        ((Scheme.Modules.pushforward f).obj F) ≫
      (Scheme.Modules.pushforward g).map
        ((AffinePushforward.baseChangeNatTrans w).app F) :=
  CategoryTheory.unit_mateEquiv_symm
    (Scheme.Modules.pullbackPushforwardAdjunction g')
    (Scheme.Modules.pullbackPushforwardAdjunction g)
    (TwoSquare.mk _ _ _ _ (AffinePushforward.pushforwardSquareIso w).hom) F

/-- On global sections the base-change morphism carries the pullback of a section along `g` to
its pullback along `g'`. -/
theorem baseChangeNatTrans_app_top_pullbackUnitSections (w : g' ≫ f = f' ≫ g) (F : X.Modules)
    (a : Γ(F, (⊤ : X.Opens))) :
    (((AffinePushforward.baseChangeNatTrans w).app F).app (⊤ : S'.Opens)).hom
        (pullbackUnitSections g ((Scheme.Modules.pushforward f).obj F) ⊤ a) =
      pullbackUnitSections g' F ⊤ a := by
  have h := congrArg (fun t => ((Scheme.Modules.Hom.app t (⊤ : S.Opens)).hom) a)
    (pushforward_unit_comp_pushforwardSquareIso w F)
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    pushforwardSquareIso_hom_app_app_top w] at h
  exact h.symm

/-- On global sections the base-change morphism carries the pullback of a section along `g` to
its pullback along `g'`, with pullback of sections written
`Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackSectionsHom` at the target open `⊤`. -/
theorem baseChangeNatTrans_app_top_pullbackSectionsHom (w : g' ≫ f = f' ≫ g) (F : X.Modules)
    (a : Γ(F, (⊤ : X.Opens))) :
    (((AffinePushforward.baseChangeNatTrans w).app F).app (⊤ : S'.Opens)).hom
        (pullbackSectionsHom g ((Scheme.Modules.pushforward f).obj F) ⊤ ⊤
          (le_preimage_top g ⊤) a) =
      pullbackSectionsHom g' F ⊤ ⊤ (le_preimage_top g' ⊤) a :=
  (congrArg (fun z => (((AffinePushforward.baseChangeNatTrans w).app F).app
      (⊤ : S'.Opens)).hom z)
    (pullbackSectionsHom_top g ((Scheme.Modules.pushforward f).obj F) a)).trans
    ((baseChangeNatTrans_app_top_pullbackUnitSections w F a).trans
      (pullbackSectionsHom_top g' F a).symm)

end Normalisation

/-! ### The affine case -/

section Affine

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {g : S' ⟶ S} {g' : X' ⟶ X}

/-- Flat base change for direct images in degree zero, over affine bases.  Let
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
be a cartesian square of schemes with `S` and `S'` affine, with `g` flat and with `X`
quasi-compact and quasi-separated, and let `ℱ` be a quasi-coherent sheaf of modules on `X`.
Then the canonical base-change morphism `g^* f_* ℱ ⟶ f'_* (g')^* ℱ` is an isomorphism. -/
theorem isIso_baseChangeNatTrans_of_isAffineBases (H : IsPullback g' f' f g)
    [IsAffine S] [IsAffine S'] [Flat g] [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent] :
    IsIso ((AffinePushforward.baseChangeNatTrans H.w).app F) := by
  have hfqc : QuasiCompact f := quasiCompact_of_compactSpace f
  have hpushF : ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent :=
    AlgebraicGeometry.pushforward_isQuasicoherent f F
  have hsrc : ((Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback g).obj F
      ).IsQuasicoherent :=
    AffineBaseChange.isQuasicoherent_pullback g _
  have hpull : ((Scheme.Modules.pullback g').obj F).IsQuasicoherent :=
    AffineBaseChange.isQuasicoherent_pullback g' F
  have hf'qc : QuasiCompact f' := MorphismProperty.IsStableUnderBaseChange.of_isPullback H hfqc
  have hf'qs : QuasiSeparated f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback H inferInstance
  have htgt : ((Scheme.Modules.pullback g' ⋙ Scheme.Modules.pushforward f').obj F
      ).IsQuasicoherent :=
    AlgebraicGeometry.pushforward_isQuasicoherent f' _
  refine AffineBaseChange.isIso_of_isIso_app_top _ ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  let _ := baseAlgebra g
  have hq := exists_linearEquiv_sections_baseChange (IsPullback.of_id_snd (f := g))
    ((Scheme.Modules.pushforward f).obj F)
  rw [baseModule_id_eq_instModule ((Scheme.Modules.pushforward f).obj F),
    baseModule_id_eq_instModule
      ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj F))] at hq
  obtain ⟨e₀, he₀⟩ := hq
  have hp := exists_linearEquiv_sections_baseChange H F
  rw [baseModule_eq_instModule f F,
    baseModule_eq_instModule f' ((Scheme.Modules.pullback g').obj F)] at hp
  obtain ⟨e, he⟩ := hp
  have hcomp : ∀ x, (((AffinePushforward.baseChangeNatTrans H.w).app F).app
      (⊤ : S'.Opens)).hom (e₀ x) = e x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul b a =>
        rw [he₀ b a]
        exact ((Scheme.Modules.Hom.app_smul
            ((AffinePushforward.baseChangeNatTrans H.w).app F) b _).trans
          (congrArg (fun z => b • z)
            (baseChangeNatTrans_app_top_pullbackSectionsHom H.w F a))).trans (he b a).symm
    | add x y hx hy =>
        rw [map_add, map_add, hx, hy]
        exact (map_add e x y).symm
  have hbij : Function.Bijective
      ((((AffinePushforward.baseChangeNatTrans H.w).app F).app (⊤ : S'.Opens)).hom ∘ e₀) := by
    refine ⟨fun u v huv => e.injective (((hcomp u).symm.trans huv).trans (hcomp v)), fun z => ?_⟩
    obtain ⟨x, hx⟩ := e.surjective z
    exact ⟨x, (hcomp x).trans hx⟩
  exact (Function.Bijective.of_comp_iff _ e₀.bijective).mp hbij

/-- Flat base change for direct images of quasi-coherent modules in degree zero.  Let
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
be a cartesian square of schemes with `g` flat and `f` quasi-compact and quasi-separated, and let
`ℱ` be a quasi-coherent sheaf of modules on `X`.  Then the canonical base-change morphism
`g^* f_* ℱ ⟶ f'_* (g')^* ℱ` is an isomorphism. -/
theorem isIso_baseChangeNatTrans_of_flat (H : IsPullback g' f' f g)
    [Flat g] [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] :
    IsIso ((AffinePushforward.baseChangeNatTrans H.w).app F) := by
  refine isIso_baseChangeNatTrans_of_affineBases H.w F (fun U V hV hU hVa => ?_)
  have _ : IsAffine U.toScheme := hU
  have _ : IsAffine V.toScheme := hVa
  have _ : CompactSpace (f ⁻¹ᵁ U).toScheme :=
    (quasiCompact_iff_compactSpace (f ∣_ U)).mp inferInstance
  have _ : QuasiSeparatedSpace (f ⁻¹ᵁ U).toScheme :=
    (quasiSeparated_iff_quasiSeparatedSpace (f ∣_ U)).mp inferInstance
  have _ : ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj F).IsQuasicoherent :=
    AffineBaseChange.isQuasicoherent_pullback (f ⁻¹ᵁ U).ι F
  exact isIso_baseChangeNatTrans_of_isAffineBases (isPullback_restrictBasesSquare H U hV) _

end Affine

end Stacks.AlgebraicGeometry.FlatBaseChangeCohomology

end
