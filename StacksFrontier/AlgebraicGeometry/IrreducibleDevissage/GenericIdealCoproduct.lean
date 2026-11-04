module

public import StacksFrontier.AlgebraicGeometry.Cohomology.CoherentExtension.IdealPowerExtension
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.GenericFreeNeighbourhood

/-!
# A finite sum of one ideal sheaf inside a coherent module, near the generic point

Let `Z` be an integral Noetherian scheme with generic point `ξ` and let `𝒢` be a coherent
`𝒪_Z`-module. Since `𝒪_{Z, ξ}` is the function field of `Z`, the stalk `𝒢_ξ` is a finite
dimensional vector space, of dimension `r` say, so `𝒢` is free of rank `r` on some open
neighbourhood `U` of `ξ`. Taking `ℐ` for the `n`-th power of the ideal sheaf of the closed
complement of `U`, for `n` large enough, the identification over `U` extends to a monomorphism

`ℐ ^{⊕ r} ⟶ 𝒢`

which is still invertible over `U`. This is the case `Z = X` of [Stacks, Tag 01YE].

## Main results

* `exists_idealCoproduct_mono_isIso_of_free`: the statement above, taking the generic freeness
  of `𝒢` as an input.
* `exists_idealCoproduct_mono_isIso_near_genericPoint`: the same with the generic freeness
  discharged, which is [Stacks, Tag 01YE] in the case `Z = X`.

## Implementation notes

The extension of the identification over `U` is
`AlgebraicGeometry.exists_idealPowSmul_hom_restrict`, the surjectivity half of
[Stacks, Tag 01YB], which produces a morphism out of `ℐ ^ n 𝒪_Z^{⊕ r}` rather than out of
`(ℐ ^ n)^{⊕ r}`. The comparison between the two is
`AlgebraicGeometry.idealPowSmulMap`, applied to each of the `r` inclusions
`𝒪_Z ⟶ 𝒪_Z^{⊕ r}`: no isomorphism between them is needed, only that the sum of the `r`
copies of `ℐ ^ n` maps into `ℐ ^ n 𝒪_Z^{⊕ r}`, and that both agree with the free module over
`U`, where `ℐ` is the unit ideal.

Injectivity is where integrality of `Z` is used, and it is tested on the sections: a morphism
into `∐ ℐ` is determined by its `r` components followed by `ℐ ⟶ 𝒪_Z`, because a finite
coproduct of modules is a finite product, and a morphism into `𝒪_Z` is determined by its
sections over the opens meeting the generic point, because restriction of functions to a
nonempty open is injective on an integral scheme and an open missing the generic point is
empty.

## References

* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPowerSmul
open Stacks.AlgebraicGeometry.Tag01YEIntegralReduction (isIso_app_of_isIso_restrictFunctor_map)

universe u

namespace Stacks.AlgebraicGeometry.IrreducibleDevissage

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

attribute [local instance] Stacks.AlgebraicGeometry.IrreducibleDevissage.hasFiniteBiproducts_modules

variable {Z : Scheme.{u}}

/-! ### A functor preserving coproducts turns a family of isomorphisms into one -/

/-- A functor which preserves the two coproducts carries a coproduct of morphisms, each of whose
images is invertible, to an invertible morphism. -/
private lemma isIso_map_sigmaMap {C : Type*} [Category C] {D : Type*} [Category D]
    (E : C ⥤ D) {J : Type} {F G : J → C} [HasCoproduct F] [HasCoproduct G]
    [HasCoproductsOfShape J D] [PreservesColimit (Discrete.functor F) E]
    [PreservesColimit (Discrete.functor G) E] (f : ∀ j, F j ⟶ G j)
    [∀ j, IsIso (E.map (f j))] : IsIso (E.map (CategoryTheory.Limits.Sigma.map f)) := by
  have h : E.map (CategoryTheory.Limits.Sigma.map f) = (PreservesCoproduct.iso E F).hom ≫
      (CategoryTheory.Limits.Sigma.map (fun j => E.map (f j))) ≫
        (PreservesCoproduct.iso E G).inv := by
    apply (cancel_epi (PreservesCoproduct.iso E F).inv).mp
    simp only [Iso.inv_hom_id_assoc]
    refine Sigma.hom_ext _ _ fun j => ?_
    simp only [PreservesCoproduct.inv_hom, ι_comp_sigmaComparison_assoc,
      Sigma.ι_map_assoc, ι_comp_sigmaComparison]
    rw [← E.map_comp, Sigma.ι_map, E.map_comp]
  rw [h]
  infer_instance

/-! ### Morphisms into the structure sheaf of an integral scheme -/

/-- On an integral scheme, restriction of functions to a nonempty open subset is injective; the
same map, read on the structure sheaf as a module over itself. -/
private lemma unit_val_map_injective [IsIntegral Z] {V W : Z.Opens} (i : W ⟶ V) [Nonempty W] :
    Function.Injective ((SheafOfModules.unit Z.ringCatSheaf).val.map i.op) :=
  map_injective_of_isIntegral (X := Z) i

/-- **On an integral scheme a morphism into the structure sheaf is determined near the generic
point.** Two morphisms into `𝒪_Z` agreeing on sections over every open contained in a
neighbourhood `U` of the generic point are equal: over an open meeting `U` they agree after the
injective restriction to the intersection, and an open missing the generic point is empty. -/
private lemma hom_eq_of_app_eq_unit [IsIntegral Z]
    (ξ : Z) (hξ : IsGenericPoint ξ (Set.univ : Set Z)) (U : Z.Opens) (hξU : ξ ∈ U)
    {A : Z.Modules} {f g : A ⟶ SheafOfModules.unit Z.ringCatSheaf}
    (h : ∀ W : Z.Opens, W ≤ U → f.app W = g.app W) : f = g := by
  refine Scheme.Modules.hom_ext f g fun V => ?_
  by_cases hξV : ξ ∈ V
  · have hne : Nonempty (V ⊓ U : Z.Opens) := ⟨⟨ξ, ⟨hξV, hξU⟩⟩⟩
    ext s
    refine unit_val_map_injective (homOfLE (inf_le_left : V ⊓ U ≤ V)) ?_
    rw [← AlgebraicGeometry.app_apply_map f (homOfLE (inf_le_left : V ⊓ U ≤ V)) s,
      ← AlgebraicGeometry.app_apply_map g (homOfLE (inf_le_left : V ⊓ U ≤ V)) s]
    exact ConcreteCategory.congr_hom (h (V ⊓ U) inf_le_right) _
  · obtain rfl : V = ⊥ := by
      ext x
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hξV ((hξ.mem_open_set_iff V.isOpen).2 ⟨x, Set.mem_univ x, hx⟩)
    ext s
    exact @Subsingleton.elim Γ(Z, ⊥) inferInstance _ _

/-- **A morphism into a finite sum of copies of an ideal sheaf is determined near the generic
point.** A finite coproduct is a finite product, so such a morphism is determined by its `r`
components followed by the inclusion of the ideal sheaf into `𝒪_Z`. -/
private lemma hom_eq_of_app_eq_idealCoproduct [IsIntegral Z]
    (ξ : Z) (hξ : IsGenericPoint ξ (Set.univ : Set Z)) (U : Z.Opens) (hξU : ξ ∈ U)
    (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule) (r : ℕ) {A : Z.Modules}
    {f g : A ⟶ ∐ fun _ : Fin r => I.toSheafOfModules}
    (h : ∀ W : Z.Opens, W ≤ U → f.app W = g.app W) : f = g := by
  have key : ∀ k : (∐ fun _ : Fin r => I.toSheafOfModules) ⟶
      SheafOfModules.unit Z.ringCatSheaf, f ≫ k = g ≫ k := by
    intro k
    refine hom_eq_of_app_eq_unit ξ hξ U hξU fun W hW => ?_
    exact congrArg (fun m => m ≫ Scheme.Modules.Hom.app (X := Z) k W) (h W hW)
  let H : Fin r → Z.Modules := fun _ => I.toSheafOfModules
  let e := (biproduct.isoCoproduct H).symm ≪≫ biproduct.isoProduct H
  apply (cancel_mono e.hom).mp
  refine Limits.Pi.hom_ext _ _ fun j => (cancel_mono I.ι).mp ?_
  exact (Category.assoc f (e.hom ≫ Pi.π H j) I.ι).trans
    ((key _).trans (Category.assoc g (e.hom ≫ Pi.π H j) I.ι).symm)

/-- **A morphism out of a finite sum of copies of an ideal sheaf on an integral scheme which is
invertible near the generic point is a monomorphism.** -/
private lemma mono_of_isIso_restrictFunctor_idealCoproduct [IsIntegral Z]
    (ξ : Z) (hξ : IsGenericPoint ξ (Set.univ : Set Z)) (U : Z.Opens) (hξU : ξ ∈ U)
    (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule) (r : ℕ) {G : Z.Modules}
    (β : (∐ fun _ : Fin r => I.toSheafOfModules) ⟶ G)
    (hβ : IsIso ((Scheme.Modules.restrictFunctor U.ι).map β)) : Mono β := by
  refine ⟨fun {A} f g hfg => hom_eq_of_app_eq_idealCoproduct ξ hξ U hξU I r fun W hW => ?_⟩
  have hiso : IsIso (Scheme.Modules.Hom.app (X := Z) β W) :=
    isIso_app_of_isIso_restrictFunctor_map β U hβ W hW
  exact (cancel_mono (Scheme.Modules.Hom.app (X := Z) β W)).mp
    (congrArg (fun k : A ⟶ G => Scheme.Modules.Hom.app (X := Z) k W) hfg)

/-! ### The integral case of [Stacks, Tag 01YE] -/

/-- **A finite sum of one coherent ideal sheaf inside a coherent module, invertible near the
generic point.** Let `Z` be an integral Noetherian scheme with generic point `ξ`, let `𝒢` be a
coherent `𝒪_Z`-module, and suppose `𝒢` is free of rank `r` on a neighbourhood `U` of `ξ`. Then
there is a coherent sheaf of ideals `ℐ ⊆ 𝒪_Z` and a monomorphism `ℐ^{⊕ r} ⟶ 𝒢` which is an
isomorphism over `U`.

This is the case `Z = X` of [Stacks, Tag 01YE]; the generic freeness it assumes is where that
proof uses that `𝒪_{Z, ξ}` is a field. -/
theorem exists_idealCoproduct_mono_isIso_of_free [IsNoetherian Z] [IsIntegral Z]
    (G : Z.Modules) [G.IsCoherent] (ξ : Z) (hξ : IsGenericPoint ξ (Set.univ : Set Z))
    (r : ℕ) (U : Z.Opens) (hξU : ξ ∈ U)
    (hFr : (SheafOfModules.free.{u} (R := Z.ringCatSheaf) (ULift.{u} (Fin r))).IsCoherent)
    (eC : (∐ fun _ : Fin r => SheafOfModules.unit Z.ringCatSheaf) ≅
      SheafOfModules.free.{u} (R := Z.ringCatSheaf) (ULift.{u} (Fin r)))
    (eU : (Scheme.Modules.restrictFunctor U.ι).obj
        (SheafOfModules.free.{u} (R := Z.ringCatSheaf) (ULift.{u} (Fin r))) ≅
      (Scheme.Modules.restrictFunctor U.ι).obj G) :
    ∃ I : (SheafOfModules.unit Z.ringCatSheaf).Submodule,
      I.toSheafOfModules.IsCoherent ∧
      ∃ β : (∐ fun _ : Fin r => I.toSheafOfModules) ⟶ G, Mono β ∧
        IsIso ((Scheme.Modules.restrictFunctor U.ι).map β) := by
  classical
  have hGqc : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  have hunit : (SheafOfModules.unit Z.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent Z
  have hunitqc : (SheafOfModules.unit Z.ringCatSheaf).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  have hFrqc : (SheafOfModules.free.{u} (R := Z.ringCatSheaf)
      (ULift.{u} (Fin r))).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  set Fr := SheafOfModules.free.{u} (R := Z.ringCatSheaf) (ULift.{u} (Fin r))
  set J : Z.IdealSheafData := closedIdeal ⟨(U : Set Z)ᶜ, isClosed_compl_iff.mpr U.2⟩
  -- extend the identification over `U` to a morphism out of an ideal power
  obtain ⟨n, ψ, hψ⟩ := exists_idealPowSmul_hom_restrict Fr G U eU.hom
  set I : (SheafOfModules.unit Z.ringCatSheaf).Submodule :=
    idealPowSmul J n (SheafOfModules.unit Z.ringCatSheaf)
  -- the sum of `r` copies of `ℐ ^ n` maps into `ℐ ^ n 𝒪_Z^{⊕ r}`
  set a : (∐ fun _ : Fin r => I.toSheafOfModules) ⟶ (idealPowSmul J n Fr).toSheafOfModules :=
    Sigma.desc (fun j => idealPowSmulMap J n
      (Sigma.ι (fun _ : Fin r => SheafOfModules.unit Z.ringCatSheaf) j ≫ eC.hom)) with ha
  have hκ : a ≫ (idealPowSmul J n Fr).ι =
      CategoryTheory.Limits.Sigma.map (fun _ : Fin r => I.ι) ≫ eC.hom := by
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [ha, Sigma.ι_desc_assoc, Sigma.ι_map_assoc]
    exact idealPowSmulMap_comp_ι J n _
  -- everything in sight is invertible over `U`
  have hIiso : IsIso ((Scheme.Modules.restrictFunctor U.ι).map I.ι) :=
    isIso_restrictFunctor_map_idealPowSmul_ι U n _
  have hιiso : IsIso ((Scheme.Modules.restrictFunctor U.ι).map (idealPowSmul J n Fr).ι) :=
    isIso_restrictFunctor_map_idealPowSmul_ι U n Fr
  have hall : ∀ j : Fin r, IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      ((fun _ : Fin r => I.ι) j)) := fun _ => hIiso
  have hsig : IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (CategoryTheory.Limits.Sigma.map (fun _ : Fin r => I.ι))) :=
    isIso_map_sigmaMap _ _
  have heC : IsIso ((Scheme.Modules.restrictFunctor U.ι).map eC.hom) :=
    inferInstanceAs (IsIso ((Scheme.Modules.restrictFunctor U.ι).mapIso eC).hom)
  have haiso : IsIso ((Scheme.Modules.restrictFunctor U.ι).map a) := by
    have h1 : (Scheme.Modules.restrictFunctor U.ι).map a ≫
        (Scheme.Modules.restrictFunctor U.ι).map (idealPowSmul J n Fr).ι =
          (Scheme.Modules.restrictFunctor U.ι).map
            (CategoryTheory.Limits.Sigma.map (fun _ : Fin r => I.ι)) ≫
            (Scheme.Modules.restrictFunctor U.ι).map eC.hom :=
      (Functor.map_comp _ a (idealPowSmul J n Fr).ι).symm.trans
        ((congrArg (Scheme.Modules.restrictFunctor U.ι).map hκ).trans (Functor.map_comp _ _ _))
    have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map a ≫
        (Scheme.Modules.restrictFunctor U.ι).map (idealPowSmul J n Fr).ι) := by
      rw [h1]
      exact IsIso.comp_isIso' hsig heC
    exact IsIso.of_isIso_comp_right _
      ((Scheme.Modules.restrictFunctor U.ι).map (idealPowSmul J n Fr).ι)
  have hψiso : IsIso ((Scheme.Modules.restrictFunctor U.ι).map ψ) := by
    rw [← hψ]
    infer_instance
  have hβiso : IsIso ((Scheme.Modules.restrictFunctor U.ι).map (a ≫ ψ)) := by
    rw [show (Scheme.Modules.restrictFunctor U.ι).map (a ≫ ψ) = _ ≫ _ from
      Functor.map_comp (Scheme.Modules.restrictFunctor U.ι) a ψ]
    infer_instance
  exact ⟨I, isCoherent_idealPowSmul J n _, a ≫ ψ,
    mono_of_isIso_restrictFunctor_idealCoproduct ξ hξ U hξU I r (a ≫ ψ) hβiso, hβiso⟩

/-- **The case `Z = X` of [Stacks, Tag 01YE].** On an integral Noetherian scheme `Z` with
generic point `ξ`, every coherent module `𝒢` contains a finite sum of copies of one coherent
sheaf of ideals, by a monomorphism which is an isomorphism on a neighbourhood of `ξ`.

The rank `r` is `dim_{κ(ξ)} 𝒢_ξ`: the local ring at the generic point of an integral scheme is
the function field, so the stalk is a finite dimensional vector space and `𝒢` is free of rank
`r` near `ξ`, which is `exists_isIso_restrictFunctor_free_near_genericPoint`. -/
theorem exists_idealCoproduct_mono_isIso_near_genericPoint [AlgebraicGeometry.IsNoetherian Z]
    [IsIntegral Z] (G : Z.Modules) [G.IsCoherent] (ξ : Z)
    (hξ : IsGenericPoint ξ (Set.univ : Set Z)) :
    ∃ (r : ℕ) (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsCoherent ∧
      ∃ β : (∐ fun _ : Fin r => I.toSheafOfModules) ⟶ G, Mono β ∧
        ∃ V : Z.Opens, ξ ∈ V ∧ IsIso ((Scheme.Modules.restrictFunctor V.ι).map β) := by
  have hZln : IsLocallyNoetherian Z := AlgebraicGeometry.IsNoetherian.toIsLocallyNoetherian
  obtain ⟨r, U, hξU, ⟨eU⟩⟩ := exists_isIso_restrictFunctor_free_near_genericPoint G ξ hξ
  obtain ⟨I, hI, β, hβ, hβiso⟩ := exists_idealCoproduct_mono_isIso_of_free G ξ hξ r U hξU
    (isCoherent_free_ulift r) (freeCoproductIso Z r) eU
  exact ⟨r, I, hI, β, hβ, U, hξU, hβiso⟩

end Stacks.AlgebraicGeometry.IrreducibleDevissage

end
