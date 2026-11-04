module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverTerminal
public import StacksFrontier.AlgebraicGeometry.ProEtale.CompletedConstantSheafMaps
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleDerivedSheaves
import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CompleteGlobalSection
import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.RestrictScalars
import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory

/-!
# Derived completeness on `X_proét` against derived completeness of `Λ`-module complexes

Let `X` be a scheme, `Λ` a Noetherian ring and `I ⊆ Λ` an ideal. An object `K` of
`D(X_proét, Λ)`, the derived category of sheaves of modules over the constant ring sheaf
`\underline{Λ}`, may be derived complete in two senses:

* along the ideal sheaf `I·\underline{Λ}` of the ringed site, in the sense of Stacks 0999:
  `T(K|_U, f) = 0` for every object `U` and every local section `f` of `I·\underline{Λ}` over `U`;
* as an object of the `Λ`-linear derived category of sheaves of `Λ`-modules, in the sense of
  Stacks 091S: `T(K, f) = 0` for every `f ∈ I`.

The first implies the second. For `l ∈ I` the section `l` of `I·\underline{Λ}` over the final
object `T` of `X_proét` gives `T(K|_T, l) = 0` on the slice site over `T`. Over a terminal object
restriction to the slice is an equivalence (`Stacks.SheafOfModules.overTerminalEquivalence`),
so composing it with the equivalence between sheaves of `Λ`-modules and sheaves of
`\underline{Λ}`-modules gives an exact equivalence of derived categories which carries
multiplication by `l` to multiplication by the section `l` over the final object; such a
functor reflects the invertibility of `1 - l·shift` on `∏ K`.

## Main results

* `AlgebraicGeometry.ProEtale.constantCoefficientModuleEquiv_functor_map_smul_id_val_app`: the
  equivalence between sheaves of `Λ`-modules and sheaves of `\underline{Λ}`-modules carries
  multiplication by `l ∈ Λ` to multiplication by the section `l` of `\underline{Λ}`.
* `AlgebraicGeometry.ProEtale.isDerivedComplete_derivedModuleEquiv_inverse_obj`: derived
  completeness along `I·\underline{Λ}` implies derived completeness along `I` of the
  corresponding complex of sheaves of `Λ`-modules.

## References

* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
* [Stacks Project, Tag 091S](https://stacks.math.columbia.edu/tag/091S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped IsMulCommutative

universe u w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard
  SheafOfModules.hasSheafify_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  SheafOfModules.wEqualsLocallyBijective_commRingCat
  GrothendieckTopology.hasSheafify_addCommGrpCat
  SheafOfModules.wEqualsLocallyBijective_addCommGrpCat

variable (X : Scheme.{u}) {Λ : Type (max (u + 1) w)} [CommRing Λ] [IsNoetherianRing Λ]

/-- **The coefficients act through the constant ring sheaf.** The equivalence between sheaves of
`Λ`-modules and sheaves of `\underline{Λ}`-modules carries multiplication by `l ∈ Λ` to
multiplication by the section of `\underline{Λ}` given by `l`, on the sections over every
object. -/
theorem constantCoefficientModuleEquiv_functor_map_smul_id_val_app
    (P : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) (l : Λ) (W : X.ProEt)
    (z : ((constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ).functor.obj P).val.obj
      (op W)) :
    ((constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ).functor.map (l • 𝟙 P)).val.app
        (op W) z = coefficientSectionsMap.{u, max (u + 1) w, w} X Λ W l • z := by
  obtain ⟨y, rfl⟩ := (moduleSheafOverConstantCoefficientsSectionsEquiv X P W).surjective z
  rw [← moduleSheafOverConstantCoefficientsSectionsEquiv_naturality]
  exact moduleSheafOverConstantCoefficientsSectionsEquiv_smul X P W l y

/-- **Derived completeness along `I·\underline{Λ}` gives derived completeness along `I`.** If an
object `K` of `D(X_proét, Λ)` is derived complete along the ideal sheaf `I·\underline{Λ}`
(Stacks 0999), then the corresponding object of the derived category of sheaves of `Λ`-modules
is derived complete along `I` (Stacks 091S): `T(K, l) = 0` for every `l ∈ I`. -/
theorem isDerivedComplete_derivedModuleEquiv_inverse_obj (I : Ideal Λ)
    {K : DerivedSheaves.{u, max (u + 1) w, w} X Λ}
    (hK : RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I) K) :
    IsDerivedComplete I ((derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.obj K) := by
  intro l hl
  let R := Stacks.SheafOfModules.Tensor.ringSheaf
    (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ).O
  let T : X.ProEt := ⊤_ X.ProEt
  obtain ⟨hAdd, hLim, hColim, hProd, hc⟩ := hK T (coefficientSectionsMap X Λ T l)
    (coefficientSectionsMap_mem_constantCoefficientIdealSheaf X Λ I T hl)
  let : ∀ V : X.ProEtᵒᵖ, IsMulCommutative (R.obj.obj V) := fun V ↦ by
    show IsMulCommutative ((constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ).O.obj.obj V)
    infer_instance
  let : ∀ V : (Over T)ᵒᵖ, IsMulCommutative ((R.over T).obj.obj V) := fun V ↦
    inferInstanceAs (IsMulCommutative (R.obj.obj (op V.unop.left)))
  let A := SheafOfModules.{max (u + 1) w} (R.over T)
  let : Linear (CatCenter A) A := Linear.ofRingMorphism (RingHom.id (CatCenter A))
  let F := SheafOfModules.overFunctor.{max (u + 1) w} R T
  let := hAdd
  let := hLim
  let := hColim
  let := hProd
  let aT : CatCenter A := Stacks.SheafOfModules.terminalSectionToEnd (R.over T) (Over.mk (𝟙 T))
    Over.mkIdTerminal (coefficientSectionsMap X Λ T l)
  let E := constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ
  let Φ := E.trans (Stacks.SheafOfModules.overTerminalEquivalence R terminalIsTerminal :
    SheafOfModules.{max (u + 1) w} R ≌ SheafOfModules.{max (u + 1) w} (R.over T))
  let : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  let : Φ.functor.Additive := Functor.additive_of_preserves_binary_products _
  let : Φ.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let D := Dualizing.mapDerivedCategoryEquivalenceOfEquivalence Φ
  let K' := (derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.obj K
  let s : (R.obj ⋙ forget RingCat).sections :=
    ⟨fun V ↦ coefficientSectionsMap.{u, max (u + 1) w, w} X Λ V.unop l,
      fun f ↦ coefficientSectionsMap_restrict X Λ f.unop l⟩
  have hab : ∀ P, Φ.functor.map (l • 𝟙 P) = aT • 𝟙 (Φ.functor.obj P) := fun P ↦ by
    have hE : E.functor.map (l • 𝟙 P) =
        (Stacks.SheafOfModules.globalSectionToEnd R s).app (E.functor.obj P) := by
      ext W z
      exact constantCoefficientModuleEquiv_functor_map_smul_id_val_app X P l W.unop z
    show F.map (E.functor.map (l • 𝟙 P)) = aT.app _ ≫ 𝟙 _
    rw [Category.comp_id, hE]
    exact Stacks.SheafOfModules.overFunctor_map_globalSectionToEnd R T s _
  have : D.functor.Additive := inferInstanceAs Φ.functor.mapDerivedCategory.Additive
  have hsmul : D.functor.map (l • 𝟙 K') = aT • 𝟙 (D.functor.obj K') :=
    Stacks.SheafOfModules.DerivedRestrictScalars.mapDerivedCategory_map_smul_id Φ.functor l aT
      (fun Z ↦ Stacks.SemilinearFunctor.map_smul_id_mapHomologicalComplex Φ.functor l aT hab _ Z)
      K'
  let e : D.functor.obj K' ≅ F.mapDerivedCategory.obj K :=
    (Stacks.SheafOfModules.DerivedRestrictScalars.mapDerivedCategoryCompIso E.functor F).app K' ≪≫
      F.mapDerivedCategory.mapIso ((derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).counitIso.app K)
  have := RingedSite.isIso_map_oneSubSmulShift_of_isDerivedCompleteAt D.functor hsmul
    ((RingedSite.isDerivedCompleteAt_iff_of_iso e aT).2 hc)
  exact isIso_of_reflects_iso _ D.functor

end AlgebraicGeometry.ProEtale

end
