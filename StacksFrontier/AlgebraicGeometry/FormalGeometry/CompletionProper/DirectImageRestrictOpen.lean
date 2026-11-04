module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.BaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaRestrictionSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Product
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.DirectImageCharacterization
public import StacksCore.Tactic.StacksAttribute

/-!
# `δ` and the `γ_n` commute with restriction to an open of the base

Let `f : X ⟶ Y` be a morphism of schemes, let `𝒥 ⊆ 𝒪_Y` be a quasi-coherent sheaf of ideals, and
let `U ⊆ Y` be open. Writing `g = f ∣_ U : f ⁻¹ U ⟶ U` for the induced morphism, this file proves
that the comparison

`δ_m : (f_*𝓕) / 𝒥 ᵐ (f_*𝓕) ⟶ f_*(𝓕 / ℐ ᵐ 𝓕)`

of `Stacks.Coherent.directImageQuotientComparison` restricts, over `U`, to the same comparison
for `g` and the restricted data `𝒥|_U`, `𝓕|_{f ⁻¹ U}`, and that the maps `γ_n` of
`Stacks.Coherent.directImageComparison` do the same.

## Main definitions

* `Stacks.Algebraization.idealPowerQuotientCongr` — the quotient `M / 𝒦 ᵐ M` under an equality
  of ideal sheaves.
* `Stacks.Algebraization.restrictIdealPowerQuotientCongrIso` — **restriction of `M / ℐ ᵐ M` to an
  open**, with the restricted ideal sheaf named by another pullback.
* `Stacks.Coherent.directImageQuotientRestrictTargetIso`,
  `Stacks.Coherent.directImageQuotientRestrictSourceIso` — the identifications of the target
  and of the source of `δ_m` with the target and the source of `δ_m` for `f ∣_ U`.

## Main results

* `Stacks.Coherent.comap_comap_morphismRestrict` — the two ways of pulling `𝒥` back to
  `f ⁻¹ U`, through `U` and through `X`, agree.
* `Stacks.Coherent.directImageQuotientComparison_restrict_π` — **the normalized form of the
  compatibility**: the restriction of `δ_m`, read out of `f_*𝓕` along the restricted quotient
  projection, is `δ_m` for `f ∣_ U` read out of `(f ∣_ U)_*(𝓕|_{f ⁻¹ U})` along the base-change
  isomorphism. This needs no quasi-coherence of `f_*𝓕`.
* `Stacks.Coherent.directImageQuotientComparison_restrict` — **`δ` commutes with restriction to
  an open of the base**, as an identity of morphisms conjugated by the two identifications.
* `Stacks.Coherent.directImageComparison_app_restrict` — **`γ_n` carried to the comparison for
  `f ⁻¹ U ⟶ U`**: the restriction of `γ_n`, read through the base-change isomorphism, is the
  restricted adjunction map followed by the direct image along `f ∣_ U` of the restricted `β_n`.
* `Stacks.Coherent.directImageComparison_app_restrict_unit` — the same, with the restricted
  adjunction map replaced by the adjunction map of `f ∣_ U`: the restricted `γ_n` is the `γ_n` of
  `f ∣_ U` for an explicitly named restriction `β'` of `β`.
* `Stacks.AlgebraicGeometry.AffinePushforward.pullbackPushforwardAdjunction_unit_restrict` —
  **the unit of `f^* ⊣ f_*` commutes with restriction to an open of the base**.

## References

* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PresheafOfModules
open Stacks.AlgebraicGeometry.RestrictionSections
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.AffinePushforward

/-! ### The unit of `f^* ⊣ f_*` and restriction to an open of the base -/

section Unit

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)

/-- The unit of `f^* ⊣ f_*` restricted to `V`, read through the two base-change isomorphisms, on
a section coming from an open `W` of `S`, is the unit of `(f ∣_ V)^* ⊣ (f ∣_ V)_*` on the
restricted section. -/
public theorem pullbackRestrictIso_hom_restrictPushforwardIso_hom_unit
    (M : S.Modules) (W : S.Opens) (y : M.val.obj (op W)) :
    Hom.app ((pullbackRestrictIso f V).hom.app M).val (op ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ W)))
        (Hom.app ((restrictPushforwardIso f V).hom.app
            ((Scheme.Modules.pullback f).obj M)).val (op (V.ι ⁻¹ᵁ W))
          (Hom.app ((Scheme.Modules.restrictFunctor V.ι).map
              ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)).val
            (op (V.ι ⁻¹ᵁ W))
            (Hom.app ((Scheme.Modules.restrictAdjunction V.ι).unit.app M).val (op W) y))) =
      Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ V)).unit.app
            ((Scheme.Modules.restrictFunctor V.ι).obj M)).val (op (V.ι ⁻¹ᵁ W))
        (Hom.app ((Scheme.Modules.restrictAdjunction V.ι).unit.app M).val (op W) y) :=
  (congrArg (fun z => Hom.app ((pullbackRestrictIso f V).hom.app M).val
        (op ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ W)))
      (Hom.app ((restrictPushforwardIso f V).hom.app
        ((Scheme.Modules.pullback f).obj M)).val (op (V.ι ⁻¹ᵁ W)) z))
    (restrictUnit_naturality V.ι
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) (op W) y)).trans
  ((congrArg (Hom.app ((pullbackRestrictIso f V).hom.app M).val
        (op ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ W))))
      (restrictPushforwardIso_hom_restrictUnit f V ((Scheme.Modules.pullback f).obj M) W
        (Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val
          (op W) y))).trans
    (pullbackRestrictIso_hom_pullbackUnit f V M W y))

/-- **The unit of `f^* ⊣ f_*` commutes with restriction to an open of the base**, in the form
with `Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictIso` read forwards. -/
public theorem restrictPushforwardIso_hom_comp_map_pullbackRestrictIso_hom (M : S.Modules) :
    (Scheme.Modules.restrictFunctor V.ι).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
      (restrictPushforwardIso f V).hom.app ((Scheme.Modules.pullback f).obj M) ≫
        (Scheme.Modules.pushforward (f ∣_ V)).map ((pullbackRestrictIso f V).hom.app M) =
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ V)).unit.app
      ((Scheme.Modules.restrictFunctor V.ι).obj M) := by
  ext W z
  obtain ⟨W, rfl⟩ : ∃ W₀ : V.toScheme.Opens, V.ι ⁻¹ᵁ (V.ι ''ᵁ W₀) = W :=
    ⟨W, V.ι.preimage_image_eq W⟩
  obtain ⟨y, hy⟩ := exists_restrictUnit_eq V.ι M (V.ι ''ᵁ W) (image_preimage_image V.ι W) z
  rw [← hy]
  exact pullbackRestrictIso_hom_restrictPushforwardIso_hom_unit f V M (V.ι ''ᵁ W) y

/-- **The unit of `f^* ⊣ f_*` commutes with restriction to an open of the base.** Restricting the
adjunction map `M ⟶ f_*f^*M` to `V` and reading the result through the direct-image base-change
isomorphism gives the adjunction map `M|_V ⟶ (f ∣_ V)_*(f ∣_ V)^*(M|_V)` of the restricted
morphism, followed by the direct image of the inverse-image base-change isomorphism. -/
public theorem pullbackPushforwardAdjunction_unit_restrict (M : S.Modules) :
    (Scheme.Modules.restrictFunctor V.ι).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
      (restrictPushforwardIso f V).hom.app ((Scheme.Modules.pullback f).obj M) =
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ V)).unit.app
        ((Scheme.Modules.restrictFunctor V.ι).obj M) ≫
      (Scheme.Modules.pushforward (f ∣_ V)).map ((pullbackRestrictIso f V).inv.app M) :=
  (Iso.eq_comp_inv ((Scheme.Modules.pushforward (f ∣_ V)).mapIso
      ((pullbackRestrictIso f V).app M))).2
    ((Category.assoc (obj := V.toScheme.Modules) _ _ _).trans
      (restrictPushforwardIso_hom_comp_map_pullbackRestrictIso_hom f V M))

end Unit

end Stacks.AlgebraicGeometry.AffinePushforward

namespace Stacks.Algebraization

/-! ### The quotient `M / 𝒦 ᵐ M` under an equality of ideal sheaves -/

section Congr

variable {Z : Scheme.{u}} {K K' : Z.IdealSheafData} (h : K = K') (m : ℕ) (N : Z.Modules)

/-- The map `M / 𝒦 ᵐ M ⟶ M / 𝒦' ᵐ M` induced by an equality `𝒦 = 𝒦'` of ideal sheaves: the
reduction of the identity of `M`. -/
public def idealPowerQuotientCongrMap :
    idealPowerQuotient K m N ⟶ idealPowerQuotient K' m N :=
  idealPowerQuotientMap K K' m m (le_of_eq (congrArg (fun L => L ^ m) h)) (𝟙 N)

/-- `Stacks.Algebraization.idealPowerQuotientCongrMap` composed with the quotient projection of
its source is the quotient projection of its target. -/
public theorem idealPowerQuotientCongrMap_π :
    cokernel.π (C := Z.Modules) (idealPowerMultiple K m N).ι ≫
        idealPowerQuotientCongrMap h m N =
      cokernel.π (C := Z.Modules) (idealPowerMultiple K' m N).ι :=
  (idealPowerQuotientMap_π K K' m m (le_of_eq (congrArg (fun L => L ^ m) h)) (𝟙 N)).trans
    (Category.id_comp _)

/-- **The quotient `M / 𝒦 ᵐ M` depends on `𝒦` only through `𝒦` itself**: an equality of ideal
sheaves induces an isomorphism of quotients, compatible with the quotient projections. -/
public def idealPowerQuotientCongr :
    idealPowerQuotient K m N ≅ idealPowerQuotient K' m N where
  hom := idealPowerQuotientCongrMap h m N
  inv := idealPowerQuotientCongrMap h.symm m N
  hom_inv_id := by
    refine (cancel_epi (cokernel.π (C := Z.Modules) (idealPowerMultiple K m N).ι)).1 ?_
    exact ((Category.assoc (obj := Z.Modules) _ _ _).symm.trans
      ((congrArg (fun z => z ≫ idealPowerQuotientCongrMap h.symm m N)
          (idealPowerQuotientCongrMap_π h m N)).trans
        (idealPowerQuotientCongrMap_π h.symm m N))).trans (Category.comp_id _).symm
  inv_hom_id := by
    refine (cancel_epi (cokernel.π (C := Z.Modules) (idealPowerMultiple K' m N).ι)).1 ?_
    exact ((Category.assoc (obj := Z.Modules) _ _ _).symm.trans
      ((congrArg (fun z => z ≫ idealPowerQuotientCongrMap h m N)
          (idealPowerQuotientCongrMap_π h.symm m N)).trans
        (idealPowerQuotientCongrMap_π h m N))).trans (Category.comp_id _).symm

end Congr

/-! ### Restriction of `M / ℐ ᵐ M` to an open, after a transport of the ideal sheaf -/

section RestrictQuotient

variable {X V : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] (I : X.IdealSheafData) (m : ℕ)
  (M : X.Modules) [M.IsQuasicoherent]

/-- `Stacks.Algebraization.restrictIdealPowerQuotientIso` read in the direction that takes the
restricted quotient to the quotient of the restriction. -/
public theorem restrictFunctor_map_cokernel_π_comp_restrictIdealPowerQuotientIso_inv :
    (Scheme.Modules.restrictFunctor j).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple I m M).ι) ≫
      (restrictIdealPowerQuotientIso j I m M).inv =
    cokernel.π (C := V.Modules)
      (idealPowerMultiple (I.comap j) m ((Scheme.Modules.restrictFunctor j).obj M)).ι :=
  ((Iso.eq_comp_inv (restrictIdealPowerQuotientIso j I m M)).2
    (cokernel_π_comp_restrictIdealPowerQuotientIso j I m M)).symm

/-- **Restriction of `M / ℐ ᵐ M` to an open, named by another pullback of the ideal sheaf.** For
an ideal sheaf `𝒦` on `V` equal to the pullback of `ℐ`, the restriction of `M / ℐ ᵐ M` to `V` is
`M|_V / 𝒦 ᵐ M|_V`. -/
public def restrictIdealPowerQuotientCongrIso {K : V.IdealSheafData} (h : K = I.comap j) :
    (Scheme.Modules.restrictFunctor j).obj (idealPowerQuotient I m M) ≅
      idealPowerQuotient K m ((Scheme.Modules.restrictFunctor j).obj M) :=
  (restrictIdealPowerQuotientIso j I m M).symm ≪≫
    idealPowerQuotientCongr h.symm m ((Scheme.Modules.restrictFunctor j).obj M)

/-- **The normalization of `Stacks.Algebraization.restrictIdealPowerQuotientCongrIso`**: it
carries the restriction of the quotient projection of `M` to the quotient projection of
`M|_V`. -/
public theorem restrictIdealPowerQuotientCongrIso_π {K : V.IdealSheafData} (h : K = I.comap j) :
    (Scheme.Modules.restrictFunctor j).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple I m M).ι) ≫
      (restrictIdealPowerQuotientCongrIso j I m M h).hom =
    cokernel.π (C := V.Modules)
      (idealPowerMultiple K m ((Scheme.Modules.restrictFunctor j).obj M)).ι :=
  (Category.assoc (obj := V.Modules) _ _ _).symm.trans
    ((congrArg (fun z => z ≫ idealPowerQuotientCongrMap h.symm m
          ((Scheme.Modules.restrictFunctor j).obj M))
        (restrictFunctor_map_cokernel_π_comp_restrictIdealPowerQuotientIso_inv j I m M)).trans
      (idealPowerQuotientCongrMap_π h.symm m ((Scheme.Modules.restrictFunctor j).obj M)))

end RestrictQuotient

end Stacks.Algebraization

namespace Stacks.Coherent

open Stacks.Algebraization Stacks.AlgebraicGeometry.AffinePushforward

/-! ### `δ` and restriction to an open of the base -/

section DeltaRestrict

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (J : Y.IdealSheafData) (m : ℕ)
  (F : X.Modules) [F.IsQuasicoherent]

/-- **The two ways of pulling `𝒥` back to `f ⁻¹ U` agree.** Restricting `𝒥` to `U` and then
pulling back along `f ∣_ U` gives the same ideal sheaf as pulling `𝒥` back along `f` and then
restricting to `f ⁻¹ U`. -/
public theorem comap_comap_morphismRestrict :
    (J.comap U.ι).comap (f ∣_ U) = (J.comap f).comap (f ⁻¹ᵁ U).ι :=
  (Scheme.IdealSheafData.comap_comp J (f ∣_ U) U.ι).symm.trans
    ((congrArg J.comap (morphismRestrict_ι f U)).trans
      (Scheme.IdealSheafData.comap_comp J (f ⁻¹ᵁ U).ι f))

/-- **The target of `δ_m` under restriction to `U`.** The restriction to `U` of
`f_*(𝓕 / ℐ ᵐ 𝓕)` is `(f ∣_ U)_*(𝓕|_{f ⁻¹ U} / (𝒥|_U)|_{f ⁻¹ U} ᵐ 𝓕|_{f ⁻¹ U})`, the target of
`δ_m` for `f ∣_ U`: the base-change isomorphism
`Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso` followed by the direct image
along `f ∣_ U` of `Stacks.Algebraization.restrictIdealPowerQuotientCongrIso`. -/
public def directImageQuotientRestrictTargetIso :
    (Scheme.Modules.restrictFunctor U.ι).obj
        ((Scheme.Modules.pushforward f).obj (idealPowerQuotient (J.comap f) m F)) ≅
      (Scheme.Modules.pushforward (f ∣_ U)).obj
        (idealPowerQuotient ((J.comap U.ι).comap (f ∣_ U)) m
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj F)) :=
  (restrictPushforwardIso f U).app (idealPowerQuotient (J.comap f) m F) ≪≫
    (Scheme.Modules.pushforward (f ∣_ U)).mapIso
      (restrictIdealPowerQuotientCongrIso (f ⁻¹ᵁ U).ι (J.comap f) m F
        (comap_comap_morphismRestrict f U J))

/-- **The source of `δ_m` under restriction to `U`.** The restriction to `U` of
`(f_*𝓕) / 𝒥 ᵐ (f_*𝓕)` is `((f ∣_ U)_*(𝓕|_{f ⁻¹ U})) / (𝒥|_U) ᵐ (…)`, the source of `δ_m` for
`f ∣_ U`: `Stacks.Algebraization.restrictIdealPowerQuotientIso` followed by the reduction modulo
`(𝒥|_U) ᵐ` of the base-change isomorphism. Here `f_*𝓕` is assumed quasi-coherent. -/
public def directImageQuotientRestrictSourceIso
    [((Scheme.Modules.pushforward f).obj F).IsQuasicoherent] :
    (Scheme.Modules.restrictFunctor U.ι).obj
        (idealPowerQuotient J m ((Scheme.Modules.pushforward f).obj F)) ≅
      idealPowerQuotient (J.comap U.ι) m
        ((Scheme.Modules.pushforward (f ∣_ U)).obj
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj F)) :=
  (restrictIdealPowerQuotientIso U.ι J m ((Scheme.Modules.pushforward f).obj F)).symm ≪≫
    (idealPowerQuotientFunctor (J.comap U.ι) m).mapIso ((restrictPushforwardIso f U).app F)

/-- **`δ` commutes with restriction to an open of the base, in normalized form.** Both sides are
read out of `f_*𝓕` restricted to `U`: on the left by the restriction of the quotient projection
of `f_*𝓕` followed by the restriction of `δ_m`, on the right by the base-change isomorphism
followed by the quotient projection of `(f ∣_ U)_*(𝓕|_{f ⁻¹ U})` and by `δ_m` for `f ∣_ U`. No
hypothesis on `f_*𝓕` is needed. -/
public theorem directImageQuotientComparison_restrict_π :
    (Scheme.Modules.restrictFunctor U.ι).map
        (cokernel.π (C := Y.Modules)
          (idealPowerMultiple J m ((Scheme.Modules.pushforward f).obj F)).ι) ≫
      (Scheme.Modules.restrictFunctor U.ι).map
          (directImageQuotientComparison f J m F) ≫
        (directImageQuotientRestrictTargetIso f U J m F).hom =
    (restrictPushforwardIso f U).hom.app F ≫
      cokernel.π (C := U.toScheme.Modules)
          (idealPowerMultiple (J.comap U.ι) m
            ((Scheme.Modules.pushforward (f ∣_ U)).obj
              ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj F))).ι ≫
        directImageQuotientComparison (f ∣_ U) (J.comap U.ι) m
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj F) := by
  have hnat := (restrictPushforwardIso f U).hom.naturality
    (cokernel.π (C := X.Modules) (idealPowerMultiple (J.comap f) m F).ι)
  simp only [Functor.comp_map] at hnat
  have hq := restrictIdealPowerQuotientCongrIso_π (f ⁻¹ᵁ U).ι (J.comap f) m F
    (comap_comap_morphismRestrict f U J)
  have hR := directImageQuotientComparison_π (f ∣_ U) (J.comap U.ι) m
    ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj F)
  rw [← Category.assoc, ← Functor.map_comp, directImageQuotientComparison_π,
    directImageQuotientRestrictTargetIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    ← Category.assoc, hnat, Category.assoc, ← Functor.map_comp, hq, hR]

/-- **`δ` commutes with restriction to an open of the base.** The restriction to `U` of the
comparison `δ_m` for `f` is the comparison `δ_m` for `f ∣_ U` and the restricted data, read
through `Stacks.Coherent.directImageQuotientRestrictSourceIso` and
`Stacks.Coherent.directImageQuotientRestrictTargetIso`. -/
public theorem directImageQuotientComparison_restrict
    [((Scheme.Modules.pushforward f).obj F).IsQuasicoherent] :
    (Scheme.Modules.restrictFunctor U.ι).map (directImageQuotientComparison f J m F) =
      (directImageQuotientRestrictSourceIso f U J m F).hom ≫
        directImageQuotientComparison (f ∣_ U) (J.comap U.ι) m
            ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj F) ≫
          (directImageQuotientRestrictTargetIso f U J m F).inv := by
  have hS : (Scheme.Modules.restrictFunctor U.ι).map
        (cokernel.π (C := Y.Modules)
          (idealPowerMultiple J m ((Scheme.Modules.pushforward f).obj F)).ι) ≫
      (directImageQuotientRestrictSourceIso f U J m F).hom =
      (restrictPushforwardIso f U).hom.app F ≫
        cokernel.π (C := U.toScheme.Modules)
          (idealPowerMultiple (J.comap U.ι) m
            ((Scheme.Modules.pushforward (f ∣_ U)).obj
              ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj F))).ι :=
    (Category.assoc (obj := U.toScheme.Modules) _ _ _).symm.trans
      ((congrArg (fun z => z ≫ idealPowerQuotientMap (J.comap U.ι) (J.comap U.ι) m m le_rfl
            ((restrictPushforwardIso f U).hom.app F))
          (restrictFunctor_map_cokernel_π_comp_restrictIdealPowerQuotientIso_inv U.ι J m
            ((Scheme.Modules.pushforward f).obj F))).trans
        (idealPowerQuotientMap_π (J.comap U.ι) (J.comap U.ι) m m le_rfl
          ((restrictPushforwardIso f U).hom.app F)))
  rw [← cancel_epi ((Scheme.Modules.restrictFunctor U.ι).map
      (cokernel.π (C := Y.Modules)
        (idealPowerMultiple J m ((Scheme.Modules.pushforward f).obj F)).ι)),
    ← cancel_mono (directImageQuotientRestrictTargetIso f U J m F).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, reassoc_of% hS]
  exact directImageQuotientComparison_restrict_π f U J m F

end DeltaRestrict

/-! ### `γ_n` and restriction to an open of the base -/

section GammaRestrict

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) (U : Y.Opens)
  (J : Y.IdealSheafData) (G : CoherentAdicSystems J)
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
  (β : (coherentAdicPullback f J).obj G ≅ (completionFunctor X (J.comap f)).obj F)

/-- **`γ_n` carried to the comparison for `f ⁻¹ U ⟶ U`.** The restriction to `U` of
`γ_n = 𝒢_n ⟶ f_*f^*𝒢_n ⟶ f_*(𝓕/ℐ ⁿ⁺¹𝓕)`, followed by the base-change isomorphism, is the
restriction of the adjunction map followed by the base-change isomorphism and the direct image
along `f ∣_ U` of the restriction of `β_n`. -/
public theorem directImageComparison_app_restrict (n : ℕᵒᵖ) :
    (Scheme.Modules.restrictFunctor U.ι).map
        ((directImageComparison f J G F β).app n) ≫
      (restrictPushforwardIso f U).hom.app
        (((completionFunctor X (J.comap f)).obj F).obj.obj n) =
    (Scheme.Modules.restrictFunctor U.ι).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (G.obj.obj n)) ≫
      (restrictPushforwardIso f U).hom.app
          ((Scheme.Modules.pullback f).obj (G.obj.obj n)) ≫
        (Scheme.Modules.pushforward (f ∣_ U)).map
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map (β.hom.hom.app n)) := by
  have hnat := (restrictPushforwardIso f U).hom.naturality (β.hom.hom.app n)
  simp only [Functor.comp_map] at hnat
  rw [directImageComparison_app, Functor.map_comp, Category.assoc]
  exact congrArg _ hnat

/-- **`γ_n` carried to the comparison for `f ⁻¹ U ⟶ U`, intrinsically.** The restriction to `U` of
`γ_n`, followed by the base-change isomorphism, is literally `γ_n` for `f ∣_ U`: the adjunction
map of `f ∣_ U` followed by `(f ∣_ U)_*` of

`β'_n = (f ∣_ U)^*(𝒢_n|_U) ⟶ (f^*𝒢_n)|_{f ⁻¹ U} ⟶ (𝓕/ℐ ⁿ⁺¹𝓕)|_{f ⁻¹ U}`,

the restriction of `β_n` read through
`Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictIso`. -/
public theorem directImageComparison_app_restrict_unit (n : ℕᵒᵖ) :
    (Scheme.Modules.restrictFunctor U.ι).map
        ((directImageComparison f J G F β).app n) ≫
      (restrictPushforwardIso f U).hom.app
        (((completionFunctor X (J.comap f)).obj F).obj.obj n) =
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app
        ((Scheme.Modules.restrictFunctor U.ι).obj (G.obj.obj n)) ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map
        ((pullbackRestrictIso f U).inv.app (G.obj.obj n) ≫
          (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map (β.hom.hom.app n)) := by
  rw [directImageComparison_app_restrict, ← Category.assoc,
    pullbackPushforwardAdjunction_unit_restrict, Category.assoc, ← Functor.map_comp]

end GammaRestrict

end Stacks.Coherent

end
