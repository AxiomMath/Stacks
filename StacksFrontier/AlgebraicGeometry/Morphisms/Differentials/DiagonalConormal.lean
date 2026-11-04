module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AffineGenerators
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.ReesPullback
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Sheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.RestrictOpen

/-!
# Tag 08S2: the derivation `s₂ - s₁` into the conormal sheaf of the diagonal

Let `f : X ⟶ S` be a morphism of schemes and let `Δ : X ⟶ X ×_S X` be its diagonal, an immersion
by Mathlib's `AlgebraicGeometry.IsImmersion` instance for `pullback.diagonal`.  [Stacks, Tag
08S2] identifies `Ω_{X/S}` with the conormal sheaf `𝒞_{X/X ×_S X}` of `Δ`, the identification
being induced by the `S`-derivation `d = s₂ - s₁` sending a local section `b` of `𝒪_X` to the
conormal class of `p₂^♯ b - p₁^♯ b`.

This file constructs that derivation and the canonical map `Ω_{X/S} ⟶ 𝒞_{X/X ×_S X}` it induces,
together with the formula and the uniqueness.

For any immersion `i : Z ⟶ Y`, a section of `𝒪_Y` over an open `U` whose pullback to `Z` vanishes
has a conormal class in `𝒞_{Z/Y}`; that class is additive, semilinear, compatible with
restriction, and zero on products of two vanishing sections.

## Main definitions

* `Stacks.Conormal.idealSectionOf`: a section of `𝒪_Y` over `U` killed by `i`, read as a section
  of the ideal sheaf of the canonical closed-immersion factorization `i.liftCoborder`.
* `Stacks.Conormal.conormalClass`: its class in the conormal sheaf of Tag 01R2.
* `Stacks.Diagonal.prodOpen`: the open `p₁⁻¹U ∩ p₂⁻¹U` of `X ×_S X`.
* `Stacks.Diagonal.diffSection`: the section `p₂^♯ b - p₁^♯ b` of `𝒪_{X ×_S X}` over it.
* `Stacks.Diagonal.diagonalD`: the conormal class of `p₂^♯ b - p₁^♯ b`, that is, `d b`.
* `Stacks.Diagonal.conormalDerivation`: `d = s₂ - s₁` as a relative derivation of `𝒪_X` over
  `f⁻¹𝒪_S` with values in `𝒞_{X/X ×_S X}`.
* `Stacks.Diagonal.differentialsToConormal`: the induced canonical map
  `Ω_{X/S} ⟶ 𝒞_{X/X ×_S X}`.

## Main results

* `Stacks.Conormal.pullbackSection_add`, `Stacks.Conormal.pullbackSection_zero` and
  `Stacks.Conormal.pullbackSection_smul_le`: additivity and semilinearity of
  `AlgebraicGeometry.Scheme.Modules.pullbackSection` over an open below the preimage.
* `Stacks.Conormal.conormalClass_add`, `Stacks.Conormal.conormalClass_mul_left`,
  `Stacks.Conormal.conormalClass_mul_of_both` and `Stacks.Conormal.conormalClass_restrict`: the
  conormal class is additive, semilinear, zero on products of two vanishing sections, and
  compatible with restriction.
* `Stacks.Conormal.affineConormalIsoCotangent_hom_conormalClass`: on an affine chart with
  `Z ∩ U = Spec (Γ(Y, U) ⧸ I)`, the conormal class of a generator `a ∈ I` is `I.toCotangent a`
  under the identification of Tag 01R3 (2).
* `Stacks.Diagonal.diffSection_mul`: the Leibniz identity for `p₂^♯ - p₁^♯`, with its error term
  made explicit.
* `Stacks.Diagonal.differentialsToConormal_d` and `Stacks.Diagonal.eq_differentialsToConormal`:
  the canonical map carries `d b` to the conormal class of `p₂^♯ b - p₁^♯ b`, and is the only
  morphism of `𝒪_X`-modules that does.

## References

* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01KJ](https://stacks.math.columbia.edu/tag/01KJ)
* [Stacks Project, Tag 01UP](https://stacks.math.columbia.edu/tag/01UP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Conormal

/-- The maps on sections of two equal morphisms of schemes agree. -/
theorem appLE_eq_of_eq {W Y : Scheme.{u}} {a b : W ⟶ Y} (hab : a = b) (U : Y.Opens)
    (V : W.Opens) (ea : V ≤ a ⁻¹ᵁ U) (eb : V ≤ b ⁻¹ᵁ U) :
    a.appLE U V ea = b.appLE U V eb := by
  subst hab; rfl

/-! ### Additivity and semilinearity of the pullback of a section -/

section PullbackSection

variable {Z Y : Scheme.{u}} (a : Z ⟶ Y) (F : Y.Modules) (U : Y.Opens) (V : Z.Opens)
  (h : V ≤ a ⁻¹ᵁ U)

/-- Pulling a section back is additive. -/
theorem pullbackSection_add (x y : F.val.obj (op U)) :
    Scheme.Modules.pullbackSection a F U V h (x + y) =
      Scheme.Modules.pullbackSection a F U V h x +
        Scheme.Modules.pullbackSection a F U V h y :=
  (congrArg
      (ConcreteCategory.hom (((Scheme.Modules.pullback a).obj F).val.map (homOfLE h).op))
      (map_add (ConcreteCategory.hom
        (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app F).val.app (op U)))
        x y)).trans
    (map_add _ _ _)

/-- Pulling the zero section back gives zero. -/
theorem pullbackSection_zero : Scheme.Modules.pullbackSection a F U V h 0 = 0 :=
  (congrArg
      (ConcreteCategory.hom (((Scheme.Modules.pullback a).obj F).val.map (homOfLE h).op))
      (map_zero (ConcreteCategory.hom
        (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app F).val.app (op U))))).trans
    (map_zero _)

/-- Pulling a section back is semilinear, over an open `V` of the source contained in the
preimage of `U`. -/
theorem pullbackSection_smul_le (r : Y.ringCatSheaf.obj.obj (op U)) (x : F.val.obj (op U)) :
    Scheme.Modules.pullbackSection a F U V h (r • x) =
      (show Z.ringCatSheaf.obj.obj (op V) from
          (a.appLE U V h).hom (show Γ(Y, U) from r)) •
        Scheme.Modules.pullbackSection a F U V h x := by
  refine (pullbackSection_restrict_target a F U (a ⁻¹ᵁ U) V le_rfl h (r • x)).symm.trans ?_
  refine Eq.trans ?_ (congrArg
    (fun y => (show Z.ringCatSheaf.obj.obj (op V) from
        (a.appLE U V h).hom (show Γ(Y, U) from r)) • y)
    (pullbackSection_restrict_target a F U (a ⁻¹ᵁ U) V le_rfl h x))
  refine (congrArg
    (ConcreteCategory.hom (((Scheme.Modules.pullback a).obj F).val.map (homOfLE h).op))
    (pullbackSection_smul a F U r x)).trans ?_
  exact PresheafOfModules.map_smul (((Scheme.Modules.pullback a).obj F).val) (homOfLE h).op _ _

end PullbackSection

/-! ### The ideal-sheaf section attached to a vanishing function -/

variable {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsImmersion i]

/-- A section of `𝒪_Y` over `U` killed by an immersion `i` lies in the ideal of the canonical
closed-immersion factorization of `i`. -/
theorem mem_ker_app_liftCoborder (U : Y.Opens) (r : Γ(Y, U)) (hr : (i.app U).hom r = 0) :
    (i.coborderRange.ι.app U).hom r ∈
      RingHom.ker (i.liftCoborder.app (i.coborderRange.ι ⁻¹ᵁ U)).hom := by
  have key : ∀ (g : Z ⟶ Y) (_hg : i.liftCoborder ≫ i.coborderRange.ι = g)
      (_hg' : (g.app U).hom r = 0),
      (i.coborderRange.ι.app U).hom r ∈
        RingHom.ker (i.liftCoborder.app (i.coborderRange.ι ⁻¹ᵁ U)).hom := by
    intro g hg hg'
    subst hg
    rw [Scheme.Hom.comp_app] at hg'
    exact RingHom.mem_ker.mpr hg'
  exact key i i.liftCoborder_ι hr

/-- Two sections of the ideal sheaf of a closed immersion with the same image in the structure
sheaf are equal. -/
theorem kernelι_inj {W C : Scheme.{u}} (a : W ⟶ C) (O : C.Opens)
    {x y : (Stacks.ClosedImmersion.idealSheaf a.toLRSHom.toShHom).val.obj (op O)}
    (h : (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom a.toLRSHom.toShHom))).val.app (op O) x =
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom a.toLRSHom.toShHom))).val.app (op O) y) :
    x = y :=
  kernelι_val_app_injective a O h

/-- The section of the ideal sheaf of `i.liftCoborder` determined by a section of `𝒪_Y` over `U`
killed by `i`. -/
def idealSectionOf (U : Y.Opens) (r : Γ(Y, U)) (hr : (i.app U).hom r = 0) :
    (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom).val.obj
      (op (i.coborderRange.ι ⁻¹ᵁ U)) :=
  (idealSheafSectionsIso i.liftCoborder (i.coborderRange.ι ⁻¹ᵁ U)).inv.hom
    ⟨(i.coborderRange.ι.app U).hom r, mem_ker_app_liftCoborder i U r hr⟩

/-- `Stacks.Conormal.idealSectionOf` depends only on the section, not on the proof that it
vanishes. -/
theorem idealSectionOf_congr (U : Y.Opens) {r r' : Γ(Y, U)} (hrr' : r = r')
    (hr : (i.app U).hom r = 0) (hr' : (i.app U).hom r' = 0) :
    idealSectionOf i U r hr = idealSectionOf i U r' hr' := by
  subst hrr'; rfl

/-- `Stacks.Conormal.idealSectionOf` lies over the given section of `𝒪_Y`. -/
theorem kernelι_idealSectionOf (U : Y.Opens) (r : Γ(Y, U)) (hr : (i.app U).hom r = 0) :
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i.liftCoborder.toLRSHom.toShHom))).val.app
          (op (i.coborderRange.ι ⁻¹ᵁ U)) (idealSectionOf i U r hr) =
      (i.coborderRange.ι.app U).hom r := by
  rw [← idealSheafSectionsIso_hom_coe]
  exact congrArg
    (fun z : ↥(RingHom.ker (i.liftCoborder.app (i.coborderRange.ι ⁻¹ᵁ U)).hom) =>
      (z : Γ(i.coborderRange.toScheme, i.coborderRange.ι ⁻¹ᵁ U)))
    ((idealSheafSectionsIso i.liftCoborder (i.coborderRange.ι ⁻¹ᵁ U)).inv_hom_id_apply _)

/-- `Stacks.Conormal.idealSectionOf` is additive. -/
theorem idealSectionOf_add (U : Y.Opens) (r r' : Γ(Y, U))
    (hr : (i.app U).hom r = 0) (hr' : (i.app U).hom r' = 0)
    (hsum : (i.app U).hom (r + r') = 0) :
    idealSectionOf i U (r + r') hsum =
      idealSectionOf i U r hr + idealSectionOf i U r' hr' := by
  refine Eq.trans (congrArg
    (ConcreteCategory.hom
      (idealSheafSectionsIso i.liftCoborder (i.coborderRange.ι ⁻¹ᵁ U)).inv)
    (Subtype.ext (map_add (i.coborderRange.ι.app U).hom r r') :
      (⟨(i.coborderRange.ι.app U).hom (r + r'),
          mem_ker_app_liftCoborder i U (r + r') hsum⟩ :
        ↥(RingHom.ker (i.liftCoborder.app (i.coborderRange.ι ⁻¹ᵁ U)).hom)) =
      ⟨(i.coborderRange.ι.app U).hom r, mem_ker_app_liftCoborder i U r hr⟩ +
        ⟨(i.coborderRange.ι.app U).hom r', mem_ker_app_liftCoborder i U r' hr'⟩)) ?_
  exact map_add _ _ _

/-- `Stacks.Conormal.idealSectionOf` of `0` is `0`. -/
theorem idealSectionOf_zero (U : Y.Opens) (h0 : (i.app U).hom 0 = 0) :
    idealSectionOf i U 0 h0 = 0 := by
  refine Eq.trans (congrArg
    (ConcreteCategory.hom
      (idealSheafSectionsIso i.liftCoborder (i.coborderRange.ι ⁻¹ᵁ U)).inv)
    (Subtype.ext (map_zero (i.coborderRange.ι.app U).hom) :
      (⟨(i.coborderRange.ι.app U).hom 0, mem_ker_app_liftCoborder i U 0 h0⟩ :
        ↥(RingHom.ker (i.liftCoborder.app (i.coborderRange.ι ⁻¹ᵁ U)).hom)) = 0)) ?_
  exact map_zero _

/-- `Stacks.Conormal.idealSectionOf` is semilinear: multiplying the vanishing section by an
arbitrary section of `𝒪_Y` scales the section of the ideal sheaf. -/
theorem idealSectionOf_mul_left (U : Y.Opens) (s r : Γ(Y, U)) (hr : (i.app U).hom r = 0)
    (hsr : (i.app U).hom (s * r) = 0) :
    idealSectionOf i U (s * r) hsr =
      (show (structureSheafRing (i.coborderRange.toScheme).toRingedSpace).obj.obj
          (op (i.coborderRange.ι ⁻¹ᵁ U)) from (i.coborderRange.ι.app U).hom s) •
        idealSectionOf i U r hr := by
  refine kernelι_inj i.liftCoborder (i.coborderRange.ι ⁻¹ᵁ U) ?_
  refine Eq.trans (kernelι_idealSectionOf i U (s * r) hsr) ?_
  refine Eq.trans (map_mul (i.coborderRange.ι.app U).hom s r) ?_
  refine Eq.trans ?_ (map_smul (ConcreteCategory.hom
    ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom i.liftCoborder.toLRSHom.toShHom))).val.app
        (op (i.coborderRange.ι ⁻¹ᵁ U)))) _ _).symm
  exact congrArg (fun y : Γ(i.coborderRange.toScheme, i.coborderRange.ι ⁻¹ᵁ U) =>
      (i.coborderRange.ι.app U).hom s * y)
    (kernelι_idealSectionOf i U r hr).symm

/-- `Stacks.Conormal.idealSectionOf` is compatible with restriction. -/
theorem idealSectionOf_restrict (U U' : Y.Opens) (hU : U' ≤ U) (r : Γ(Y, U))
    (hr : (i.app U).hom r = 0)
    (hr' : (i.app U').hom ((Y.presheaf.map (homOfLE hU).op).hom r) = 0) :
    (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom).val.map
        (homOfLE (i.coborderRange.ι.preimage_mono hU)).op (idealSectionOf i U r hr) =
      idealSectionOf i U' ((Y.presheaf.map (homOfLE hU).op).hom r) hr' := by
  refine kernelι_inj i.liftCoborder (i.coborderRange.ι ⁻¹ᵁ U') ?_
  refine Eq.trans (PresheafOfModules.naturality_apply
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom i.liftCoborder.toLRSHom.toShHom))).val
    (homOfLE (i.coborderRange.ι.preimage_mono hU)).op (idealSectionOf i U r hr)) ?_
  rw [kernelι_idealSectionOf, kernelι_idealSectionOf]
  exact (congrArg
    (fun q : Γ(Y, U) ⟶ Γ(i.coborderRange.toScheme, i.coborderRange.ι ⁻¹ᵁ U') => q.hom r)
    (Scheme.Hom.naturality i.coborderRange.ι (homOfLE hU).op)).symm

/-! ### The conormal class of a vanishing function -/

/-- An open of `Z` below the preimage of `U` lies below the preimage of the corresponding open
of `i.coborderRange`. -/
theorem le_liftCoborder_preimage (U : Y.Opens) {V : Z.Opens} (hV : V ≤ i ⁻¹ᵁ U) :
    V ≤ i.liftCoborder ⁻¹ᵁ (i.coborderRange.ι ⁻¹ᵁ U) := by
  rwa [← Scheme.Hom.comp_preimage, i.liftCoborder_ι]

/-- The conormal class of a function vanishing on `Z`: for an immersion `i : Z ⟶ Y`, an
open `U` of `Y` and a section `r` of `𝒪_Y` over `U` whose pullback to `Z` vanishes, this is the
section of the conormal sheaf `𝒞_{Z/Y}` over an open `V ≤ i ⁻¹ᵁ U` given by the class of `r`
modulo the square of the ideal. -/
def conormalClass (U : Y.Opens) {V : Z.Opens} (hV : V ≤ i ⁻¹ᵁ U) (r : Γ(Y, U))
    (hr : (i.app U).hom r = 0) : (conormalSheaf i).val.obj (op V) :=
  Scheme.Modules.pullbackSection i.liftCoborder
    (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom)
    (i.coborderRange.ι ⁻¹ᵁ U) V (le_liftCoborder_preimage i U hV) (idealSectionOf i U r hr)

/-- `Stacks.Conormal.conormalClass` depends only on the section, not on the proof that it
vanishes. -/
theorem conormalClass_congr (U : Y.Opens) {V : Z.Opens} (hV : V ≤ i ⁻¹ᵁ U) {r r' : Γ(Y, U)}
    (hrr' : r = r') (hr : (i.app U).hom r = 0) (hr' : (i.app U).hom r' = 0) :
    conormalClass i U hV r hr = conormalClass i U hV r' hr' := by
  subst hrr'; rfl

/-- The map on sections of an immersion factors through the map on sections of its canonical
closed-immersion factorization. -/
theorem appLE_liftCoborder_comp (U : Y.Opens) {V : Z.Opens} (hV : V ≤ i ⁻¹ᵁ U) :
    i.coborderRange.ι.app U ≫
        i.liftCoborder.appLE (i.coborderRange.ι ⁻¹ᵁ U) V (le_liftCoborder_preimage i U hV) =
      i.appLE U V hV := by
  have h1 := Scheme.Hom.appLE_comp_appLE i.liftCoborder i.coborderRange.ι U
    (i.coborderRange.ι ⁻¹ᵁ U) V le_rfl (le_liftCoborder_preimage i U hV)
  rw [Scheme.Hom.appLE_preimage_self] at h1
  exact h1.trans (appLE_eq_of_eq i.liftCoborder_ι U V _ hV)

/-- `Stacks.Conormal.conormalClass` is additive. -/
theorem conormalClass_add (U : Y.Opens) {V : Z.Opens} (hV : V ≤ i ⁻¹ᵁ U) (r r' : Γ(Y, U))
    (hr : (i.app U).hom r = 0) (hr' : (i.app U).hom r' = 0)
    (hsum : (i.app U).hom (r + r') = 0) :
    conormalClass i U hV (r + r') hsum =
      conormalClass i U hV r hr + conormalClass i U hV r' hr' := by
  unfold conormalClass
  rw [idealSectionOf_add i U r r' hr hr' hsum]
  exact pullbackSection_add _ _ _ _ _ _ _

/-- `Stacks.Conormal.conormalClass` of `0` is `0`. -/
theorem conormalClass_zero (U : Y.Opens) {V : Z.Opens} (hV : V ≤ i ⁻¹ᵁ U)
    (h0 : (i.app U).hom 0 = 0) : conormalClass i U hV 0 h0 = 0 := by
  unfold conormalClass
  rw [idealSectionOf_zero i U h0]
  exact pullbackSection_zero _ _ _ _ _

/-- `Stacks.Conormal.conormalClass` is semilinear: multiplying a vanishing function by an
arbitrary section of `𝒪_Y` scales its conormal class by the restriction of that section to `Z`. -/
theorem conormalClass_mul_left (U : Y.Opens) {V : Z.Opens} (hV : V ≤ i ⁻¹ᵁ U) (s r : Γ(Y, U))
    (hr : (i.app U).hom r = 0) (hsr : (i.app U).hom (s * r) = 0) :
    conormalClass i U hV (s * r) hsr =
      (show (structureSheafRing Z.toRingedSpace).obj.obj (op V) from (i.appLE U V hV).hom s) •
        conormalClass i U hV r hr := by
  unfold conormalClass
  rw [idealSectionOf_mul_left i U s r hr hsr]
  refine (pullbackSection_smul_le _ _ _ _ _ _ _).trans ?_
  exact congrArg
    (fun c : Γ(Z, V) => (show (structureSheafRing Z.toRingedSpace).obj.obj (op V) from c) •
      conormalClass i U hV r hr)
    (congrArg (fun q : Γ(Y, U) ⟶ Γ(Z, V) => q.hom s) (appLE_liftCoborder_comp i U hV))

/-- A product of two functions vanishing on `Z` has zero conormal class. -/
theorem conormalClass_mul_of_both (U : Y.Opens) {V : Z.Opens} (hV : V ≤ i ⁻¹ᵁ U) (s r : Γ(Y, U))
    (hs : (i.app U).hom s = 0) (hr : (i.app U).hom r = 0)
    (hsr : (i.app U).hom (s * r) = 0) : conormalClass i U hV (s * r) hsr = 0 := by
  have hz : (i.appLE U V hV).hom s = 0 := by
    rw [Scheme.Hom.appLE]
    exact Eq.trans (CommRingCat.comp_apply (i.app U) (Z.presheaf.map (homOfLE hV).op) s)
      (Eq.trans (congrArg (ConcreteCategory.hom (Z.presheaf.map (homOfLE hV).op)) hs)
        (map_zero _))
  refine Eq.trans (conormalClass_mul_left i U hV s r hr hsr) ?_
  refine Eq.trans (congrArg
    (fun c : Γ(Z, V) => (show (structureSheafRing Z.toRingedSpace).obj.obj (op V) from c) •
      conormalClass i U hV r hr) hz) ?_
  exact zero_smul _ _

/-- `Stacks.Conormal.conormalClass` is compatible with restriction. -/
theorem conormalClass_restrict (U U' : Y.Opens) (hU : U' ≤ U) {V V' : Z.Opens}
    (hV : V ≤ i ⁻¹ᵁ U) (hV' : V' ≤ i ⁻¹ᵁ U') (hVV' : V' ≤ V) (r : Γ(Y, U))
    (hr : (i.app U).hom r = 0)
    (hr' : (i.app U').hom ((Y.presheaf.map (homOfLE hU).op).hom r) = 0) :
    (conormalSheaf i).val.map (homOfLE hVV').op (conormalClass i U hV r hr) =
      conormalClass i U' hV' ((Y.presheaf.map (homOfLE hU).op).hom r) hr' := by
  unfold conormalClass
  refine (pullbackSection_restrict_target i.liftCoborder _ (i.coborderRange.ι ⁻¹ᵁ U) V V'
    (le_liftCoborder_preimage i U hV) hVV' _).trans ?_
  refine (pullbackSection_restrict_source i.liftCoborder _ (i.coborderRange.ι ⁻¹ᵁ U)
    (i.coborderRange.ι ⁻¹ᵁ U') (i.coborderRange.ι.preimage_mono hU) V'
    (le_liftCoborder_preimage i U' hV') _).trans ?_
  exact congrArg _ (idealSectionOf_restrict i U U' hU r hr hr')

/-! ### The conormal class on an affine chart -/

/-- On an affine chart `U` with `Z ∩ U = Spec (Γ(Y, U) ⧸ I)`, the identification
`Stacks.Conormal.affineConormalIsoCotangent` of [Stacks, Tag 01R3] (2) carries the conormal class
of a generator `a ∈ I` to its class `I.toCotangent a` in `I/I²`. -/
theorem affineConormalIsoCotangent_hom_conormalClass (U : Y.Opens) (hU : IsAffineOpen U)
    (I : Ideal Γ(Y, U)) (e : pullback i U.ι ≅ Spec (.of (Γ(Y, U) ⧸ I)))
    (he : pullback.snd i U.ι ≫ hU.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (a : I) (ha : (i.app U).hom (a : Γ(Y, U)) = 0) :
    (affineConormalIsoCotangent i U hU I e he).hom.hom
        (conormalClass i U (le_refl (i ⁻¹ᵁ U)) (a : Γ(Y, U)) ha) = I.toCotangent a :=
  affineConormalIsoCotangent_hom_pullbackSection i U hU I e he
    (le_liftCoborder_preimage i U (le_refl (i ⁻¹ᵁ U))) a
    (idealSectionOf i U (a : Γ(Y, U)) ha)
    (kernelι_idealSectionOf i U (a : Γ(Y, U)) ha).symm

/-- On an affine chart `U` with `Z ∩ U = Spec (Γ(Y, U) ⧸ I)`, the inverse of the identification
`Stacks.Conormal.affineConormalIsoCotangent` carries `I.toCotangent a` to the conormal class of
`a ∈ I`. -/
theorem affineConormalIsoCotangent_inv_toCotangent_conormalClass (U : Y.Opens)
    (hU : IsAffineOpen U) (I : Ideal Γ(Y, U))
    (e : pullback i U.ι ≅ Spec (.of (Γ(Y, U) ⧸ I)))
    (he : pullback.snd i U.ι ≫ hU.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (a : I) (ha : (i.app U).hom (a : Γ(Y, U)) = 0) :
    (affineConormalIsoCotangent i U hU I e he).inv.hom (I.toCotangent a) =
      conormalClass i U (le_refl (i ⁻¹ᵁ U)) (a : Γ(Y, U)) ha := by
  conv_lhs => rw [← affineConormalIsoCotangent_hom_conormalClass i U hU I e he a ha]
  exact (affineConormalIsoCotangent i U hU I e he).hom_inv_id_apply _

end Stacks.Conormal

namespace Stacks.Diagonal

open Stacks.Conormal

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### The product open and the difference of the two pullbacks -/

/-- The open `p₁⁻¹U ∩ p₂⁻¹U` of `X ×_S X`. -/
def prodOpen (U : X.Opens) : (pullback f f).Opens :=
  (pullback.fst f f ⁻¹ᵁ U) ⊓ (pullback.snd f f ⁻¹ᵁ U)

/-- `Stacks.Diagonal.prodOpen f U` lies in `p₁⁻¹U`. -/
theorem prodOpen_le_fst (U : X.Opens) : prodOpen f U ≤ pullback.fst f f ⁻¹ᵁ U := inf_le_left

/-- `Stacks.Diagonal.prodOpen f U` lies in `p₂⁻¹U`. -/
theorem prodOpen_le_snd (U : X.Opens) : prodOpen f U ≤ pullback.snd f f ⁻¹ᵁ U := inf_le_right

/-- `Stacks.Diagonal.prodOpen f` is monotone. -/
theorem prodOpen_mono {U U' : X.Opens} (h : U' ≤ U) : prodOpen f U' ≤ prodOpen f U :=
  inf_le_inf ((pullback.fst f f).preimage_mono h) ((pullback.snd f f).preimage_mono h)

/-- The preimage of `p₁⁻¹U` under the diagonal is `U`. -/
theorem diagonal_preimage_fst_preimage (U : X.Opens) :
    pullback.diagonal f ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ U) = U := by
  rw [← Scheme.Hom.comp_preimage, pullback.diagonal_fst, Scheme.Hom.id_preimage]

/-- The preimage of `p₂⁻¹U` under the diagonal is `U`. -/
theorem diagonal_preimage_snd_preimage (U : X.Opens) :
    pullback.diagonal f ⁻¹ᵁ (pullback.snd f f ⁻¹ᵁ U) = U := by
  rw [← Scheme.Hom.comp_preimage, pullback.diagonal_snd, Scheme.Hom.id_preimage]

/-- The preimage of `Stacks.Diagonal.prodOpen f U` under the diagonal is `U`. -/
theorem diagonal_preimage_prodOpen (U : X.Opens) :
    pullback.diagonal f ⁻¹ᵁ prodOpen f U = U := by
  show (pullback.diagonal f ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ U)) ⊓
    (pullback.diagonal f ⁻¹ᵁ (pullback.snd f f ⁻¹ᵁ U)) = U
  rw [diagonal_preimage_fst_preimage, diagonal_preimage_snd_preimage, inf_idem]

/-- `U` lies in the preimage of `Stacks.Diagonal.prodOpen f U` under the diagonal. -/
theorem le_diagonal_preimage_prodOpen (U : X.Opens) :
    U ≤ pullback.diagonal f ⁻¹ᵁ prodOpen f U :=
  le_of_eq (diagonal_preimage_prodOpen f U).symm

/-- `p₂^♯ b - p₁^♯ b`, a section of the structure sheaf of `X ×_S X` over `prodOpen f U`. -/
def diffSection (U : X.Opens) (b : Γ(X, U)) : Γ(pullback f f, prodOpen f U) :=
  ((pullback.snd f f).appLE U (prodOpen f U) (prodOpen_le_snd f U)).hom b -
    ((pullback.fst f f).appLE U (prodOpen f U) (prodOpen_le_fst f U)).hom b

/-- `Stacks.Diagonal.diffSection` is additive. -/
theorem diffSection_add (U : X.Opens) (b b' : Γ(X, U)) :
    diffSection f U (b + b') = diffSection f U b + diffSection f U b' := by
  simp only [diffSection, map_add]
  abel

/-- `Stacks.Diagonal.diffSection` of `1` is `0`. -/
theorem diffSection_one (U : X.Opens) : diffSection f U 1 = 0 := by
  simp only [diffSection, map_one, sub_self]

/-- The Leibniz identity for `p₂^♯ - p₁^♯`: the difference of the two pullbacks of a product is
a combination of the differences of the factors, plus the product of the two differences. -/
theorem diffSection_mul (U : X.Opens) (a b : Γ(X, U)) :
    diffSection f U (a * b) =
      ((pullback.fst f f).appLE U (prodOpen f U) (prodOpen_le_fst f U)).hom a *
          diffSection f U b +
        (((pullback.fst f f).appLE U (prodOpen f U) (prodOpen_le_fst f U)).hom b *
            diffSection f U a +
          diffSection f U a * diffSection f U b) := by
  simp only [diffSection, map_mul]
  ring

/-- For a projection `p` with `Δ ≫ p = 𝟙 X`, the pullback of `p^♯ b` along the diagonal is the
restriction of `b`. -/
theorem diagonal_appLE_proj (U W : X.Opens) (p : pullback f f ⟶ X)
    (hp : pullback.diagonal f ≫ p = 𝟙 X) (e : prodOpen f U ≤ p ⁻¹ᵁ U)
    (hW : W ≤ pullback.diagonal f ⁻¹ᵁ prodOpen f U) (hid : W ≤ U) (b : Γ(X, U)) :
    ((pullback.diagonal f).appLE (prodOpen f U) W hW).hom ((p.appLE U (prodOpen f U) e).hom b)
      = (X.presheaf.map (homOfLE hid).op).hom b := by
  have hid' : (𝟙 X : X ⟶ X).appLE U W hid = X.presheaf.map (homOfLE hid).op := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact Category.id_comp _
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq hp U W _ hid, hid']

/-- Restricting a section to the same open leaves it unchanged. -/
theorem map_homOfLE_self_apply (U : X.Opens) (hid : U ≤ U) (b : Γ(X, U)) :
    (X.presheaf.map (homOfLE hid).op).hom b = b := by
  rw [show (homOfLE hid).op = 𝟙 (op U) from Subsingleton.elim _ _,
    X.presheaf.map_id (op U)]
  rfl

/-- The difference `p₂^♯ b - p₁^♯ b` is killed by the diagonal. -/
theorem appLE_diffSection (U W : X.Opens)
    (hW : W ≤ pullback.diagonal f ⁻¹ᵁ prodOpen f U) (b : Γ(X, U)) :
    ((pullback.diagonal f).appLE (prodOpen f U) W hW).hom (diffSection f U b) = 0 := by
  have hid : W ≤ U := hW.trans (le_of_eq (diagonal_preimage_prodOpen f U))
  rw [diffSection, map_sub,
    diagonal_appLE_proj f U W (pullback.snd f f) (pullback.diagonal_snd f)
      (prodOpen_le_snd f U) hW hid b,
    diagonal_appLE_proj f U W (pullback.fst f f) (pullback.diagonal_fst f)
      (prodOpen_le_fst f U) hW hid b, sub_self]

/-- The difference `p₂^♯ b - p₁^♯ b` is killed by the map on sections of the diagonal over
`Stacks.Diagonal.prodOpen f U`. -/
theorem app_diffSection (U : X.Opens) (b : Γ(X, U)) :
    ((pullback.diagonal f).app (prodOpen f U)).hom (diffSection f U b) = 0 := by
  rw [← Scheme.Hom.appLE_preimage_self (pullback.diagonal f) (prodOpen f U)]
  exact appLE_diffSection f U _ le_rfl b

/-- The restriction of `p₁^♯ b` along the diagonal is `b`. -/
theorem appLE_diagonal_fst_appLE (U : X.Opens) (b : Γ(X, U)) :
    ((pullback.diagonal f).appLE (prodOpen f U) U (le_diagonal_preimage_prodOpen f U)).hom
        (((pullback.fst f f).appLE U (prodOpen f U) (prodOpen_le_fst f U)).hom b) = b :=
  (diagonal_appLE_proj f U U (pullback.fst f f) (pullback.diagonal_fst f)
    (prodOpen_le_fst f U) (le_diagonal_preimage_prodOpen f U) le_rfl b).trans
    (map_homOfLE_self_apply U le_rfl b)

/-- The difference `p₂^♯ - p₁^♯` is compatible with restriction. -/
theorem diffSection_restrict {U U' : X.Opens} (hU : U' ≤ U) (b : Γ(X, U)) :
    ((pullback f f).presheaf.map (homOfLE (prodOpen_mono f hU)).op).hom (diffSection f U b) =
      diffSection f U' ((X.presheaf.map (homOfLE hU).op).hom b) := by
  have key : ∀ (p : pullback f f ⟶ X) (e : prodOpen f U ≤ p ⁻¹ᵁ U)
      (e' : prodOpen f U' ≤ p ⁻¹ᵁ U'),
      ((pullback f f).presheaf.map (homOfLE (prodOpen_mono f hU)).op).hom
          ((p.appLE U (prodOpen f U) e).hom b) =
        (p.appLE U' (prodOpen f U') e').hom ((X.presheaf.map (homOfLE hU).op).hom b) := by
    intro p e e'
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map,
      Scheme.Hom.map_appLE]
  rw [diffSection, diffSection, map_sub, key (pullback.snd f f) _ _, key (pullback.fst f f) _ _]

/-- The difference `p₂^♯ - p₁^♯` kills the functions pulled back from the base. -/
theorem diffSection_app_eq_zero (W : S.Opens) (b : Γ(S, W)) :
    diffSection f (f ⁻¹ᵁ W) ((f.app W).hom b) = 0 := by
  have key : ∀ (p : pullback f f ⟶ X) (e : prodOpen f (f ⁻¹ᵁ W) ≤ p ⁻¹ᵁ (f ⁻¹ᵁ W))
      (hpf : p ≫ f = pullback.fst f f ≫ f)
      (e2 : prodOpen f (f ⁻¹ᵁ W) ≤ (pullback.fst f f ≫ f) ⁻¹ᵁ W),
      (p.appLE (f ⁻¹ᵁ W) (prodOpen f (f ⁻¹ᵁ W)) e).hom ((f.app W).hom b) =
        ((pullback.fst f f ≫ f).appLE W (prodOpen f (f ⁻¹ᵁ W)) e2).hom b := by
    intro p e hpf e2
    rw [← Scheme.Hom.appLE_preimage_self f W, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_comp_appLE]
    exact ConcreteCategory.congr_hom (appLE_eq_of_eq hpf W (prodOpen f (f ⁻¹ᵁ W)) _ e2) b
  rw [diffSection,
    key (pullback.snd f f) _ pullback.condition.symm (prodOpen_le_fst f (f ⁻¹ᵁ W)),
    key (pullback.fst f f) _ rfl (prodOpen_le_fst f (f ⁻¹ᵁ W)), sub_self]

/-! ### The relative derivation `d = s₂ - s₁` -/

/-- The derivation `d = s₂ - s₁` of [Stacks, Tag 08S2] on sections: a section `b` of `𝒪_X`
over `U` is sent to the conormal class of `p₂^♯ b - p₁^♯ b`. -/
def diagonalD (U : X.Opens) (b : Γ(X, U)) :
    (conormalSheaf (pullback.diagonal f)).val.obj (op U) :=
  conormalClass (pullback.diagonal f) (prodOpen f U) (le_diagonal_preimage_prodOpen f U)
    (diffSection f U b) (app_diffSection f U b)

/-- If `p₂^♯ b - p₁^♯ b = r`, then `d b` is the conormal class of `r`. -/
private theorem diagonalD_eq_conormalClass (U : X.Opens) (b : Γ(X, U))
    (r : Γ(pullback f f, prodOpen f U))
    (hbr : diffSection f U b = r) (hr : ((pullback.diagonal f).app (prodOpen f U)).hom r = 0) :
    diagonalD f U b =
      conormalClass (pullback.diagonal f) (prodOpen f U) (le_diagonal_preimage_prodOpen f U) r hr :=
  conormalClass_congr _ _ _ hbr _ _

/-- `Stacks.Diagonal.diagonalD` is additive. -/
theorem diagonalD_add (U : X.Opens) (b b' : Γ(X, U)) :
    diagonalD f U (b + b') = diagonalD f U b + diagonalD f U b' := by
  have h : ((pullback.diagonal f).app (prodOpen f U)).hom
      (diffSection f U b + diffSection f U b') = 0 := by
    rw [map_add, app_diffSection, app_diffSection, add_zero]
  refine (diagonalD_eq_conormalClass f U _ _ (diffSection_add f U b b') h).trans ?_
  exact conormalClass_add (pullback.diagonal f) (prodOpen f U)
    (le_diagonal_preimage_prodOpen f U) (diffSection f U b) (diffSection f U b')
    (app_diffSection f U b) (app_diffSection f U b') h

/-- `Stacks.Diagonal.diagonalD` vanishes on a section `b` with `p₂^♯ b = p₁^♯ b`. -/
theorem diagonalD_of_eq_zero (U : X.Opens) (b : Γ(X, U)) (hb : diffSection f U b = 0) :
    diagonalD f U b = 0 := by
  have h : ((pullback.diagonal f).app (prodOpen f U)).hom (0 : Γ(pullback f f, prodOpen f U))
      = 0 := map_zero _
  refine (diagonalD_eq_conormalClass f U b 0 hb h).trans ?_
  exact conormalClass_zero (pullback.diagonal f) (prodOpen f U)
    (le_diagonal_preimage_prodOpen f U) h

/-- `Stacks.Diagonal.diagonalD` of `1` is `0`. -/
theorem diagonalD_one (U : X.Opens) : diagonalD f U 1 = 0 :=
  diagonalD_of_eq_zero f U 1 (diffSection_one f U)

/-- The derivation `d = s₂ - s₁` satisfies the Leibniz rule. -/
theorem diagonalD_mul (U : X.Opens) (a b : Γ(X, U)) :
    diagonalD f U (a * b) =
      (show (structureSheafRing X.toRingedSpace).obj.obj (op U) from a) • diagonalD f U b +
        (show (structureSheafRing X.toRingedSpace).obj.obj (op U) from b) • diagonalD f U a := by
  have ha := app_diffSection f U a
  have hb := app_diffSection f U b
  have hA : ((pullback.diagonal f).app (prodOpen f U)).hom
      (((pullback.fst f f).appLE U (prodOpen f U) (prodOpen_le_fst f U)).hom a *
        diffSection f U b) = 0 := by rw [map_mul, hb, mul_zero]
  have hB : ((pullback.diagonal f).app (prodOpen f U)).hom
      (((pullback.fst f f).appLE U (prodOpen f U) (prodOpen_le_fst f U)).hom b *
        diffSection f U a) = 0 := by rw [map_mul, ha, mul_zero]
  have hC : ((pullback.diagonal f).app (prodOpen f U)).hom
      (diffSection f U a * diffSection f U b) = 0 := by rw [map_mul, hb, mul_zero]
  have hBC : ((pullback.diagonal f).app (prodOpen f U)).hom
      (((pullback.fst f f).appLE U (prodOpen f U) (prodOpen_le_fst f U)).hom b *
          diffSection f U a + diffSection f U a * diffSection f U b) = 0 := by
    rw [map_add, hB, hC, add_zero]
  have hABC : ((pullback.diagonal f).app (prodOpen f U)).hom
      (((pullback.fst f f).appLE U (prodOpen f U) (prodOpen_le_fst f U)).hom a *
          diffSection f U b +
        (((pullback.fst f f).appLE U (prodOpen f U) (prodOpen_le_fst f U)).hom b *
            diffSection f U a + diffSection f U a * diffSection f U b)) = 0 := by
    rw [map_add, hA, hBC, add_zero]
  refine (diagonalD_eq_conormalClass f U _ _ (diffSection_mul f U a b) hABC).trans ?_
  refine Eq.trans (conormalClass_add (pullback.diagonal f) (prodOpen f U)
    (le_diagonal_preimage_prodOpen f U) _ _ hA hBC hABC) ?_
  refine Eq.trans (congrArg (fun y => conormalClass (pullback.diagonal f) (prodOpen f U)
      (le_diagonal_preimage_prodOpen f U) _ hA + y)
    (conormalClass_add (pullback.diagonal f) (prodOpen f U)
      (le_diagonal_preimage_prodOpen f U) _ _ hB hC hBC)) ?_
  rw [conormalClass_mul_of_both (pullback.diagonal f) (prodOpen f U)
    (le_diagonal_preimage_prodOpen f U) (diffSection f U a) (diffSection f U b) ha hb hC,
    add_zero,
    conormalClass_mul_left (pullback.diagonal f) (prodOpen f U)
      (le_diagonal_preimage_prodOpen f U) _ (diffSection f U b) hb hA,
    conormalClass_mul_left (pullback.diagonal f) (prodOpen f U)
      (le_diagonal_preimage_prodOpen f U) _ (diffSection f U a) ha hB]
  refine congrArg₂ (fun c c' =>
      (show (structureSheafRing X.toRingedSpace).obj.obj (op U) from c) • diagonalD f U b +
        (show (structureSheafRing X.toRingedSpace).obj.obj (op U) from c') • diagonalD f U a)
    (appLE_diagonal_fst_appLE f U a) (appLE_diagonal_fst_appLE f U b)

/-- The derivation `d = s₂ - s₁` is compatible with restriction. -/
theorem diagonalD_restrict {U U' : X.Opens} (hU : U' ≤ U) (b : Γ(X, U)) :
    (conormalSheaf (pullback.diagonal f)).val.map (homOfLE hU).op (diagonalD f U b) =
      diagonalD f U' ((X.presheaf.map (homOfLE hU).op).hom b) := by
  have h := app_diffSection f U' ((X.presheaf.map (homOfLE hU).op).hom b)
  rw [← diffSection_restrict f hU b] at h
  refine (conormalClass_restrict (pullback.diagonal f) (prodOpen f U)
    (prodOpen f U') (prodOpen_mono f hU) (le_diagonal_preimage_prodOpen f U)
    (le_diagonal_preimage_prodOpen f U') hU (diffSection f U b) (app_diffSection f U b)
    h).trans ?_
  exact (diagonalD_eq_conormalClass f U' _ _ (diffSection_restrict f hU b).symm h).symm

/-- The derivation `d = s₂ - s₁` kills the functions pulled back from the base. -/
theorem diagonalD_app_eq_zero (W : S.Opens) (b : Γ(S, W)) :
    diagonalD f (f ⁻¹ᵁ W) ((f.app W).hom b) = 0 :=
  diagonalD_of_eq_zero f (f ⁻¹ᵁ W) ((f.app W).hom b) (diffSection_app_eq_zero f W b)

/-! ### The sheaf of differentials maps to the conormal sheaf of the diagonal -/

/-- The derivation `d = s₂ - s₁` of [Stacks, Tag 08S2] as a derivation of `𝒪_X` over the
constant sheaf `ℤ`, with values in the conormal sheaf of the diagonal. -/
def conormalDerivationData :
    (conormalSheaf (pullback.diagonal f)).val.Derivation'
      (SheafOfModules.constIntMap X.presheaf) where
  d {W} := AddMonoidHom.mk' (fun b => diagonalD f W.unop b) (diagonalD_add f W.unop)
  d_mul {W} a b := diagonalD_mul f W.unop a b
  d_map idx x := (diagonalD_restrict f idx.unop.le x).symm
  d_app {W} a := SheafOfModules.constIntMap_app_eq_zero _ (diagonalD_one f W.unop) a

/-- The relative derivation `d = s₂ - s₁` of [Stacks, Tag 08S2]: an `S`-derivation of `𝒪_X`
with values in the conormal sheaf of the diagonal, sending a local section `b` of `𝒪_X` to the
conormal class of `p₂^♯ b - p₁^♯ b`. -/
def conormalDerivation : SheafOfModules.SheafDerivation (inverseImageStructureMap f)
    (conormalSheaf (pullback.diagonal f)) :=
  SheafOfModules.ofComorphism f (conormalDerivationData f) (diagonalD_app_eq_zero f)

/-- The derivation `d = s₂ - s₁`, read on sections. -/
theorem conormalDerivation_d (U : X.Opens) (b : Γ(X, U)) :
    (conormalDerivation f).d (X := op U) b = diagonalD f U b := rfl

/-- The `𝒪_X`-linear map `Ω_{X/S} ⟶ 𝒞_{X/X ×_S X}` of [Stacks, Tag 08S2] induced by the
derivation `d = s₂ - s₁` through the universal property of the sheaf of relative differentials. -/
def differentialsToConormal :
    f.relativeDifferentials ⟶ conormalSheaf (pullback.diagonal f) :=
  (SheafOfModules.universalDerivation_isUniversal (inverseImageStructureMap f)).desc
    (conormalDerivation f)

/-- The canonical map `Stacks.Diagonal.differentialsToConormal` carries the universal differential
`d b` of a local section `b` of `𝒪_X` to the conormal class of `p₂^♯ b - p₁^♯ b`. -/
theorem differentialsToConormal_d (U : X.Opens) (b : Γ(X, U)) :
    ((differentialsToConormal f).val.app (op U)).hom (f.universalRelativeDerivation.d b) =
      diagonalD f U b :=
  PresheafOfModules.Derivation.congr_d
    ((SheafOfModules.universalDerivation_isUniversal
      (inverseImageStructureMap f)).postcomp_desc (conormalDerivation f)) b

/-- `Stacks.Diagonal.differentialsToConormal` is the only morphism of
`𝒪_X`-modules `Ω_{X/S} ⟶ 𝒞_{X/X ×_S X}` carrying `d b` to the conormal class of
`p₂^♯ b - p₁^♯ b`. -/
theorem eq_differentialsToConormal
    (g : f.relativeDifferentials ⟶ conormalSheaf (pullback.diagonal f))
    (hg : ∀ (U : X.Opens) (b : Γ(X, U)),
      (g.val.app (op U)).hom (f.universalRelativeDerivation.d b) = diagonalD f U b) :
    g = differentialsToConormal f := by
  refine (SheafOfModules.universalDerivation_isUniversal
    (inverseImageStructureMap f)).desc_eq g ?_
  ext W x
  exact hg W.unop x

end Stacks.Diagonal

end
