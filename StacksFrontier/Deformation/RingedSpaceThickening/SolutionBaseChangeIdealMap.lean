module

public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionClasses
public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalSheaf

/-!
# The map of base ideals along a morphism of thickenings of the base

Let `t₁ : (S, 𝒪_S) ⟶ (S'₁, 𝒪_{S'₁})` and `t₂ : (S, 𝒪_S) ⟶ (S'₂, 𝒪_{S'₂})` be morphisms of ringed
spaces with ideals `𝒥₁ = Ker(t₁^♯)` and `𝒥₂ = Ker(t₂^♯)`, and let `h' : S'₂ ⟶ S'₁` satisfy
`t₂ ≫ h' = t₁`. The comorphism `h'^♯` carries `𝒥₁` into `𝒥₂`, and so induces a map
`t₁^*𝒥₁ ⟶ t₂^*𝒥₂` on `S` and, for `f : X ⟶ S`, its pullback `f^*t₁^*𝒥₁ ⟶ f^*t₂^*𝒥₂`. This is the
comparison of the two prescribed maps `c₁`, `c₂` of the deformation problems of **Stacks 08U7**
over `t₁` and over `t₂`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.baseIdealSheafMap`: the map `h'^*𝒥₁ ⟶ 𝒥₂` on `S'₂`,
  the canonical ideal map of the square `t₂ ≫ h' = 𝟙 ≫ t₁`.
* `AlgebraicGeometry.RingedSpaceThickening.baseChangeIdealMapOnBase`: the map `t₁^*𝒥₁ ⟶ t₂^*𝒥₂`.
* `AlgebraicGeometry.RingedSpaceThickening.baseChangeIdealMap`: its pullback along `f`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.homEquiv_baseIdealSheafMap_comp`: the transpose
  `𝒥₁ ⟶ h'_*𝒥₂` of `baseIdealSheafMap`, followed by `h'_*` of the inclusion of `𝒥₂`, is the
  inclusion of `𝒥₁` followed by `h'^♯`.
* `AlgebraicGeometry.RingedSpaceThickening.prescribedIdealSection_baseChangeIdealMap_comp`: the
  value of `baseChangeIdealMap ≫ c₂` at a section `a` of `𝒥₁` is the value of `c₂` at `h'^♯ a`.

## References

* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
* [Stacks Project, Tag 08UA](https://stacks.math.columbia.edu/tag/08UA)
* [Stacks Project, Tag 08KZ](https://stacks.math.columbia.edu/tag/08KZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

/-- **Transposing across a composite pullback.** For `a : X ⟶ Y` and `b : Y ⟶ Z`, precomposing
with the comparison `(a ≫ b)^* ≅ a^* b^*` and transposing along `(a ≫ b)^* ⊣ (a ≫ b)_*` is
transposing along `a^* ⊣ a_*` and then along `b^* ⊣ b_*`. -/
theorem homEquiv_modulePullbackCompUniq_hom_comp {X Y Z : RingedSpace.{u, u}} (a : X ⟶ Y)
    (b : Y ⟶ Z) (M : SheafOfModules.{u} (structureSheafRing Z))
    {N : SheafOfModules.{u} (structureSheafRing X)}
    (z : (modulePullback a).obj ((modulePullback b).obj M) ⟶ N) :
    (modulePullbackPushforwardAdjunction (a ≫ b)).homEquiv _ _
        ((modulePullbackCompUniq a b).hom.app M ≫ z) =
      (modulePullbackPushforwardAdjunction b).homEquiv _ _
        ((modulePullbackPushforwardAdjunction a).homEquiv _ _ z) := by
  let adjseq := ((modulePullbackPushforwardAdjunction b).comp
    (modulePullbackPushforwardAdjunction a)).ofNatIsoRight (modulePushforwardCompSymm a b).symm
  have h := homEquiv_leftAdjointUniq_inv_app_comp
    (modulePullbackPushforwardAdjunction (a ≫ b)) adjseq M
    ((modulePullbackCompUniq a b).hom.app M ≫ z)
  have e : (Adjunction.leftAdjointUniq (modulePullbackPushforwardAdjunction (a ≫ b))
      adjseq).inv.app M ≫ (modulePullbackCompUniq a b).hom.app M ≫ z = z :=
    Iso.inv_hom_id_app_assoc (modulePullbackCompUniq a b) M z
  rw [e] at h
  rw [← h, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  rfl

/-! ### The prescribed value on sections -/

section Prescribed

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} {f : X ⟶ S}
  {G : SheafOfModules.{u} (structureSheafRing X)}

/-- The section of the base ideal defined by `s` is any section whose inclusion is `s`. -/
private theorem baseIdealSection_eq_of_idealSheafι_eq (V : (Opens S'.carrier)ᵒᵖ)
    {s : S'.presheaf.obj V} (hs : (t.hom.c.app V).hom s = 0)
    {y : (AlgebraicGeometry.SheafOfModules.idealSheaf t).val.obj V}
    (h : (Stacks.ClosedImmersion.idealSheafι t).val.app V y = s) :
    baseIdealSection t V s hs = y :=
  Stacks.ClosedImmersion.injective_idealSheafι_val_app t V.unop
    ((idealSheafι_baseIdealSection t V s hs).trans h.symm)

/-- The section of the base ideal defined by `s` depends only on `s`. -/
theorem baseIdealSection_congr (V : (Opens S'.carrier)ᵒᵖ) {s s' : S'.presheaf.obj V}
    (e : s = s') (hs : (t.hom.c.app V).hom s = 0) (hs' : (t.hom.c.app V).hom s' = 0) :
    baseIdealSection t V s hs = baseIdealSection t V s' hs' := by
  subst e
  rfl

/-- The section of the base ideal defined by `0` is `0`. -/
theorem baseIdealSection_zero (V : (Opens S'.carrier)ᵒᵖ) (h0 : (t.hom.c.app V).hom 0 = 0) :
    baseIdealSection t V 0 h0 = 0 :=
  baseIdealSection_eq_of_idealSheafι_eq V h0 (map_zero _)

/-- The section of the base ideal defined by `s + s'` is the sum of those for `s` and `s'`. -/
theorem baseIdealSection_add (V : (Opens S'.carrier)ᵒᵖ) (s s' : S'.presheaf.obj V)
    (hs : (t.hom.c.app V).hom s = 0) (hs' : (t.hom.c.app V).hom s' = 0)
    (h : (t.hom.c.app V).hom (s + s') = 0) :
    baseIdealSection t V (s + s') h = baseIdealSection t V s hs + baseIdealSection t V s' hs' :=
  baseIdealSection_eq_of_idealSheafι_eq V h
    ((map_add _ _ _).trans (congrArg₂ (· + ·) (idealSheafι_baseIdealSection t V s hs)
      (idealSheafι_baseIdealSection t V s' hs')))

/-- The section of the base ideal defined by `r * s` is `r` acting on the one defined by `s`. -/
theorem baseIdealSection_mul (V : (Opens S'.carrier)ᵒᵖ) (r s : S'.presheaf.obj V)
    (hs : (t.hom.c.app V).hom s = 0) (h : (t.hom.c.app V).hom (r * s) = 0) :
    baseIdealSection t V (r * s) h = r • baseIdealSection t V s hs :=
  baseIdealSection_eq_of_idealSheafι_eq V h
    ((((Stacks.ClosedImmersion.idealSheafι t).val.app V).hom.map_smul r _).trans
      (congrArg (r * ·) (idealSheafι_baseIdealSection t V s hs)))

/-- The section of the base ideal defined by `s` commutes with restriction. -/
theorem baseIdealSection_map {V W : (Opens S'.carrier)ᵒᵖ} (i : V ⟶ W) (s : S'.presheaf.obj V)
    (hs : (t.hom.c.app V).hom s = 0) (h : (t.hom.c.app W).hom ((S'.presheaf.map i).hom s) = 0) :
    baseIdealSection t W ((S'.presheaf.map i).hom s) h =
      (AlgebraicGeometry.SheafOfModules.idealSheaf t).val.map i (baseIdealSection t V s hs) :=
  baseIdealSection_eq_of_idealSheafι_eq W h
    ((PresheafOfModules.naturality_apply (Stacks.ClosedImmersion.idealSheafι t).val i _).trans
      (congrArg (S'.presheaf.map i).hom (idealSheafι_baseIdealSection t V s hs)))

variable (c : (modulePullback f).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G)

/-- The prescribed value at `s` depends only on `s`. -/
theorem prescribedIdealSection_congr (V : (Opens S'.carrier)ᵒᵖ) {s s' : S'.presheaf.obj V}
    (e : s = s') (hs : (t.hom.c.app V).hom s = 0) (hs' : (t.hom.c.app V).hom s' = 0) :
    prescribedIdealSection c V s hs = prescribedIdealSection c V s' hs' := by
  subst e
  rfl

/-- The prescribed value depends only on the prescribed map `c`. -/
theorem prescribedIdealSection_congr' {c' : (modulePullback f).obj
      ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G} (e : c = c')
    (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V) (hs : (t.hom.c.app V).hom s = 0) :
    prescribedIdealSection c V s hs = prescribedIdealSection c' V s hs := by
  subst e
  rfl

/-- The prescribed value at `0` is `0`. -/
theorem prescribedIdealSection_zero (V : (Opens S'.carrier)ᵒᵖ)
    (h0 : (t.hom.c.app V).hom 0 = 0) : prescribedIdealSection c V 0 h0 = 0 := by
  unfold prescribedIdealSection
  rw [baseIdealSection_zero]
  exact map_zero _

/-- The prescribed value at `s + s'` is the sum of the prescribed values at `s` and `s'`. -/
theorem prescribedIdealSection_add (V : (Opens S'.carrier)ᵒᵖ) (s s' : S'.presheaf.obj V)
    (hs : (t.hom.c.app V).hom s = 0) (hs' : (t.hom.c.app V).hom s' = 0)
    (h : (t.hom.c.app V).hom (s + s') = 0) :
    prescribedIdealSection c V (s + s') h =
      prescribedIdealSection c V s hs + prescribedIdealSection c V s' hs' := by
  unfold prescribedIdealSection
  rw [baseIdealSection_add V s s' hs hs' h]
  exact map_add _ _ _

/-- The prescribed value at `s - s'` is the difference of the values at `s` and `s'`. -/
theorem prescribedIdealSection_sub (V : (Opens S'.carrier)ᵒᵖ) (s s' : S'.presheaf.obj V)
    (hs : (t.hom.c.app V).hom s = 0) (hs' : (t.hom.c.app V).hom s' = 0)
    (h : (t.hom.c.app V).hom (s - s') = 0) :
    prescribedIdealSection c V (s - s') h =
      prescribedIdealSection c V s hs - prescribedIdealSection c V s' hs' := by
  have h' : prescribedIdealSection c V (s - s') h + prescribedIdealSection c V s' hs' =
      prescribedIdealSection c V s hs :=
    (prescribedIdealSection_add c V _ _ h hs' (by rw [sub_add_cancel]; exact hs)).symm.trans
      (prescribedIdealSection_congr c V (sub_add_cancel s s') _ _)
  exact eq_sub_of_add_eq h'

/-- **The prescribed value is linear**: at `r · s` it is the comorphism of `f ∘ t` at `r` acting
on the value at `s`. -/
theorem prescribedIdealSection_mul (V : (Opens S'.carrier)ᵒᵖ) (r s : S'.presheaf.obj V)
    (hs : (t.hom.c.app V).hom s = 0) (h : (t.hom.c.app V).hom (r * s) = 0) :
    prescribedIdealSection c V (r * s) h =
      ((f ≫ t).hom.c.app V).hom r • prescribedIdealSection c V s hs := by
  unfold prescribedIdealSection
  rw [baseIdealSection_mul V r s hs h]
  exact ((prescribedIdealMap c).val.app V).hom.map_smul r _

/-- The prescribed value commutes with restriction. -/
theorem prescribedIdealSection_map {V W : (Opens S'.carrier)ᵒᵖ} (i : V ⟶ W)
    (s : S'.presheaf.obj V) (hs : (t.hom.c.app V).hom s = 0)
    (h : (t.hom.c.app W).hom ((S'.presheaf.map i).hom s) = 0) :
    prescribedIdealSection c W ((S'.presheaf.map i).hom s) h =
      G.val.map ((Opens.map (f ≫ t).hom.base).op.map i) (prescribedIdealSection c V s hs) := by
  unfold prescribedIdealSection
  rw [baseIdealSection_map i s hs h]
  exact PresheafOfModules.naturality_apply (prescribedIdealMap c).val i _

/-- The prescribed value of `c ≫ ν` is `ν` of the prescribed value of `c`. -/
theorem prescribedIdealSection_comp {G' : SheafOfModules.{u} (structureSheafRing X)} (ν : G ⟶ G')
    (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V) (hs : (t.hom.c.app V).hom s = 0) :
    prescribedIdealSection (c ≫ ν) V s hs = ν.val.app _ (prescribedIdealSection c V s hs) := by
  unfold prescribedIdealSection prescribedIdealMap
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
  rfl

end Prescribed

variable {X S S₁ S₂ : RingedSpace.{u, u}} {t₁ : S ⟶ S₁} {t₂ : S ⟶ S₂}

/-- **The map `h'^*𝒥₁ ⟶ 𝒥₂` of base ideals** on `S'₂`: the canonical map of ideal sheaves of the
square `t₂ ≫ h' = 𝟙 ≫ t₁` (`Stacks.ClosedImmersion.idealSheafMap`), i.e. the restriction of
`h'^♯` to `𝒥₁`. -/
abbrev baseIdealSheafMap (h' : S₂ ⟶ S₁) (comm : t₂ ≫ h' = t₁) :
    (modulePullback h').obj (AlgebraicGeometry.SheafOfModules.idealSheaf t₁) ⟶
      AlgebraicGeometry.SheafOfModules.idealSheaf t₂ :=
  Stacks.ClosedImmersion.idealSheafMap (i := t₂) (k := h') (f := 𝟙 S) (j := t₁)
    (comm.trans (Category.id_comp t₁).symm)

/-- **The transpose of the map of base ideals** `𝒥₁ ⟶ h'_*𝒥₂`, followed by `h'_*` of the
inclusion of `𝒥₂`, is the inclusion of `𝒥₁` followed by `h'^♯ : 𝒪_{S'₁} ⟶ h'_*𝒪_{S'₂}`. -/
theorem homEquiv_baseIdealSheafMap_comp (h' : S₂ ⟶ S₁) (comm : t₂ ≫ h' = t₁) :
    (modulePullbackPushforwardAdjunction h').homEquiv _ _ (baseIdealSheafMap h' comm) ≫
        (modulePushforward h').map (Stacks.ClosedImmersion.idealSheafι t₂) =
      Stacks.ClosedImmersion.idealSheafι t₁ ≫ structureSheafModuleHom h' := by
  rw [← Adjunction.homEquiv_naturality_right, Stacks.ClosedImmersion.idealSheafMap_comp_ι,
    Adjunction.homEquiv_naturality_left, homEquiv_modulePullbackUnitToUnit]

/-- **The map `t₁^*𝒥₁ ⟶ t₂^*𝒥₂` of pulled back base ideals** on `S` induced by `h'` with
`t₂ ≫ h' = t₁`: the identification `t₁^* = (t₂ ≫ h')^* ≅ t₂^* h'^*` followed by `t₂^*` of the map
of base ideals `h'^*𝒥₁ ⟶ 𝒥₂`. -/
def baseChangeIdealMapOnBase (h' : S₂ ⟶ S₁) (comm : t₂ ≫ h' = t₁) :
    (modulePullback t₁).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t₁) ⟶
      (modulePullback t₂).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t₂) :=
  eqToHom (congrArg (fun k => (modulePullback k).obj
      (AlgebraicGeometry.SheafOfModules.idealSheaf t₁)) comm.symm) ≫
    (modulePullbackCompUniq t₂ h').hom.app _ ≫ (modulePullback t₂).map (baseIdealSheafMap h' comm)

/-- **The map `f^*t₁^*𝒥₁ ⟶ f^*t₂^*𝒥₂` of pulled back base ideals** along `f : X ⟶ S`, which
compares the prescribed maps of the deformation problems of Stacks 08U7 over `t₁` and `t₂`. -/
def baseChangeIdealMap (f : X ⟶ S) (h' : S₂ ⟶ S₁) (comm : t₂ ≫ h' = t₁) :
    (modulePullback f).obj ((modulePullback t₁).obj
        (AlgebraicGeometry.SheafOfModules.idealSheaf t₁)) ⟶
      (modulePullback f).obj ((modulePullback t₂).obj
        (AlgebraicGeometry.SheafOfModules.idealSheaf t₂)) :=
  (modulePullback f).map (baseChangeIdealMapOnBase h' comm)

variable {G₂ : SheafOfModules.{u} (structureSheafRing X)}

/-- **The transposed prescribed map of `baseChangeIdealMap ≫ c₂`** is the transposed map of base
ideals followed by `h'_*` of the transposed prescribed map of `c₂`. -/
theorem prescribedIdealMap_baseChangeIdealMap_comp (f : X ⟶ S) (h' : S₂ ⟶ S₁)
    (c₂ : (modulePullback f).obj ((modulePullback t₂).obj
      (AlgebraicGeometry.SheafOfModules.idealSheaf t₂)) ⟶ G₂) :
    prescribedIdealMap (t := t₂ ≫ h') (baseChangeIdealMap f h' rfl ≫ c₂) =
      (modulePullbackPushforwardAdjunction h').homEquiv _ _ (baseIdealSheafMap h' rfl) ≫
        (modulePushforward h').map (prescribedIdealMap (t := t₂) c₂) := by
  unfold prescribedIdealMap baseChangeIdealMap
  rw [homEquiv_modulePullbackCompUniq_hom_comp, Adjunction.homEquiv_naturality_left,
    baseChangeIdealMapOnBase, eqToHom_refl, Category.id_comp, Category.assoc,
    homEquiv_modulePullbackCompUniq_hom_comp, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right, homEquiv_modulePullbackCompUniq_hom_comp]
  rfl

/-- **The value of `baseChangeIdealMap ≫ c₂` at a section `a` of `𝒥₁` is the value of `c₂` at
`h'^♯ a`**, a section of `𝒥₂` over the preimage of the open of `a`. -/
theorem prescribedIdealSection_baseChangeIdealMap_comp (f : X ⟶ S) (h' : S₂ ⟶ S₁)
    (c₂ : (modulePullback f).obj ((modulePullback t₂).obj
      (AlgebraicGeometry.SheafOfModules.idealSheaf t₂)) ⟶ G₂)
    (V : (Opens S₁.carrier)ᵒᵖ) (a : S₁.presheaf.obj V)
    (ha : ((t₂ ≫ h').hom.c.app V).hom a = 0) :
    prescribedIdealSection (t := t₂ ≫ h') (baseChangeIdealMap f h' rfl ≫ c₂) V a ha =
      prescribedIdealSection (t := t₂) c₂ (op ((Opens.map h'.hom.base).obj V.unop))
        ((h'.hom.c.app V).hom a) ha := by
  have key := congrArg (fun φ => (φ.val.app V).hom (baseIdealSection (t₂ ≫ h') V a ha))
    (homEquiv_baseIdealSheafMap_comp h' (rfl : t₂ ≫ h' = t₂ ≫ h'))
  have hj : ((modulePullbackPushforwardAdjunction h').homEquiv _ _
      (baseIdealSheafMap h' rfl)).val.app V (baseIdealSection (t₂ ≫ h') V a ha) =
      baseIdealSection t₂ (op ((Opens.map h'.hom.base).obj V.unop))
        ((h'.hom.c.app V).hom a) ha :=
    (baseIdealSection_eq_of_idealSheafι_eq (t := t₂) _ ha
      (key.trans (congrArg (h'.hom.c.app V).hom
        (idealSheafι_baseIdealSection (t₂ ≫ h') V a ha)))).symm
  unfold prescribedIdealSection
  rw [prescribedIdealMap_baseChangeIdealMap_comp]
  exact congrArg ((prescribedIdealMap (t := t₂) c₂).val.app _).hom hj

end AlgebraicGeometry.RingedSpaceThickening

end
