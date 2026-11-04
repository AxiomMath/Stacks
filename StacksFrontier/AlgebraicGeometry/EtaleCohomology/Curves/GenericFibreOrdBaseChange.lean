module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericFibreOrdLocallyIntegral
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionOrder

/-!
# The order of vanishing on generic fibres across a square of bases

Let `p : X' ⟶ X` be a morphism of integral schemes, `gY : Y ⟶ X'` and `gZ : Z ⟶ X` étale, and
`h : Y ⟶ Z` a flat morphism covered by a morphism `m` of generic fibres
`Y ×_{X'} Spec K(X') ⟶ Z ×_X Spec K(X)`. For an invertible function `a` on the generic fibre of
`Z`, the order of vanishing at a point `y` of `Y` of its restriction along `m` is

* the order of vanishing of `a` at `h y`, if the stalk map of `h` at `y` carries the maximal
  ideal onto the maximal ideal and the two local rings have the same dimension;
* zero, if the local ring of `Z` at `h y` is a field.

This is the pointwise content of the compatibility of the divisor sequences of a curve and of its
extension to a bigger algebraically closed field.

## Main results

* `Stacks.EtaleCohomology.genericFibreToFunctionField_appTop_of_square`
* `Stacks.EtaleCohomology.genericFibreOrdOfPoint_appTop_of_square`
* `Stacks.EtaleCohomology.genericFibreOrdOfPoint_appTop_eq_zero_of_square`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Order IsLocalRing AlgebraicGeometry
  AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- The cross-base naturality square, with the map on function fields in its stalk-map spelling. -/
private theorem appTop_comp_genericFibreToFunctionField_square {X X' U V : Scheme.{u}}
    [IrreducibleSpace X] [IrreducibleSpace X'] [IrreducibleSpace U] [IrreducibleSpace V]
    (gU : U ⟶ X') (gV : V ⟶ X)
    [Flat gU] [Flat gV] (h : U ⟶ V)
    (m : pullback gU (genericPointInclusion X') ⟶ pullback gV (genericPointInclusion X))
    (hm : m ≫ pullback.fst gV (genericPointInclusion X) =
      pullback.fst gU (genericPointInclusion X') ≫ h)
    (hη : genericPoint V = h.base (genericPoint U)) :
    m.appTop ≫ genericFibreToFunctionField gU =
      genericFibreToFunctionField gV ≫ eqToHom (congrArg V.presheaf.stalk hη) ≫
        h.stalkMap (genericPoint U) := by
  have isoU := isIso_stalkMap_pullback_fst_genericPointInclusion X' gU (genericFibrePoint gU)
  have isoV := isIso_stalkMap_pullback_fst_genericPointInclusion X gV
    (m.base (genericFibrePoint gU))
  have hzU : (pullback.fst gU (genericPointInclusion X')).base (genericFibrePoint gU) =
      genericPoint U := fst_base_genericFibrePoint gU
  have hbase : (pullback.fst gV (genericPointInclusion X)).base
        (m.base (genericFibrePoint gU)) =
      h.base ((pullback.fst gU (genericPointInclusion X')).base (genericFibrePoint gU)) :=
    congrArg (fun φ : pullback gU (genericPointInclusion X') ⟶ V =>
      φ.base (genericFibrePoint gU)) hm
  have hwV : (pullback.fst gV (genericPointInclusion X)).base
      (m.base (genericFibrePoint gU)) = genericPoint V :=
    hbase.trans ((congrArg h.base hzU).trans hη.symm)
  have hgerm : m.appTop ≫
      (pullback gU (genericPointInclusion X')).presheaf.germ ⊤ (genericFibrePoint gU) trivial =
        (pullback gV (genericPointInclusion X)).presheaf.germ ⊤
          (m.base (genericFibrePoint gU)) trivial ≫ m.stalkMap (genericFibrePoint gU) :=
    (Scheme.Hom.germ_stalkMap m ⊤ (genericFibrePoint gU) trivial).symm
  have hsq : (pullback.fst gV (genericPointInclusion X)).stalkMap
        (m.base (genericFibrePoint gU)) ≫ m.stalkMap (genericFibrePoint gU) =
      eqToHom (congrArg V.presheaf.stalk hbase) ≫
        h.stalkMap ((pullback.fst gU (genericPointInclusion X')).base (genericFibrePoint gU)) ≫
          (pullback.fst gU (genericPointInclusion X')).stalkMap (genericFibrePoint gU) := by
    rw [← Scheme.Hom.stalkMap_comp m (pullback.fst gV (genericPointInclusion X))
        (genericFibrePoint gU),
      ← Scheme.Hom.stalkMap_comp (pullback.fst gU (genericPointInclusion X')) h
        (genericFibrePoint gU)]
    have hcongr : ∀ {A D : Scheme.{u}} {f f' : A ⟶ D} (_ : f = f') (x : A)
        (E : D.presheaf.stalk (f.base x) = D.presheaf.stalk (f'.base x)),
        f.stalkMap x = eqToHom E ≫ f'.stalkMap x := by
      intro A D f f' e x E
      subst e
      simp
    exact hcongr hm (genericFibrePoint gU) (congrArg V.presheaf.stalk hbase)
  have hinv : m.stalkMap (genericFibrePoint gU) ≫
      inv ((pullback.fst gU (genericPointInclusion X')).stalkMap (genericFibrePoint gU)) =
      inv ((pullback.fst gV (genericPointInclusion X)).stalkMap (m.base (genericFibrePoint gU))) ≫
        (eqToHom (congrArg V.presheaf.stalk hbase) ≫
          h.stalkMap
            ((pullback.fst gU (genericPointInclusion X')).base (genericFibrePoint gU))) := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp, hsq, Category.assoc]
  have htail : m.stalkMap (genericFibrePoint gU) ≫
        inv ((pullback.fst gU (genericPointInclusion X')).stalkMap (genericFibrePoint gU)) ≫
          (U.presheaf.stalkCongr (Inseparable.of_eq hzU)).hom =
      inv ((pullback.fst gV (genericPointInclusion X)).stalkMap
          (m.base (genericFibrePoint gU))) ≫
        (V.presheaf.stalkCongr (Inseparable.of_eq hwV)).hom ≫
          eqToHom (congrArg V.presheaf.stalk hη) ≫ h.stalkMap (genericPoint U) := by
    have hcc : ∀ {x : U} (_ : x = genericPoint U) {b : V} (e : b = h.base x)
        (hb : b = genericPoint V),
        eqToHom (congrArg V.presheaf.stalk e) ≫ h.stalkMap x ≫
            (U.presheaf.stalkCongr (Inseparable.of_eq ‹x = genericPoint U›)).hom =
          (V.presheaf.stalkCongr (Inseparable.of_eq hb)).hom ≫
            eqToHom (congrArg V.presheaf.stalk hη) ≫ h.stalkMap (genericPoint U) := by
      intro x hx b e hb
      subst hx
      subst hb
      simp only [Stacks.Chow.stalkCongr_eq_eqToHom, eqToHom_refl, Category.comp_id,
        Category.id_comp]
    rw [← Category.assoc, hinv, Category.assoc, Category.assoc, hcc hzU hbase hwV]
  calc m.appTop ≫ genericFibreToFunctionField gU
      = (m.appTop ≫
          (pullback gU (genericPointInclusion X')).presheaf.germ ⊤ (genericFibrePoint gU)
            trivial) ≫
          (inv ((pullback.fst gU (genericPointInclusion X')).stalkMap (genericFibrePoint gU)) ≫
            (U.presheaf.stalkCongr (Inseparable.of_eq hzU)).hom) := by
        rw [genericFibreToFunctionField_eq_germ_comp gU hzU]
        simp only [Category.assoc]
    _ = ((pullback gV (genericPointInclusion X)).presheaf.germ ⊤
            (m.base (genericFibrePoint gU)) trivial ≫
          m.stalkMap (genericFibrePoint gU)) ≫
          (inv ((pullback.fst gU (genericPointInclusion X')).stalkMap (genericFibrePoint gU)) ≫
            (U.presheaf.stalkCongr (Inseparable.of_eq hzU)).hom) := by rw [hgerm]
    _ = (pullback gV (genericPointInclusion X)).presheaf.germ ⊤
            (m.base (genericFibrePoint gU)) trivial ≫
          (m.stalkMap (genericFibrePoint gU) ≫
            inv ((pullback.fst gU (genericPointInclusion X')).stalkMap (genericFibrePoint gU)) ≫
              (U.presheaf.stalkCongr (Inseparable.of_eq hzU)).hom) := by
        simp only [Category.assoc]
    _ = genericFibreToFunctionField gV ≫ eqToHom (congrArg V.presheaf.stalk hη) ≫
          h.stalkMap (genericPoint U) := by
        rw [htail, genericFibreToFunctionField_eq_germ_comp gV hwV]
        simp only [Category.assoc]

/-- **The comparison with the function field across a square of bases.** For `gU : U ⟶ X'`,
`gV : V ⟶ X`, `h : U ⟶ V` dominant and `m` a morphism of generic fibres over `h`, a global
function on the generic fibre of `V`, restricted along `m` and read as a rational function on
`U`, is the pullback along `h` of the rational function it defines on `V`. -/
theorem genericFibreToFunctionField_appTop_of_square {X X' U V : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace X']
    [IsIntegral U] [IsIntegral V] (gU : U ⟶ X') (gV : V ⟶ X) [Flat gU] [Flat gV]
    (h : U ⟶ V) [IsDominant h]
    (m : pullback gU (genericPointInclusion X') ⟶ pullback gV (genericPointInclusion X))
    (hm : m ≫ pullback.fst gV (genericPointInclusion X) =
      pullback.fst gU (genericPointInclusion X') ≫ h)
    (a : Γ(pullback gV (genericPointInclusion X), ⊤)) :
    genericFibreToFunctionField gU (m.appTop a) =
      dominantFunctionFieldMap h (genericFibreToFunctionField gV a) := by
  have hη : h.base (genericPoint U) = genericPoint V :=
    ((tfae_isDominant_of_isIntegral h).out 1 2).mp (inferInstance : IsDominant h)
  have key := appTop_comp_genericFibreToFunctionField_square gU gV h m hm hη.symm
  have keyapp := congrArg (fun φ => CommRingCat.Hom.hom φ a) key
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at keyapp
  have hdffm : dominantFunctionFieldMap h (genericFibreToFunctionField gV a) =
      (h.stalkMap (genericPoint U)).hom
        ((eqToHom (congrArg V.presheaf.stalk hη.symm)).hom
          ((genericFibreToFunctionField gV).hom a)) := by
    show (hη ▸ h.stalkMap (genericPoint U)).hom _ = _
    rw [← Stacks.Chow.stalkMap_eqToHom_eq_cast h (genericPoint U) (genericPoint V) hη]
    rfl
  rw [hdffm]
  exact keyapp


/-- The order across a square, as the order of the pullback of a rational function on `V`. -/
private theorem genericFibreOrd_square_eq_ord_dominantFunctionFieldMap {X X' U V : Scheme.{u}}
    [IrreducibleSpace X] [IrreducibleSpace X'] [IsIntegral U] [IsIntegral V]
    [IsLocallyNoetherian U]
    (gU : U ⟶ X') (gV : V ⟶ X) [Flat gU] [Flat gV] (h : U ⟶ V) [IsDominant h]
    (m : pullback gU (genericPointInclusion X') ⟶ pullback gV (genericPointInclusion X))
    (hm : m ≫ pullback.fst gV (genericPointInclusion X) =
      pullback.fst gU (genericPointInclusion X') ≫ h)
    (y : U) (a : (Γ(pullback gV (genericPointInclusion X), ⊤))ˣ) :
    genericFibreOrd gU y (Additive.ofMul (Units.map m.appTop.hom.toMonoidHom a)) =
      Scheme.ord (dominantFunctionFieldMap h
        (genericFibreToFunctionField gV (a : Γ(pullback gV (genericPointInclusion X), ⊤)))) y := by
  rw [genericFibreOrd_apply]
  change Scheme.ord (genericFibreToFunctionField gU
    (m.appTop (a : Γ(pullback gV (genericPointInclusion X), ⊤)))) y = _
  rw [genericFibreToFunctionField_appTop_of_square gU gV h m hm]

/-! ### Integral schemes -/

section Integral

variable {X X' U V : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace X'] [IsIntegral U]
  [IsIntegral V] [IsLocallyNoetherian U] [IsLocallyNoetherian V] (gU : U ⟶ X') (gV : V ⟶ X)
  [Flat gU] [Flat gV] (h : U ⟶ V) [Flat h]
  (m : pullback gU (genericPointInclusion X') ⟶ pullback gV (genericPointInclusion X))
  (hm : m ≫ pullback.fst gV (genericPointInclusion X) =
    pullback.fst gU (genericPointInclusion X') ≫ h)

include hm in
/-- **The order of vanishing across a square, integral case**, at a point where the stalk map
of `h` carries the maximal ideal onto the maximal ideal. -/
theorem genericFibreOrd_appTop_of_square (y : U)
    (hmax : (maximalIdeal (V.presheaf.stalk (h.base y))).map (h.stalkMap y).hom =
      maximalIdeal (U.presheaf.stalk y))
    (hcoh : coheight (h.base y) = coheight y)
    (a : (Γ(pullback gV (genericPointInclusion X), ⊤))ˣ) :
    genericFibreOrd gU y (Additive.ofMul (Units.map m.appTop.hom.toMonoidHom a)) =
      genericFibreOrd gV (h.base y) (Additive.ofMul a) := by
  have : IsDominant h := ((tfae_isDominant_of_isIntegral h).out 1 2).mpr
    (base_genericPoint_eq_genericPoint_of_flat h)
  rw [genericFibreOrd_square_eq_ord_dominantFunctionFieldMap gU gV h m hm, genericFibreOrd_apply,
    Stacks.Chow.ord_dominantFunctionFieldMap_of_flat h y hmax hcoh]
  rfl

omit [IsLocallyNoetherian V] in
include hm in
/-- **The order of vanishing across a square vanishes at a point over a field point**: if the
local ring of `V` at `h y` is a field. -/
theorem genericFibreOrd_appTop_eq_zero_of_square (y : U)
    (hbot : maximalIdeal (V.presheaf.stalk (h.base y)) = ⊥)
    (a : (Γ(pullback gV (genericPointInclusion X), ⊤))ˣ) :
    genericFibreOrd gU y (Additive.ofMul (Units.map m.appTop.hom.toMonoidHom a)) = 0 := by
  have : IsDominant h := ((tfae_isDominant_of_isIntegral h).out 1 2).mpr
    (base_genericPoint_eq_genericPoint_of_flat h)
  rw [genericFibreOrd_square_eq_ord_dominantFunctionFieldMap gU gV h m hm]
  exact Stacks.Chow.ord_dominantFunctionFieldMap_eq_zero_of_maximalIdeal_eq_bot h y hbot _

end Integral

/-- **Transport of `𝔪 ↦ 𝔪` along open immersions**: if `f ≫ j = i ≫ f'` with `i`, `j` open
immersions and the stalk map of `f'` at `i z` carries the maximal ideal onto the maximal ideal,
so does the stalk map of `f` at `z`. -/
theorem map_maximalIdeal_stalkMap_of_comp_eq {A B C D : Scheme.{u}} {f : A ⟶ B} {f' : C ⟶ D}
    {i : A ⟶ C} {j : B ⟶ D} [IsOpenImmersion i] [IsOpenImmersion j] (hsq : f ≫ j = i ≫ f')
    (z : A)
    (hmax : (maximalIdeal (D.presheaf.stalk (f'.base (i.base z)))).map
        (f'.stalkMap (i.base z)).hom = maximalIdeal (C.presheaf.stalk (i.base z))) :
    (maximalIdeal (B.presheaf.stalk (f.base z))).map (f.stalkMap z).hom =
      maximalIdeal (A.presheaf.stalk z) := by
  have e1 := map_maximalIdeal_stalkMap_congr hsq z
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at e1
  have e2 : (maximalIdeal (D.presheaf.stalk ((f ≫ j).base z))).map
      (j.stalkMap (f.base z) ≫ f.stalkMap z).hom =
      (maximalIdeal (B.presheaf.stalk (f.base z))).map (f.stalkMap z).hom := by
    rw [CommRingCat.hom_comp]
    exact (Ideal.map_map (j.stalkMap (f.base z)).hom (f.stalkMap z).hom).symm.trans
      (congrArg (Ideal.map (f.stalkMap z).hom) (map_maximalIdeal_of_isIso _))
  have e3 : (maximalIdeal (D.presheaf.stalk ((i ≫ f').base z))).map
      (f'.stalkMap (i.base z) ≫ i.stalkMap z).hom = maximalIdeal (A.presheaf.stalk z) := by
    rw [CommRingCat.hom_comp]
    exact (Ideal.map_map (f'.stalkMap (i.base z)).hom (i.stalkMap z).hom).symm.trans
      ((congrArg (Ideal.map (i.stalkMap z).hom) hmax).trans (map_maximalIdeal_of_isIso _))
  exact e2.symm.trans (e1.trans e3)

/-! ### Arbitrary étale schemes over the two bases -/

section Point

variable {X X' Y Z : Scheme.{u}} [IsIntegral X] [IsNormal X] [IsIntegral X'] [IsNormal X']
  (gY : Y ⟶ X') (gZ : Z ⟶ X) [Etale gY] [Etale gZ] [IsLocallyNoetherian Y]
  [IsLocallyNoetherian Z] (h : Y ⟶ Z) [Flat h]
  (m : pullback gY (genericPointInclusion X') ⟶ pullback gZ (genericPointInclusion X))
  (hm : m ≫ pullback.fst gZ (genericPointInclusion X) =
    pullback.fst gY (genericPointInclusion X') ≫ h)

/-- The restriction of `h : Y ⟶ Z` to opens `WY ≤ h⁻¹ WZ`. -/
def opensRestrict {WY : Y.Opens} {WZ : Z.Opens} (hle : WY ≤ h ⁻¹ᵁ WZ) :
    WY.toScheme ⟶ WZ.toScheme :=
  Y.homOfLE hle ≫ (h ∣_ WZ)

omit [IsLocallyNoetherian Y] [IsLocallyNoetherian Z] [Flat h] in
/-- The restriction `opensRestrict h hle` followed by the inclusion of `WZ` is the inclusion
of `WY` followed by `h`. -/
theorem opensRestrict_ι {WY : Y.Opens} {WZ : Z.Opens} (hle : WY ≤ h ⁻¹ᵁ WZ) :
    opensRestrict h hle ≫ WZ.ι = WY.ι ≫ h := by
  rw [opensRestrict, Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]

/-- The image of a point under `opensRestrict h hle`, viewed in `Z`, is the image of the point
under `h`. -/
private theorem ι_base_opensRestrict_base {Y Z : Scheme.{u}} (h : Y ⟶ Z) {WY : Y.Opens}
    {WZ : Z.Opens} (hle : WY ≤ h ⁻¹ᵁ WZ) (y : WY) :
    WZ.ι.base ((opensRestrict h hle).base y) = h.base (WY.ι.base y) :=
  congrArg (fun φ : WY.toScheme ⟶ Z => φ.base y) (opensRestrict_ι h hle)

include hm in
/-- **The morphism of generic fibres restricted to opens** `WY ≤ h⁻¹ WZ`. -/
def genericFibreSquareOpensMap {WY : Y.Opens} {WZ : Z.Opens} (hle : WY ≤ h ⁻¹ᵁ WZ) :
    pullback (WY.ι ≫ gY) (genericPointInclusion X') ⟶
      pullback (WZ.ι ≫ gZ) (genericPointInclusion X) :=
  pullback.lift (pullback.fst _ _ ≫ opensRestrict h hle)
    (genericFibreOpensMap gY WY ≫ m ≫ pullback.snd _ _) (by
      have h1 := opensRestrict_ι h hle
      simp only [Category.assoc]
      rw [← pullback.condition, reassoc_of% hm, reassoc_of% h1, genericFibreOpensMap,
        reassoc_of% (genericFibreMap_comp_fst (gV := gY) WY.ι rfl)])

omit [IsNormal X] [IsNormal X'] [Etale gY] [Etale gZ] [IsLocallyNoetherian Y]
  [IsLocallyNoetherian Z] [Flat h] in
/-- The first projection of `genericFibreSquareOpensMap` is the first projection followed by
`opensRestrict h hle`. -/
theorem genericFibreSquareOpensMap_fst {WY : Y.Opens} {WZ : Z.Opens} (hle : WY ≤ h ⁻¹ᵁ WZ) :
    genericFibreSquareOpensMap gY gZ h m hm hle ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ opensRestrict h hle :=
  pullback.lift_fst _ _ _

omit [IsNormal X] [IsNormal X'] [Etale gY] [Etale gZ] [IsLocallyNoetherian Y]
  [IsLocallyNoetherian Z] [Flat h] in
/-- `genericFibreSquareOpensMap` followed by the generic fibre map of `WZ` equals the generic
fibre map of `WY` followed by `m`. -/
theorem genericFibreSquareOpensMap_comp {WY : Y.Opens} {WZ : Z.Opens} (hle : WY ≤ h ⁻¹ᵁ WZ) :
    genericFibreSquareOpensMap gY gZ h m hm hle ≫ genericFibreOpensMap gZ WZ =
      genericFibreOpensMap gY WY ≫ m := by
  refine pullback.hom_ext ?_ ?_
  · have h1 := opensRestrict_ι h hle
    rw [Category.assoc, genericFibreOpensMap, genericFibreMap_comp_fst,
      reassoc_of% (genericFibreSquareOpensMap_fst gY gZ h m hm hle), h1, Category.assoc, hm,
      genericFibreOpensMap, reassoc_of% (genericFibreMap_comp_fst (gV := gY) WY.ι rfl)]
  · rw [Category.assoc, genericFibreOpensMap, genericFibreMap_comp_snd, genericFibreSquareOpensMap,
      pullback.lift_snd]
    exact (Category.assoc _ _ _).symm

/-- The restriction `opensRestrict h hle` of a flat morphism `h` is flat. -/
instance flat_opensRestrict {WY : Y.Opens} {WZ : Z.Opens} (hle : WY ≤ h ⁻¹ᵁ WZ) :
    Flat (opensRestrict h hle) := by
  unfold opensRestrict
  infer_instance

omit [IsLocallyNoetherian Y] [IsLocallyNoetherian Z] [Flat h] in
include gY gZ in
/-- Integral opens around a point and its image, the first mapping into the second. -/
theorem exists_isIntegral_opens_square (y : Y) :
    ∃ (WY : Y.Opens) (WZ : Z.Opens), y ∈ WY ∧ h.base y ∈ WZ ∧ WY ≤ h ⁻¹ᵁ WZ ∧
      IsIntegral WY.toScheme ∧ IsIntegral WZ.toScheme := by
  obtain ⟨WZ, hWZ, hWZi⟩ := exists_isIntegral_opens_of_etale gZ (h.base y)
  obtain ⟨W₀, hW₀, hW₀i⟩ := exists_isIntegral_opens_of_etale gY y
  have hmem : y ∈ (W₀ ⊓ h ⁻¹ᵁ WZ : Y.Opens) := ⟨hW₀, hWZ⟩
  have : Nonempty (W₀ ⊓ h ⁻¹ᵁ WZ : Y.Opens).toScheme := ⟨⟨y, hmem⟩⟩
  exact ⟨_, WZ, hmem, hWZ, inf_le_right, isIntegral_inf_opens _, hWZi⟩

omit [IsNormal X] [Etale gZ] [IsLocallyNoetherian Z] [Flat h] in
include hm in
/-- The order across the square at `y`, computed in integral opens `WY ≤ h⁻¹ WZ`. -/
theorem genericFibreOrdOfPoint_square_eq {WY : Y.Opens} {WZ : Z.Opens} [IsIntegral WY.toScheme]
    [IsIntegral WZ.toScheme] (y : Y) (hyWY : y ∈ WY) (hle : WY ≤ h ⁻¹ᵁ WZ)
    (a : (Γ(pullback gZ (genericPointInclusion X), ⊤))ˣ) :
    genericFibreOrdOfPoint gY y (Additive.ofMul (Units.map m.appTop.hom.toMonoidHom a)) =
      genericFibreOrd (WY.ι ≫ gY) ⟨y, hyWY⟩ (Additive.ofMul
        (Units.map (genericFibreSquareOpensMap gY gZ h m hm hle).appTop.hom.toMonoidHom
          (Units.map (genericFibreOpensMap gZ WZ).appTop.hom.toMonoidHom a))) := by
  rw [genericFibreOrdOfPoint_eq_genericFibreOrdOfOpen gY (W := WY) ⟨y, hyWY⟩,
    genericFibreOrdOfOpen_apply_ofMul]
  congr 2
  refine Units.ext ?_
  show (genericFibreOpensMap gY WY ≫ m).appTop (a : Γ(pullback gZ (genericPointInclusion X), ⊤)) =
    (genericFibreSquareOpensMap gY gZ h m hm hle ≫ genericFibreOpensMap gZ WZ).appTop _
  rw [genericFibreSquareOpensMap_comp]

include hm in
/-- **The order of vanishing across a square of étale schemes**, at a point `y` where the stalk
map of `h` carries the maximal ideal onto the maximal ideal and codimension is preserved. -/
theorem genericFibreOrdOfPoint_appTop_of_square (y : Y)
    (hmax : (maximalIdeal (Z.presheaf.stalk (h.base y))).map (h.stalkMap y).hom =
      maximalIdeal (Y.presheaf.stalk y))
    (hcoh : coheight (h.base y) = coheight y)
    (a : (Γ(pullback gZ (genericPointInclusion X), ⊤))ˣ) :
    genericFibreOrdOfPoint gY y (Additive.ofMul (Units.map m.appTop.hom.toMonoidHom a)) =
      genericFibreOrdOfPoint gZ (h.base y) (Additive.ofMul a) := by
  obtain ⟨WY, WZ, hyWY, hWZ, hle, hWY, hWZi⟩ := exists_isIntegral_opens_square gY gZ h y
  have h1 := opensRestrict_ι h hle
  have hbase : (opensRestrict h hle).base ⟨y, hyWY⟩ = ⟨h.base y, hWZ⟩ :=
    Subtype.ext (ι_base_opensRestrict_base h hle ⟨y, hyWY⟩)
  rw [genericFibreOrdOfPoint_square_eq gY gZ h m hm y hyWY hle a,
    genericFibreOrdOfPoint_eq_genericFibreOrdOfOpen gZ (W := WZ) ⟨h.base y, hWZ⟩,
    genericFibreOrdOfOpen_apply_ofMul, ← hbase]
  have hmax' := map_maximalIdeal_stalkMap_of_comp_eq h1 ⟨y, hyWY⟩ hmax
  have hcoh' := (coheight_eq_of_etale WZ.ι ((opensRestrict h hle).base ⟨y, hyWY⟩)).symm.trans
    ((congrArg coheight (ι_base_opensRestrict_base h hle ⟨y, hyWY⟩)).trans
      (hcoh.trans (coheight_eq_of_etale WY.ι ⟨y, hyWY⟩)))
  exact genericFibreOrd_appTop_of_square (WY.ι ≫ gY) (WZ.ι ≫ gZ) (opensRestrict h hle) _
    (genericFibreSquareOpensMap_fst gY gZ h m hm hle) ⟨y, hyWY⟩ hmax' hcoh' _

omit [IsLocallyNoetherian Z] in
include hm in
/-- **The order of vanishing across a square of étale schemes vanishes** at a point `y` whose
image has a field as local ring. -/
theorem genericFibreOrdOfPoint_appTop_eq_zero_of_square (y : Y)
    (hbot : maximalIdeal (Z.presheaf.stalk (h.base y)) = ⊥)
    (a : (Γ(pullback gZ (genericPointInclusion X), ⊤))ˣ) :
    genericFibreOrdOfPoint gY y (Additive.ofMul (Units.map m.appTop.hom.toMonoidHom a)) = 0 := by
  obtain ⟨WY, WZ, hyWY, hWZ, hle, hWY, hWZi⟩ := exists_isIntegral_opens_square gY gZ h y
  have h1 := opensRestrict_ι h hle
  have hbase : WZ.ι.base ((opensRestrict h hle).base ⟨y, hyWY⟩) = h.base y :=
    ι_base_opensRestrict_base h hle ⟨y, hyWY⟩
  have hbot' : maximalIdeal (WZ.toScheme.presheaf.stalk
      ((opensRestrict h hle).base ⟨y, hyWY⟩)) = ⊥ := by
    have hz : ∀ z : Z, z = h.base y → maximalIdeal (Z.presheaf.stalk z) = ⊥ := by
      rintro _ rfl
      exact hbot
    rw [← map_maximalIdeal_of_isIso (WZ.ι.stalkMap _), hz _ hbase, Ideal.map_bot]
  rw [genericFibreOrdOfPoint_square_eq gY gZ h m hm y hyWY hle a]
  exact genericFibreOrd_appTop_eq_zero_of_square (WY.ι ≫ gY) (WZ.ι ≫ gZ) (opensRestrict h hle) _
    (genericFibreSquareOpensMap_fst gY gZ h m hm hle) ⟨y, hyWY⟩ hbot' _

end Point

end Stacks.EtaleCohomology

end
