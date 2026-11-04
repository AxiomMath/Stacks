module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafPushforwardNormal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericFibreFunctionFieldNaturality

/-!
# The order of vanishing on an étale scheme that is only locally integral

Let `X` be an integral normal scheme with generic point `η` and function field `K`, and let
`g : Y ⟶ X` be étale with `Y` locally Noetherian. `Y` need not be irreducible, so it has no
function field and `Stacks.EtaleCohomology.genericFibreOrd` does not apply to it. Every point of
`Y` has an integral open neighbourhood, and this file defines the order of vanishing at a point of
`Y` of an invertible global function on the generic fibre of `Y`, computed in any integral open
neighbourhood of the point, the answer being independent of the neighbourhood.

## Main definitions

* `Stacks.EtaleCohomology.genericFibreOpensMap`: the generic fibre of an open subscheme of `Y`,
  as a scheme over the generic fibre of `Y`.
* `Stacks.EtaleCohomology.genericFibreOrdOfOpen`: the order of vanishing at a point of an
  integral open subscheme of `Y`, computed there.
* `Stacks.EtaleCohomology.genericFibreOrdOfPoint`: the order of vanishing at an arbitrary point
  of `Y`, computed in some integral open neighbourhood.

## Main results

* `Stacks.EtaleCohomology.exists_isIntegral_opens_of_etale`: every point of a scheme étale over
  an integral normal scheme has an integral open neighbourhood.
* `Stacks.EtaleCohomology.genericFibreOrdOfPoint_eq_genericFibreOrdOfOpen`: the order of
  vanishing does not depend on the integral open neighbourhood it is computed in.
* `Stacks.EtaleCohomology.genericFibreOrdOfPoint_restrict_eq_zero`: an invertible global function
  on `Y` has order of vanishing zero at every point.
* `Stacks.EtaleCohomology.finite_support_genericFibreOrdOfPoint`: the order of vanishing is
  nonzero at only finitely many points of a Noetherian `Y`.
* `Stacks.EtaleCohomology.genericFibreOrdOfPoint_appTop`: the order of vanishing is compatible
  with restriction along an étale morphism of `X`-schemes.

## References

* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI): the fundamental exact
  sequence.
* [Stacks Project, Tag 09Z5](https://stacks.math.columbia.edu/tag/09Z5): the disjoint-union
  description of a scheme étale over an integral normal scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### Integral open neighbourhoods -/

/-- **Every point of a scheme étale over an integral normal scheme has an integral open
neighbourhood.** -/
theorem exists_isIntegral_opens_of_etale {X Y : Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
    [IsNormal X] (g : Y ⟶ X) [Etale g] (y : Y) :
    ∃ W : Y.Opens, y ∈ W ∧ AlgebraicGeometry.IsIntegral W.toScheme := by
  obtain ⟨Z, p, hp, hZ, hy⟩ := exists_isIntegral_open_of_etale g y
  have : IsOpenImmersion p := hp
  have : AlgebraicGeometry.IsIntegral Z := hZ
  exact ⟨p.opensRange, hy, AlgebraicGeometry.IsIntegral.of_isIso
    (IsOpenImmersion.isoOfRangeEq p p.opensRange.ι (by simp)).hom⟩

/-- **A nonempty open subscheme of an integral open subscheme is integral.** -/
theorem isIntegral_inf_opens {Y : Scheme.{u}} {W : Y.Opens} (W' : Y.Opens)
    [AlgebraicGeometry.IsIntegral W.toScheme] [Nonempty (W ⊓ W' : Y.Opens).toScheme] :
    AlgebraicGeometry.IsIntegral (W ⊓ W' : Y.Opens).toScheme :=
  AlgebraicGeometry.isIntegral_of_isOpenImmersion (Y.homOfLE (inf_le_left (a := W) (b := W')))

/-- The morphism of generic fibres induced by a morphism of `X`-schemes is the identity on the
second projection. -/
@[simp]
theorem genericFibreMap_comp_snd {X U V : Scheme.{u}} [IrreducibleSpace X] {gU : U ⟶ X}
    {gV : V ⟶ X} (h : U ⟶ V) (hcomm : h ≫ gV = gU) :
    genericFibreMap h hcomm ≫ pullback.snd gV (genericPointInclusion X) =
      pullback.snd gU (genericPointInclusion X) := by
  simp [genericFibreMap]

/-! ### The order of vanishing computed in an integral open -/

section Opens

variable {X Y : Scheme.{u}} [AlgebraicGeometry.IsIntegral X] (g : Y ⟶ X)

/-- **The generic fibre of an open subscheme of `Y`, over the generic fibre of `Y`.** This is
`Stacks.EtaleCohomology.genericFibreMap` at the inclusion of the open. -/
def genericFibreOpensMap (W : Y.Opens) :
    pullback (W.ι ≫ g) (genericPointInclusion X) ⟶ pullback g (genericPointInclusion X) :=
  genericFibreMap W.ι rfl

/-- The generic fibre of a nested open maps to the generic fibre of the larger one over the
generic fibre of `Y`. -/
theorem genericFibreMap_homOfLE_comp {W W' : Y.Opens} (hle : W ≤ W')
    (hcomm : Y.homOfLE hle ≫ (W'.ι ≫ g) = W.ι ≫ g) :
    genericFibreMap (Y.homOfLE hle) hcomm ≫ genericFibreOpensMap g W' =
      genericFibreOpensMap g W := by
  refine pullback.hom_ext ?_ ?_
  · simp only [genericFibreOpensMap, Category.assoc, genericFibreMap_comp_fst]
    rw [← Category.assoc, genericFibreMap_comp_fst, Category.assoc, Scheme.homOfLE_ι]
  · simp [genericFibreOpensMap, genericFibreMap]

/-- The intersection of an integral open with another open containing a common point is
integral. -/
private theorem isIntegral_inf_opens_of_mem {Y : Scheme.{u}} {W W' : Y.Opens} {y : Y}
    [AlgebraicGeometry.IsIntegral W.toScheme] (hW : y ∈ W) (hW' : y ∈ W') :
    AlgebraicGeometry.IsIntegral (W ⊓ W' : Y.Opens).toScheme :=
  have : Nonempty (W ⊓ W' : Y.Opens).toScheme := ⟨⟨y, hW, hW'⟩⟩
  isIntegral_inf_opens W'

/-- Restricting an invertible global function to the global sections of the source of a
composite morphism is the composite of the restrictions. -/
private theorem units_map_appTop_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (u : (Γ(C, ⊤))ˣ) :
    Units.map f.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom u) =
      Units.map (f ≫ g).appTop.hom.toMonoidHom u :=
  rfl

/-- Restricting an invertible global function on the generic fibre of `Y` to the generic fibre of
an open is the same as restricting it to the generic fibre of a larger open first. -/
private theorem units_map_appTop_genericFibreOpensMap {W W' : Y.Opens} (hle : W ≤ W')
    (hcomm : Y.homOfLE hle ≫ (W'.ι ≫ g) = W.ι ≫ g)
    (u : (Γ(pullback g (genericPointInclusion X), ⊤))ˣ) :
    Units.map (genericFibreMap (Y.homOfLE hle) hcomm).appTop.hom.toMonoidHom
        (Units.map (genericFibreOpensMap g W').appTop.hom.toMonoidHom u) =
      Units.map (genericFibreOpensMap g W).appTop.hom.toMonoidHom u := by
  rw [units_map_appTop_comp, genericFibreMap_homOfLE_comp]

variable [Etale g] [IsLocallyNoetherian Y]

/-- **The order of vanishing at a point of an integral open subscheme of `Y`**, of an invertible
global function on the generic fibre of `Y`: the function is restricted to the generic fibre of
the open and its order of vanishing taken there. -/
def genericFibreOrdOfOpen (W : Y.Opens) [AlgebraicGeometry.IsIntegral W.toScheme] (y : W) :
    Additive ((Γ(pullback g (genericPointInclusion X), ⊤))ˣ) →+ ℤ :=
  (genericFibreOrd (W.ι ≫ g) y).comp
    (MonoidHom.toAdditive (Units.map (genericFibreOpensMap g W).appTop.hom.toMonoidHom))

/-- The value of `Stacks.EtaleCohomology.genericFibreOrdOfOpen` on `a` is the order of vanishing
at `y` of the restriction of `a` to the generic fibre of `W`. -/
theorem genericFibreOrdOfOpen_apply (W : Y.Opens) [AlgebraicGeometry.IsIntegral W.toScheme]
    (y : W) (a : Additive ((Γ(pullback g (genericPointInclusion X), ⊤))ˣ)) :
    genericFibreOrdOfOpen g W y a =
      genericFibreOrd (W.ι ≫ g) y (Additive.ofMul
        (Units.map (genericFibreOpensMap g W).appTop.hom.toMonoidHom (Additive.toMul a))) :=
  rfl

/-- The value of `Stacks.EtaleCohomology.genericFibreOrdOfOpen` on `Additive.ofMul u` is the
order of vanishing at `y` of the restriction of `u` to the generic fibre of `W`. -/
theorem genericFibreOrdOfOpen_apply_ofMul (W : Y.Opens)
    [AlgebraicGeometry.IsIntegral W.toScheme] (y : W)
    (u : (Γ(pullback g (genericPointInclusion X), ⊤))ˣ) :
    genericFibreOrdOfOpen g W y (Additive.ofMul u) =
      genericFibreOrd (W.ι ≫ g) y (Additive.ofMul
        (Units.map (genericFibreOpensMap g W).appTop.hom.toMonoidHom u)) :=
  rfl

/-- **The order of vanishing computed in an integral open is unchanged on passing to a smaller
integral open.** -/
theorem genericFibreOrdOfOpen_homOfLE {W W' : Y.Opens}
    [AlgebraicGeometry.IsIntegral W.toScheme] [AlgebraicGeometry.IsIntegral W'.toScheme]
    (hle : W ≤ W') (y : W)
    (a : Additive ((Γ(pullback g (genericPointInclusion X), ⊤))ˣ)) :
    genericFibreOrdOfOpen g W y a = genericFibreOrdOfOpen g W' ⟨y.1, hle y.2⟩ a := by
  have hcomm : Y.homOfLE hle ≫ (W'.ι ≫ g) = W.ι ≫ g := by
    rw [← Category.assoc, Scheme.homOfLE_ι]
  have hbase : (Y.homOfLE hle).base y = ⟨y.1, hle y.2⟩ := by
    apply Subtype.ext
    simp
  rw [genericFibreOrdOfOpen_apply, genericFibreOrdOfOpen_apply, ← hbase,
    ← units_map_appTop_genericFibreOpensMap g hle hcomm (Additive.toMul a)]
  exact genericFibreOrd_appTop (W.ι ≫ g) (W'.ι ≫ g) (Y.homOfLE hle)
    (genericFibreMap (Y.homOfLE hle) hcomm)
    (genericFibreMap_comp_fst (Y.homOfLE hle) hcomm) y _

end Opens

/-! ### The order of vanishing at an arbitrary point -/

section Point

variable {X Y : Scheme.{u}} [AlgebraicGeometry.IsIntegral X] [IsNormal X] (g : Y ⟶ X) [Etale g]
  [IsLocallyNoetherian Y]

/-- **The order of vanishing at an arbitrary point of `Y` of an invertible global function on the
generic fibre of `Y`**, for `Y` étale over an integral normal scheme, computed in an integral open
neighbourhood of the point. -/
def genericFibreOrdOfPoint (y : Y) :
    Additive ((Γ(pullback g (genericPointInclusion X), ⊤))ˣ) →+ ℤ :=
  have h := exists_isIntegral_opens_of_etale g y
  have : AlgebraicGeometry.IsIntegral h.choose.toScheme := h.choose_spec.2
  genericFibreOrdOfOpen g h.choose ⟨y, h.choose_spec.1⟩

/-- **The order of vanishing at a point of `Y` is computed by any integral open neighbourhood of
the point.** -/
theorem genericFibreOrdOfPoint_eq_genericFibreOrdOfOpen {W : Y.Opens}
    [AlgebraicGeometry.IsIntegral W.toScheme] (y : W)
    (a : Additive ((Γ(pullback g (genericPointInclusion X), ⊤))ˣ)) :
    genericFibreOrdOfPoint g y.1 a = genericFibreOrdOfOpen g W y a := by
  have h := exists_isIntegral_opens_of_etale g y.1
  have : AlgebraicGeometry.IsIntegral h.choose.toScheme := h.choose_spec.2
  have hmem : (y : Y) ∈ (W ⊓ h.choose : Y.Opens) := ⟨y.2, h.choose_spec.1⟩
  have := isIntegral_inf_opens_of_mem (W := W) y.2 h.choose_spec.1
  rw [genericFibreOrdOfPoint,
    ← genericFibreOrdOfOpen_homOfLE g (inf_le_right (a := W) (b := h.choose)) ⟨y, hmem⟩ a,
    genericFibreOrdOfOpen_homOfLE g (inf_le_left (a := W) (b := h.choose)) ⟨y, hmem⟩ a]

/-- **An invertible global function on `Y` has order of vanishing zero at every point of `Y`.** -/
theorem genericFibreOrdOfPoint_restrict_eq_zero (y : Y) (a : (Γ(Y, ⊤))ˣ) :
    genericFibreOrdOfPoint g y (Additive.ofMul (Units.map
      (pullback.fst g (genericPointInclusion X)).appTop.hom.toMonoidHom a)) = 0 := by
  obtain ⟨W, hyW, hWi⟩ := exists_isIntegral_opens_of_etale g y
  have : AlgebraicGeometry.IsIntegral W.toScheme := hWi
  have hu : Units.map (genericFibreOpensMap g W).appTop.hom.toMonoidHom
        (Units.map (pullback.fst g (genericPointInclusion X)).appTop.hom.toMonoidHom a) =
      Units.map (pullback.fst (W.ι ≫ g) (genericPointInclusion X)).appTop.hom.toMonoidHom
        (Units.map W.ι.appTop.hom.toMonoidHom a) := by
    rw [units_map_appTop_comp, units_map_appTop_comp, genericFibreOpensMap,
      genericFibreMap_comp_fst]
  rw [genericFibreOrdOfPoint_eq_genericFibreOrdOfOpen g (W := W) ⟨y, hyW⟩,
    genericFibreOrdOfOpen_apply_ofMul, hu]
  exact genericFibreOrd_restrict_eq_zero (W.ι ≫ g) ⟨y, hyW⟩ _

/-- The order of vanishing is nonzero at only finitely many points of an integral open
subscheme. -/
private theorem finite_support_genericFibreOrdOfPoint_opens [NoetherianSpace Y] (W : Y.Opens)
    [AlgebraicGeometry.IsIntegral W.toScheme]
    (a : Additive ((Γ(pullback g (genericPointInclusion X), ⊤))ˣ)) :
    {y : Y | y ∈ W ∧ genericFibreOrdOfPoint g y a ≠ 0}.Finite := by
  have : NoetherianSpace W.toScheme := inferInstanceAs (NoetherianSpace ↥(W : Set Y))
  refine ((finite_support_genericFibreOrd (W.ι ≫ g) (Additive.ofMul
    (Units.map (genericFibreOpensMap g W).appTop.hom.toMonoidHom
      (Additive.toMul a)))).image Subtype.val).subset fun y hy => ⟨⟨y, hy.1⟩, fun hc =>
    hy.2 (((genericFibreOrdOfPoint_eq_genericFibreOrdOfOpen g (W := W) ⟨y, hy.1⟩ a).trans
      (genericFibreOrdOfOpen_apply g W ⟨y, hy.1⟩ a)).trans hc), rfl⟩

/-- **The order of vanishing of an invertible global function on the generic fibre is nonzero at
only finitely many points of `Y`.** -/
theorem finite_support_genericFibreOrdOfPoint [NoetherianSpace Y]
    (a : Additive ((Γ(pullback g (genericPointInclusion X), ⊤))ˣ)) :
    {y : Y | genericFibreOrdOfPoint g y a ≠ 0}.Finite := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun y : Y => ((exists_isIntegral_opens_of_etale g y).choose : Set Y))
    (fun y => (exists_isIntegral_opens_of_etale g y).choose.isOpen)
    fun y _ => Set.mem_iUnion.2 ⟨y, (exists_isIntegral_opens_of_etale g y).choose_spec.1⟩
  have hfin : ∀ i : Y, {y : Y | y ∈ (exists_isIntegral_opens_of_etale g i).choose ∧
      genericFibreOrdOfPoint g y a ≠ 0}.Finite := by
    intro i
    have : AlgebraicGeometry.IsIntegral (exists_isIntegral_opens_of_etale g i).choose.toScheme :=
      (exists_isIntegral_opens_of_etale g i).choose_spec.2
    exact finite_support_genericFibreOrdOfPoint_opens g _ a
  refine (Set.Finite.biUnion s.finite_toSet fun i _ => hfin i).subset fun y hy => ?_
  obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
  exact Set.mem_biUnion hi ⟨hyi, hy⟩

end Point

/-! ### Compatibility with restriction -/

section Restriction

variable {X Y Z : Scheme.{u}} [AlgebraicGeometry.IsIntegral X] [IsNormal X]

/-- **The order of vanishing at a point is compatible with restriction along a morphism of
`X`-schemes**: restricting a section of `j_* 𝐆_{m,K}` over `Z` to an étale `Z`-scheme `Y` and
taking its order of vanishing at a point `y` of `Y` gives the order of vanishing of the section at
the image of `y` in `Z`. -/
theorem genericFibreOrdOfPoint_appTop (gY : Y ⟶ X) (gZ : Z ⟶ X) [Etale gY] [Etale gZ]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian Z] (h : Y ⟶ Z) (hcomm : h ≫ gZ = gY) (y : Y)
    (a : (Γ(pullback gZ (genericPointInclusion X), ⊤))ˣ) :
    genericFibreOrdOfPoint gY y
        (Additive.ofMul (Units.map (genericFibreMap h hcomm).appTop.hom.toMonoidHom a)) =
      genericFibreOrdOfPoint gZ (h.base y) (Additive.ofMul a) := by
  have : Etale h := etale_of_etale_over h hcomm
  obtain ⟨WZ, hWZ, hWZi⟩ := exists_isIntegral_opens_of_etale gZ (h.base y)
  have : AlgebraicGeometry.IsIntegral WZ.toScheme := hWZi
  obtain ⟨WY, hyWY, hWYle, hWYi⟩ :
      ∃ WY : Y.Opens, y ∈ WY ∧ WY ≤ h ⁻¹ᵁ WZ ∧
        AlgebraicGeometry.IsIntegral WY.toScheme := by
    obtain ⟨W₀, hW₀, hW₀i⟩ := exists_isIntegral_opens_of_etale gY y
    have : AlgebraicGeometry.IsIntegral W₀.toScheme := hW₀i
    exact ⟨W₀ ⊓ h ⁻¹ᵁ WZ, ⟨hW₀, hWZ⟩, inf_le_right, isIntegral_inf_opens_of_mem hW₀ hWZ⟩
  have : AlgebraicGeometry.IsIntegral WY.toScheme := hWYi
  set h' : WY.toScheme ⟶ WZ.toScheme := Y.homOfLE hWYle ≫ (h ∣_ WZ) with hh'
  have hiota : h' ≫ WZ.ι = WY.ι ≫ h := by
    rw [hh', Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  have hcomm' : h' ≫ (WZ.ι ≫ gZ) = WY.ι ≫ gY := by
    rw [← Category.assoc, hiota, Category.assoc, hcomm]
  have hbase : h'.base ⟨y, hyWY⟩ = ⟨h.base y, hWZ⟩ :=
    Subtype.ext (congrArg (fun φ : WY.toScheme ⟶ Z => φ.base ⟨y, hyWY⟩) hiota)
  have hsq : genericFibreMap h' hcomm' ≫ genericFibreOpensMap gZ WZ =
      genericFibreOpensMap gY WY ≫ genericFibreMap h hcomm := by
    refine pullback.hom_ext ?_ ?_
    · have e₁ : genericFibreMap h' hcomm' ≫ genericFibreOpensMap gZ WZ ≫
          pullback.fst gZ (genericPointInclusion X) =
            pullback.fst (WY.ι ≫ gY) (genericPointInclusion X) ≫ WY.ι ≫ h := by
        rw [genericFibreOpensMap, genericFibreMap_comp_fst, ← Category.assoc,
          genericFibreMap_comp_fst, Category.assoc, hiota]
      have e₂ : genericFibreOpensMap gY WY ≫ genericFibreMap h hcomm ≫
          pullback.fst gZ (genericPointInclusion X) =
            pullback.fst (WY.ι ≫ gY) (genericPointInclusion X) ≫ WY.ι ≫ h := by
        rw [genericFibreMap_comp_fst, ← Category.assoc, genericFibreOpensMap,
          genericFibreMap_comp_fst, Category.assoc]
      rw [Category.assoc, Category.assoc, e₁, e₂]
    · simp [genericFibreOpensMap]
  have hu : Units.map (genericFibreMap h' hcomm').appTop.hom.toMonoidHom
        (Units.map (genericFibreOpensMap gZ WZ).appTop.hom.toMonoidHom a) =
      Units.map (genericFibreOpensMap gY WY).appTop.hom.toMonoidHom
        (Units.map (genericFibreMap h hcomm).appTop.hom.toMonoidHom a) := by
    rw [units_map_appTop_comp, units_map_appTop_comp, hsq]
  refine (genericFibreOrdOfPoint_eq_genericFibreOrdOfOpen gY (W := WY) ⟨y, hyWY⟩ _).trans ?_
  refine Eq.trans ?_ (genericFibreOrdOfPoint_eq_genericFibreOrdOfOpen gZ (W := WZ)
    ⟨h.base y, hWZ⟩ (Additive.ofMul a)).symm
  rw [genericFibreOrdOfOpen_apply_ofMul, genericFibreOrdOfOpen_apply_ofMul, ← hu]
  exact (genericFibreOrd_appTop (WY.ι ≫ gY) (WZ.ι ≫ gZ) h' (genericFibreMap h' hcomm')
    (genericFibreMap_comp_fst h' hcomm') ⟨y, hyWY⟩ _).trans (by rw [hbase])

end Restriction

end Stacks.EtaleCohomology

end
