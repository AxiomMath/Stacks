module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericFibreOrdLocallyIntegral

/-!
# The second map of Stacks 03RI on sections over an arbitrary étale `X`-scheme

Let `X` be an integral normal scheme with generic point `η`, function field `K` and inclusion
`j : Spec K ⟶ X`, and let `X_0` be its set of closed points with inclusions `i_x`. The second map
of the fundamental exact sequence of Stacks 03RI,
`0 → 𝐆_{m,X} → j_* 𝐆_{m,η} → ⨁_{x ∈ X_0} (i_x)_* 𝐙 → 0`,
is read on sections over an étale `X`-scheme `U` as the homomorphism
`Γ(η ×_X U, 𝒪^*) → ⨁_{x ∈ X_0} Γ(x ×_X U, 𝐙)`
taking an invertible function on the generic fibre to its family of orders of vanishing. This
file constructs this homomorphism for an arbitrary locally Noetherian étale `X`-scheme `U` with
Noetherian underlying space, the order of vanishing at a point of `U` being
`Stacks.EtaleCohomology.genericFibreOrdOfPoint`, computed in an integral open neighbourhood of
that point.

## Main definitions

* `Stacks.EtaleCohomology.etaleGenericFibreOrdOfPoint`: the order of vanishing at a point of an
  arbitrary étale `X`-scheme `U` of an invertible global function on the generic fibre of `U`.
* `Stacks.EtaleCohomology.residueFibreOrdOfPoint`: the `x`-component of the second map, as a
  homomorphism into the locally constant `𝐙`-valued maps on the fibre `x ×_X U`.
* `Stacks.EtaleCohomology.integerSkyscraperDivisorOfPoint`: the same component read as a
  homomorphism into the sections of `(i_x)_* 𝐙` over `U`.
* `Stacks.EtaleCohomology.closedPointDivisorSections`: the second map of the fundamental exact
  sequence on sections over an arbitrary étale `X`-scheme, with values in
  `⨁_{x ∈ X_0} ((i_x)_* 𝐙)(U)`.

## Main results

* `Stacks.EtaleCohomology.closedPointDivisorSections_restrict_eq_zero`: the sequence is a
  complex: an invertible global function on `U` has order of vanishing zero on every fibre.
* `Stacks.EtaleCohomology.etaleGenericFibreOrdOfPoint_appTop`: the order of vanishing at a point
  is compatible with restriction along a morphism of the small étale site.
* `Stacks.EtaleCohomology.subsingleton_pullback_fromSpecResidueField`: the fibre
  `Z ×_X Spec κ(x)` has at most one point when the preimage of `x` in `Z` does.
* `Stacks.EtaleCohomology.nonempty_pullback_fromSpecResidueField`: the fibre `Z ×_X Spec κ(x)` is
  nonempty when some point of `Z` lies over `x`.

## References

* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI): the fundamental exact
  sequence.
* [Stacks Project, Tag 03P5](https://stacks.math.columbia.edu/tag/03P5): the sections of a
  constant sheaf are the locally constant maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

/-! ### The order of vanishing at a point of an arbitrary étale neighbourhood -/

section Ord

/-- The structure morphism of an étale `X`-scheme is étale. -/
private instance etale_hom_of_etale {X : Scheme.{u}} (U : X.Etale) : Etale U.hom := U.prop

private instance isLocallyNoetherian_obj_id {X : Scheme.{u}} (U : X.Etale)
    [IsLocallyNoetherian U.left] : IsLocallyNoetherian ((𝟭 Scheme).obj U.left) :=
  inferInstanceAs (IsLocallyNoetherian U.left)

private instance noetherianSpace_obj_id {X : Scheme.{u}} (U : X.Etale)
    [NoetherianSpace U.left] : NoetherianSpace ((𝟭 Scheme).obj U.left) :=
  inferInstanceAs (NoetherianSpace U.left)

private instance isIntegral_obj_id {X : Scheme.{u}} (U : X.Etale)
    [AlgebraicGeometry.IsIntegral U.left] :
    AlgebraicGeometry.IsIntegral ((𝟭 Scheme).obj U.left) :=
  inferInstanceAs (AlgebraicGeometry.IsIntegral U.left)

variable {X : Scheme.{u}} [AlgebraicGeometry.IsIntegral X] [IsNormal X] (U : X.Etale)
  [IsLocallyNoetherian U.left]

/-- **The order of vanishing at a point of `U` of an invertible global function on the generic
fibre `η ×_X U`**, for `U` an arbitrary étale `X`-scheme. This is
`Stacks.EtaleCohomology.genericFibreOrdOfPoint` at the structure morphism of `U`. -/
def etaleGenericFibreOrdOfPoint (y : U.left) :
    Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ) →+ ℤ :=
  have : IsLocallyNoetherian ((𝟭 Scheme).obj U.left) :=
    inferInstanceAs (IsLocallyNoetherian U.left)
  have : Etale U.hom := U.prop
  genericFibreOrdOfPoint (X := X) U.hom y

/-- **On an irreducible `U` the order of vanishing at a point is the one of the irreducible
case.** -/
theorem etaleGenericFibreOrdOfPoint_eq_etaleGenericFibreOrd [AlgebraicGeometry.IsIntegral U.left]
    (y : U.left) (a : Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ)) :
    etaleGenericFibreOrdOfPoint U y a = etaleGenericFibreOrd U y a := by
  have hiso : (⊤ : U.left.Opens).toScheme ≅ (𝟭 Scheme).obj U.left :=
    IsOpenImmersion.isoOfRangeEq (⊤ : U.left.Opens).ι (𝟙 _) (by simp)
  have : AlgebraicGeometry.IsIntegral (⊤ : U.left.Opens).toScheme :=
    AlgebraicGeometry.IsIntegral.of_isIso hiso.inv
  refine (genericFibreOrdOfPoint_eq_genericFibreOrdOfOpen (X := X) U.hom
    (W := (⊤ : U.left.Opens)) ⟨y, trivial⟩ a).trans ?_
  rw [genericFibreOrdOfOpen_apply]
  exact genericFibreOrd_appTop (X := X) ((⊤ : U.left.Opens).ι ≫ U.hom) U.hom
    (⊤ : U.left.Opens).ι (genericFibreOpensMap (X := X) U.hom (⊤ : U.left.Opens))
    (genericFibreMap_comp_fst (X := X) (⊤ : U.left.Opens).ι rfl) ⟨y, trivial⟩ _

/-- **An invertible global function on `U` has order of vanishing zero at every point of `U`.** -/
theorem etaleGenericFibreOrdOfPoint_restrict_eq_zero (y : U.left) (a : (Γ(U.left, ⊤))ˣ) :
    etaleGenericFibreOrdOfPoint U y (Additive.ofMul (Units.map
      (pullback.fst U.hom (genericPointInclusion X)).appTop.hom.toMonoidHom a)) = 0 :=
  genericFibreOrdOfPoint_restrict_eq_zero (X := X) U.hom y a

/-- **The order of vanishing of an invertible global function on the generic fibre is nonzero at
only finitely many points of `U`.** -/
theorem finite_support_etaleGenericFibreOrdOfPoint [NoetherianSpace U.left]
    (a : Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ)) :
    {y : U.left | etaleGenericFibreOrdOfPoint U y a ≠ 0}.Finite :=
  finite_support_genericFibreOrdOfPoint (X := X) U.hom a

end Ord

/-! ### The fibre over a point that the étale scheme meets once -/

/-- **A point of the fibre `Z ×_X Spec κ(x)` of a morphism of schemes lies over `x`.** -/
theorem base_pullback_fst_fromSpecResidueField {X Z : Scheme.{u}} (q : Z ⟶ X) (x : X)
    (y : ↥(pullback q (X.fromSpecResidueField x))) :
    q ((pullback.fst q (X.fromSpecResidueField x)) y) = x := by
  have h := congrArg (fun φ : pullback q (X.fromSpecResidueField x) ⟶ X => φ y)
    (pullback.condition (f := q) (g := X.fromSpecResidueField x))
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] at h
  exact h

/-- **The fibre `Z ×_X Spec κ(x)` has at most one point as soon as the preimage of `x` in `Z`
does.** -/
theorem subsingleton_pullback_fromSpecResidueField {X Z : Scheme.{u}} (q : Z ⟶ X) (x : X)
    (h : Set.Subsingleton (q.base ⁻¹' {x})) :
    Subsingleton ↥(pullback q (X.fromSpecResidueField x)) :=
  ⟨fun a b => (pullback.fst q (X.fromSpecResidueField x)).isEmbedding.injective
    (h (base_pullback_fst_fromSpecResidueField q x a)
      (base_pullback_fst_fromSpecResidueField q x b))⟩

/-- **The fibre `Z ×_X Spec κ(x)` is nonempty as soon as some point of `Z` lies over `x`.** -/
theorem nonempty_pullback_fromSpecResidueField {X Z : Scheme.{u}} (q : Z ⟶ X) {x : X} {z : Z}
    (hz : q.base z = x) : Nonempty ↥(pullback q (X.fromSpecResidueField x)) := by
  have hmem : z ∈ Set.range (pullback.fst q (X.fromSpecResidueField x)).base := by
    rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
    exact hz
  exact ⟨hmem.choose⟩

/-! ### Compatibility with restriction along a morphism of the small étale site -/

/-- **The second map of the fundamental exact sequence of Stacks 03RI is compatible with
restriction along a morphism of the small étale site of `X`**, read on the order of vanishing at a
point. -/
theorem etaleGenericFibreOrdOfPoint_appTop {X : Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
    [IsNormal X] {U V : X.Etale} [IsLocallyNoetherian U.left] [IsLocallyNoetherian V.left]
    (φ : U ⟶ V) (y : U.left)
    (a : (Γ(pullback V.hom (genericPointInclusion X), ⊤))ˣ) :
    etaleGenericFibreOrdOfPoint U y
        (Additive.ofMul (Units.map (etaleGenericFibreMap φ).appTop.hom.toMonoidHom a)) =
      etaleGenericFibreOrdOfPoint V (φ.left.base y) (Additive.ofMul a) := by
  have hw : φ.left ≫ V.hom = U.hom := MorphismProperty.Over.w φ
  have hmap : etaleGenericFibreMap φ = genericFibreMap (X := X) φ.left hw := by
    rw [etaleGenericFibreMap, genericFibreMap]
  rw [hmap]
  exact genericFibreOrdOfPoint_appTop (X := X) U.hom V.hom φ.left hw y a

/-! ### The second map on sections over an arbitrary étale neighbourhood -/

section Divisor

variable {X : Scheme.{u}} [AlgebraicGeometry.IsIntegral X] [IsNormal X] (U : X.Etale)
  [IsLocallyNoetherian U.left]

/-- **The `x`-component of the second map of the fundamental exact sequence of Stacks 03RI, on
sections over an arbitrary étale `X`-scheme `U`**: an invertible global function on the generic
fibre `η ×_X U` is sent to the `𝐙`-valued map on the fibre `x ×_X U` taking a point of that fibre
to the order of vanishing, at its image in `U`, of the function read as a rational function on an
integral open neighbourhood of that image. -/
def residueFibreOrdOfPoint (x : X) :
    Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ) →+
      LocallyConstant ((smallEtaleBaseChange (X.fromSpecResidueField x)).obj U).left
        (ULift.{max (u + 1) v} ℤ) where
  toFun a :=
    ⟨fun y => ULift.up (etaleGenericFibreOrdOfPoint U
      ((pullback.fst U.hom (X.fromSpecResidueField x)) y) a),
      IsLocallyConstant.of_discrete _⟩
  map_zero' := LocallyConstant.ext fun y => by
    change ULift.up (etaleGenericFibreOrdOfPoint U _ 0) = _
    rw [map_zero]
    rfl
  map_add' a b := LocallyConstant.ext fun y => by
    change ULift.up (etaleGenericFibreOrdOfPoint U _ (a + b)) = _
    rw [map_add]
    rfl

/-- The value of `Stacks.EtaleCohomology.residueFibreOrdOfPoint U x a` at a point `y` of the fibre
`x ×_X U` is the order of vanishing of `a` at the image of `y` in `U`, lifted to `ULift ℤ`. -/
@[simp]
theorem residueFibreOrdOfPoint_apply (x : X)
    (a : Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ))
    (y : ((smallEtaleBaseChange (X.fromSpecResidueField x)).obj U).left) :
    residueFibreOrdOfPoint.{u, v} U x a y =
      ULift.up (etaleGenericFibreOrdOfPoint U
        ((pullback.fst U.hom (X.fromSpecResidueField x)) y) a) :=
  rfl

/-- **An invertible global function on `U` has order of vanishing zero on every fibre.** -/
theorem residueFibreOrdOfPoint_restrict_eq_zero (x : X) (a : (Γ(U.left, ⊤))ˣ) :
    residueFibreOrdOfPoint.{u, v} U x (Additive.ofMul (Units.map
      (pullback.fst U.hom (genericPointInclusion X)).appTop.hom.toMonoidHom a)) = 0 :=
  LocallyConstant.ext fun y => by
    rw [residueFibreOrdOfPoint_apply, etaleGenericFibreOrdOfPoint_restrict_eq_zero]
    rfl

/-- **The components of the second map are nonzero at only finitely many points of `X`.** -/
theorem finite_support_residueFibreOrdOfPoint [NoetherianSpace U.left]
    (a : Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ)) :
    {x : X | residueFibreOrdOfPoint.{u, v} U x a ≠ 0}.Finite := by
  refine Set.Finite.subset
    ((finite_support_etaleGenericFibreOrdOfPoint U a).image fun y => U.hom y) ?_
  intro x hx
  obtain ⟨y, hy⟩ : ∃ y, etaleGenericFibreOrdOfPoint U
      ((pullback.fst U.hom (X.fromSpecResidueField x)) y) a ≠ 0 := by
    by_contra hc
    refine hx (LocallyConstant.ext fun y => ?_)
    rw [residueFibreOrdOfPoint_apply, not_not.1 fun h => hc ⟨y, h⟩]
    rfl
  exact ⟨_, hy, hom_base_pullback_fst_fromSpecResidueField x U y⟩

/-- **The `x`-component of the second map of Stacks 03RI, as a map into the sections of
`(i_x)_* 𝐙`**, through the identification of those sections with the locally constant `𝐙`-valued
maps on the fibre `x ×_X U` of Stacks 03P5. -/
def integerSkyscraperDivisorOfPoint (x : X) :
    Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ) →+
      (integerSkyscraper.{u, v} X x).obj.obj (op U) :=
  ((integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} X x U).inv.hom).comp
    (residueFibreOrdOfPoint.{u, v} U x)

/-- **An invertible global function on `U` has trivial image in `((i_x)_* 𝐙)(U)`.** -/
theorem integerSkyscraperDivisorOfPoint_restrict_eq_zero (x : X) (a : (Γ(U.left, ⊤))ˣ) :
    integerSkyscraperDivisorOfPoint.{u, v} U x (Additive.ofMul (Units.map
      (pullback.fst U.hom (genericPointInclusion X)).appTop.hom.toMonoidHom a)) = 0 := by
  rw [integerSkyscraperDivisorOfPoint, AddMonoidHom.comp_apply,
    residueFibreOrdOfPoint_restrict_eq_zero.{u, v} U x a, map_zero]

/-- **Only finitely many points of `X` carry a nonzero component of the second map.** -/
theorem finite_support_integerSkyscraperDivisorOfPoint [NoetherianSpace U.left]
    (a : Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ)) :
    {x : X | integerSkyscraperDivisorOfPoint.{u, v} U x a ≠ 0}.Finite :=
  (finite_support_residueFibreOrdOfPoint.{u, v} U a).subset fun x hx hc =>
    hx (by rw [integerSkyscraperDivisorOfPoint, AddMonoidHom.comp_apply, hc, map_zero])

end Divisor

/-! ### The second map of Stacks 03RI on sections over an arbitrary étale `X`-scheme -/

section Sequence

variable {X : Scheme.{u}} [AlgebraicGeometry.IsIntegral X] [IsNormal X] (U : X.Etale)
  [IsLocallyNoetherian U.left] [NoetherianSpace U.left]

/-- **The second map of the fundamental exact sequence
`0 → 𝐆_{m,X} → j_* 𝐆_{m,η} → ⨁_{x ∈ X_0} (i_x)_* 𝐙 → 0`, on sections over an arbitrary étale
`X`-scheme `U`**: an invertible global function on the generic fibre `η ×_X U` is sent to the
finitely supported family of its orders of vanishing in `⨁_{x ∈ X_0} ((i_x)_* 𝐙)(U)`, the member
at a closed point `x` being the locally constant `𝐙`-valued map on the fibre `x ×_X U` recording
the order of vanishing at each point of `U` over `x`. -/
@[stacks 03RI "the second map on sections over an arbitrary étale X-scheme, for X integral and
normal"]
def closedPointDivisorSections :
    Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ) →+
      DirectSum ↥(closedPoints X)
        fun x : closedPoints X => (integerSkyscraper.{u, v} X x.1).obj.obj (op U) where
  toFun a := directSumOfFiniteSupport
    (fun x : closedPoints X => integerSkyscraperDivisorOfPoint.{u, v} U x.1 a)
    ((finite_support_integerSkyscraperDivisorOfPoint.{u, v} U a).preimage
      Subtype.val_injective.injOn)
  map_zero' := DFinsupp.ext fun x => by
    rw [directSumOfFiniteSupport_apply, map_zero, DFinsupp.zero_apply]
  map_add' _ _ := DFinsupp.ext fun x => by
    rw [directSumOfFiniteSupport_apply, DFinsupp.add_apply, directSumOfFiniteSupport_apply,
      directSumOfFiniteSupport_apply, map_add]

/-- The component of `Stacks.EtaleCohomology.closedPointDivisorSections U a` at a closed point `x`
is `Stacks.EtaleCohomology.integerSkyscraperDivisorOfPoint U x a`. -/
@[simp]
theorem closedPointDivisorSections_apply
    (a : Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ)) (x : closedPoints X) :
    closedPointDivisorSections.{u, v} U a x = integerSkyscraperDivisorOfPoint.{u, v} U x.1 a :=
  directSumOfFiniteSupport_apply _ _ x

/-- **The fundamental exact sequence is a complex on sections over an arbitrary étale
`X`-scheme `U`**: the restriction to the generic fibre of an invertible global function on `U` has
zero family of orders of vanishing. -/
@[stacks 03RI "the sequence on sections over an arbitrary étale X-scheme is a complex, for X
integral and normal"]
theorem closedPointDivisorSections_restrict_eq_zero (a : (Γ(U.left, ⊤))ˣ) :
    closedPointDivisorSections.{u, v} U (Additive.ofMul (Units.map
      (pullback.fst U.hom (genericPointInclusion X)).appTop.hom.toMonoidHom a)) = 0 :=
  DFinsupp.ext fun x => by
    rw [closedPointDivisorSections_apply.{u, v} U _ x,
      integerSkyscraperDivisorOfPoint_restrict_eq_zero.{u, v} U x.1 a, DFinsupp.zero_apply]

end Sequence

end Stacks.EtaleCohomology

end
