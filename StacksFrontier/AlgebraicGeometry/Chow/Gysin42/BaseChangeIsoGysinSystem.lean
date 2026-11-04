module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Naturality
public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.ModuleIso
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardGysinSystem

/-!
# Gysin maps of the canonical Gysin system, and restriction of bivariant classes

For the Gysin system `Stacks.Chow.gysinSystemOfInvertible` of the first Chern class rule, the
Gysin map of an invertible module with a section depends on the module only through its
isomorphism class and on the section only through its zero scheme. Since this Gysin system is
natural under isomorphic base changes
(`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderBaseChangeIso`), the restriction of bivariant
classes along a base change is defined for it with no hypothesis on the Gysin system.

## Main definitions

* `Stacks.Chow.gysinComponentCycleOfIdeal`: the Gysin component cycle with the zero scheme of
  the section replaced by a quasi-coherent ideal sheaf.
* `Stacks.Chow.bivariantRestrictionOfInvertible`: the restriction `res(c)` of a bivariant class
  `c ∈ A^p(X ⟶ Y)` along a morphism `Y' ⟶ Y`.
* `Stacks.Chow.bivariantRestrictionAddHomOfInvertible`: the restriction map
  `A^p(X ⟶ Y) ⟶ A^p(X' ⟶ Y')` as a homomorphism of groups.

## Main results

* `Stacks.Chow.firstChernComponentClass_eq_of_moduleIso`: the first Chern class component rule
  of an invertible module depends only on its isomorphism class.
* `Stacks.Chow.gysinSystemOfInvertible_onChow_heq_of_moduleIso`,
  `Stacks.Chow.gysinSystemOfInvertible_onChow_eq_of_moduleIso`: two isomorphic invertible modules
  with sections having the same zero scheme have the same Gysin map.
* `Stacks.Chow.bivariantRestrictionOfInvertible_cap`: `res(c) ∩ α = c ∩ α`.
* `Stacks.Chow.bivariantRestrictionOfInvertible_comp`: restriction is compatible with
  compositions of base changes.

## References

* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v

namespace Stacks.Chow

open Stacks.Divisors

/-- The first Chern class component rule of an invertible module depends on the module only
through its isomorphism class. -/
theorem firstChernComponentClass_eq_of_moduleIso (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) {M N : X.Modules}
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (φ : M ≅ N) :
    firstChernComponentClass C p k M = firstChernComponentClass C p k N := by
  funext W hW hDim
  let : IsIntegral W.subscheme := hW
  let : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ p)
  have hT (L : X.Modules)
      [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
      ∀ x : W.subscheme, IsTrivializedNear ((Scheme.Modules.pullback W.subschemeι).obj L) x :=
    have := isInvertible_presheaf_modulePullback L W.subschemeι
    isTrivializedNear_of_isInvertible _
  exact mk_chernComponentCycle_eq_of_moduleIso C (W.subschemeι ≫ p) hDim
    ((Scheme.Modules.pullback W.subschemeι).mapIso φ) (hT M) (hT N)
    (exists_ne_zero_genericStalk (hT M _)).choose_spec
    (exists_ne_zero_genericStalk (hT N _)).choose_spec

section Congr

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)

/-- A dependent function applied to two equal quasi-coherent ideal sheaves takes heterogeneously
equal values. -/
theorem heq_of_eq_idealSheafData {Y : Scheme.{u}} {β : Y.IdealSheafData → Sort v} (f : ∀ D, β D)
    {D D' : Y.IdealSheafData} (hD : D = D') : HEq (f D) (f D') := by
  subst hD
  rfl

/-- The cycle `Stacks.Chow.gysinComponentCycle` attaches to an integral closed subscheme `W` of
delta-dimension `k + 1`, written as a function of a quasi-coherent ideal sheaf `D` in place of the
zero scheme of the section: the fundamental cycle of `W ∩ D` when `W` is not contained in `D`, and
the pushforward to `D` of a representative of the component rule when it is. -/
def gysinComponentCycleOfIdeal (chern : FirstChernComponentClassRule C p k)
    (D : X.IdealSheafData) (W : X.IdealSheafData) (hW : AlgebraicGeometry.IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    CycleGroup C (D.subschemeι ≫ p) k :=
  open Classical in
  if h : D ≤ W then
    properPushforward C (W.subschemeι ≫ p) (D.subschemeι ≫ p)
      (Scheme.IdealSheafData.inclusion h) (by simp) k (Quotient.out (chern W hW hDim))
  else
    cycleAssociatedToClosedSubscheme C (D.subschemeι ≫ p)
      ((W.comap D.subschemeι).subschemeι) k

/-- The Gysin component cycle of an invertible module and a section is the abstract one at the
zero scheme of that section: the module and the section enter only through their zero scheme. -/
theorem gysinComponentCycle_eq_ofIdeal (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (chern : FirstChernComponentClassRule C p k) :
    gysinComponentCycle C p k L s chern =
      gysinComponentCycleOfIdeal C p k chern (Stacks.Divisors.zeroScheme X L s) :=
  rfl

/-- Two rules on integral components along the inclusions of two equal ideal sheaves are
heterogeneously equal as soon as their cycle rules are. -/
theorem heq_integralComponentRule {D D' : X.IdealSheafData} (hD : D = D')
    {R : IntegralComponentRule C p (D.subschemeι ≫ p) D.subschemeι k}
    {R' : IntegralComponentRule C p (D'.subschemeι ≫ p) D'.subschemeι k}
    (hcyc : HEq R.cycle R'.cycle) : HEq R R' := by
  subst hD
  obtain ⟨c, hc⟩ := R
  obtain ⟨c', hc'⟩ := R'
  cases hcyc
  rfl

/-- The coefficientwise extension of a rule on integral components to Chow classes respects a
heterogeneous equality of rules along an equality of ideal sheaves. -/
theorem heq_integralComponentRule_extendChow {D D' : X.IdealSheafData} (hD : D = D')
    {R : IntegralComponentRule C p (D.subschemeι ≫ p) D.subschemeι k}
    {R' : IntegralComponentRule C p (D'.subschemeι ≫ p) D'.subschemeι k}
    (hR : HEq R R') : HEq R.extendChow R'.extendChow := by
  subst hD
  cases hR
  rfl

/-- Descending a homomorphism from cycles to Chow classes respects a heterogeneous equality of
the homomorphisms along an equality of ideal sheaves. -/
theorem heq_lift_rationalEquivalences {D D' : X.IdealSheafData} (hD : D = D')
    {F : CycleGroup C p (k + 1) →+ chowGroup C (D.subschemeι ≫ p) k}
    {F' : CycleGroup C p (k + 1) →+ chowGroup C (D'.subschemeι ≫ p) k} (hF : HEq F F')
    (hf : ∀ x ∈ rationalEquivalences C p (k + 1), F x = 0)
    (hf' : ∀ x ∈ rationalEquivalences C p (k + 1), F' x = 0) :
    HEq (QuotientAddGroup.lift (rationalEquivalences C p (k + 1)) F hf)
      (QuotientAddGroup.lift (rationalEquivalences C p (k + 1)) F' hf') := by
  subst hD
  cases hF
  rfl

/-- Two heterogeneously equal homomorphisms of Chow groups along an equality of ideal sheaves take
heterogeneously equal values. -/
theorem heq_chowGroupHom_apply {D D' : X.IdealSheafData} (hD : D = D')
    {F : chowGroup C p (k + 1) →+ chowGroup C (D.subschemeι ≫ p) k}
    {F' : chowGroup C p (k + 1) →+ chowGroup C (D'.subschemeι ≫ p) k} (hF : HEq F F')
    (α : chowGroup C p (k + 1)) : HEq (F α) (F' α) := by
  subst hD
  cases hF
  rfl

/-- A heterogeneous equality of Chow classes along an equality of ideal sheaves, read as an
identity: the class on the left pushes forward to the class on the right along the isomorphism of
the two subschemes. -/
theorem chowPushforwardOfIso_eqToHom_of_heq {D D' : X.IdealSheafData} (hD : D = D')
    (hbase : eqToHom (congrArg Scheme.IdealSheafData.subscheme hD) ≫ (D'.subschemeι ≫ p) =
      D.subschemeι ≫ p)
    {x : chowGroup C (D.subschemeι ≫ p) k} {y : chowGroup C (D'.subschemeι ≫ p) k}
    (hxy : HEq x y) :
    chowPushforwardOfIso C (D.subschemeι ≫ p) (D'.subschemeι ≫ p)
        (eqToHom (congrArg Scheme.IdealSheafData.subscheme hD)) hbase k x = y := by
  subst hD
  cases hxy
  exact chowPushforwardOfIso_id C (D.subschemeι ≫ p) k x

end Congr

/-! ### The Gysin map of the canonical system sees an invertible module only up to isomorphism -/

/-- Two isomorphic invertible modules with sections whose zero schemes agree have heterogeneously
equal Gysin maps for `Stacks.Chow.gysinSystemOfInvertible`. -/
theorem gysinSystemOfInvertible_onChow_heq_of_moduleIso (C : ChowSituation.{u})
    (h : GysinOfInvertibleDescends C) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (k : ℤ) {M N : X.Modules}
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (sM : Γ(M, ⊤)) (sN : Γ(N, ⊤)) (φ : M ≅ N)
    (hz : Stacks.Divisors.zeroScheme X M sM = Stacks.Divisors.zeroScheme X N sN) :
    HEq ((gysinSystemOfInvertible C).onChow p M sM k)
      ((gysinSystemOfInvertible C).onChow p N sN k) := by
  have hchern := firstChernComponentClass_eq_of_moduleIso C p k φ
  have hcyc : HEq (gysinComponentCycle C p k M sM (firstChernComponentClass C p k M))
      (gysinComponentCycle C p k N sN (firstChernComponentClass C p k N)) := by
    rw [gysinComponentCycle_eq_ofIdeal, gysinComponentCycle_eq_ofIdeal, hchern]
    exact heq_of_eq_idealSheafData _ hz
  exact heq_lift_rationalEquivalences C p k hz
    (heq_integralComponentRule_extendChow C p k hz (heq_integralComponentRule C p k hz hcyc))
    (h p M sM k) (h p N sN k)

/-- Two isomorphic invertible modules with sections whose zero schemes agree have the same Gysin
map for `Stacks.Chow.gysinSystemOfInvertible`, after pushforward along the isomorphism of the two
zero schemes. -/
theorem gysinSystemOfInvertible_onChow_eq_of_moduleIso (C : ChowSituation.{u})
    (h : GysinOfInvertibleDescends C) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (k : ℤ) {M N : X.Modules}
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (sM : Γ(M, ⊤)) (sN : Γ(N, ⊤)) (φ : M ≅ N)
    (hz : Stacks.Divisors.zeroScheme X M sM = Stacks.Divisors.zeroScheme X N sN)
    (hbase : eqToHom (congrArg Scheme.IdealSheafData.subscheme hz) ≫
        ((Stacks.Divisors.zeroScheme X N sN).subschemeι ≫ p) =
      (Stacks.Divisors.zeroScheme X M sM).subschemeι ≫ p)
    (α : chowGroup C p (k + 1)) :
    chowPushforwardOfIso C ((Stacks.Divisors.zeroScheme X M sM).subschemeι ≫ p)
        ((Stacks.Divisors.zeroScheme X N sN).subschemeι ≫ p)
        (eqToHom (congrArg Scheme.IdealSheafData.subscheme hz)) hbase k
        ((gysinSystemOfInvertible C).onChow p M sM k α) =
      (gysinSystemOfInvertible C).onChow p N sN k α :=
  chowPushforwardOfIso_eqToHom_of_heq C p k hz hbase
    (heq_chowGroupHom_apply C p k hz
      (gysinSystemOfInvertible_onChow_heq_of_moduleIso C h p k sM sN φ hz) α)

/-! ### Restriction of bivariant classes -/

section Restriction

open CategoryTheory.Limits

variable (C : ChowSituation.{u}) {X Y Y' : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX)
  (b : Y' ⟶ Y) [LocallyOfFiniteType b] (p : ℤ)

/-- The restriction `res(c)` of a bivariant class `c ∈ A^p(X ⟶ Y)` along a morphism
`b : Y' ⟶ Y`, for the Gysin system of the first Chern class rule of an invertible module: the
bivariant class of degree `p` for the base change `X ×_Y Y' ⟶ Y'` with `res(c) ∩ α = c ∩ α`. -/
@[stacks 0F9Z]
def bivariantRestrictionOfInvertible
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) :
    BivariantClass C (gysinSystemOfInvertible C) (pullback.fst f b ≫ sX) (b ≫ sY)
      (pullback.snd f b) (pullbackSnd_comp_structureMorphism_eq C sX sY f hf b) p :=
  bivariantRestriction C (gysinSystemOfInvertible C) sX sY f hf b p
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c

/-- The restriction caps by the cap operation of `c`: `res(c) ∩ α = c ∩ α`, after the canonical
identification of the two fibre products. -/
@[stacks 0F9Z]
theorem bivariantRestrictionOfInvertible_cap
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) {T : Scheme.{u}}
    (g : T ⟶ Y') [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ (b ≫ sY)) k) :
    (bivariantRestrictionOfInvertible C sX sY f hf b p c).cap g k α =
      bivariantRestrictionCap C (gysinSystemOfInvertible C) sX sY f hf b p c g k α :=
  rfl

/-- The restriction map `A^p(X ⟶ Y) ⟶ A^p(X' ⟶ Y')` along `b : Y' ⟶ Y`, as a homomorphism of
groups, for the Gysin system of the first Chern class rule of an invertible module. -/
@[stacks 0F9Z]
def bivariantRestrictionAddHomOfInvertible :
    BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p →+
      BivariantClass C (gysinSystemOfInvertible C) (pullback.fst f b ≫ sX) (b ≫ sY)
        (pullback.snd f b) (pullbackSnd_comp_structureMorphism_eq C sX sY f hf b) p :=
  bivariantRestrictionAddHom C (gysinSystemOfInvertible C) sX sY f hf b p
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)

variable {Y'' : Scheme.{u}} (b' : Y'' ⟶ Y') [LocallyOfFiniteType b']

/-- Restriction is compatible with composition of base changes: restricting along `b` and then
along `b'` agrees with restricting along `b' ≫ b`, after the canonical identification of the two
iterated fibre products. -/
@[stacks 0F9Z]
theorem bivariantRestrictionOfInvertible_comp
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) {T : Scheme.{u}}
    (g : T ⟶ Y'') [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ (b' ≫ (b ≫ sY))) k) :
    chowPushforwardOfIso C
        (pullback.fst (pullback.snd (pullback.snd f b) b') g ≫
          (pullback.fst (pullback.snd f b) b' ≫ (pullback.fst f b ≫ sX)))
        (pullback.fst (pullback.snd f (b' ≫ b)) g ≫ (pullback.fst f (b' ≫ b) ≫ sX))
        (iteratedRestrictionIso f b b' g).hom
        (iteratedRestrictionIso_hom_comp C sX f b b' g) (k - p)
        ((bivariantRestrictionOfInvertible C (pullback.fst f b ≫ sX) (b ≫ sY)
          (pullback.snd f b) (pullbackSnd_comp_structureMorphism_eq C sX sY f hf b) b' p
          (bivariantRestrictionOfInvertible C sX sY f hf b p c)).cap g k α) =
      (bivariantRestrictionOfInvertible C sX sY f hf (b' ≫ b) p c).cap g k
        (chowGroupCongr C (congrArg (g ≫ ·) (Category.assoc b' b sY).symm) k α) :=
  bivariantRestriction_comp C (gysinSystemOfInvertible C) sX sY f hf b p b'
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c g k α

end Restriction

end Stacks.Chow

end
