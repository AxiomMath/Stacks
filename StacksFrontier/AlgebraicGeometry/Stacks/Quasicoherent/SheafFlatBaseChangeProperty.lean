module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentModuleUniverse
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageSmoothLocalCriterion

/-!
# The flat base change property, read on sheaves (Stacks 0762)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `F` a presheaf of modules over
the structure sheaf of **Stacks 06TV**. An arrow `φ : x ⟶ y` of `𝒳` over a morphism of schemes
`a : U ⟶ V` gives the comparison map `c_φ : a_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of **Stacks 06WC**,
and **Stacks 0762** says `F` has the *flat base change property* when `c_φ` is an isomorphism
whenever `a` is flat. In the source `F` is a sheaf on `𝒳_ét` and `a_{small}^*` is the inverse
image of *sheaves* of modules, that is the étale sheafification of the presheaf inverse image.

## Why a second reading is needed

`AlgebraicGeometry.Stack.HasFlatBaseChangeProperty` (and its universe-free form
`AlgebraicGeometry.Stack.HasFlatBaseChangePropertyUnivLE`) asks that the comparison map
`AlgebraicGeometry.Stack.restrictModulePullbackComparison` be an isomorphism of *presheaves* of
modules, its source being `PresheafOfModules.pullback`, the presheaf inverse image (a left Kan
extension), with no sheafification. That is strictly stronger than **Stacks 0762**, and it fails
for quasi-coherent modules, so that with it `QCoh(𝒪_𝒳) ⊄ LQCoh^fbc(𝒪_𝒳)`, contrary to
**Stacks 06WK**. Three examples, over a field `k`:

1. *(the Jouanolou device)* Let `𝒳 = (Sch/ℙ¹)_{fppf}`, `F = 𝒪(-1)` and let `a : W ⟶ ℙ¹` be an
   affine `𝔸¹`-bundle with `W` affine (Jouanolou's device), which is flat. At the object `W` of
   the small étale site of `W`, the presheaf inverse image is the colimit of
   `Γ(V', 𝒪(-1)) ⊗_{𝒪(V')} 𝒪(W)` over pairs of an étale `V' ⟶ ℙ¹` and a `ℙ¹`-morphism
   `s : W ⟶ V'`. The fibres of `a` are connected and those of `V' ⟶ ℙ¹` are discrete, so `s(W)`
   is an open of `V'` mapping bijectively and étale, hence isomorphically, onto `ℙ¹`; every term
   therefore maps to one through `Γ(ℙ¹, 𝒪(-1)) = 0`, and the colimit is `0`. The target is
   `Γ(W, a^*𝒪(-1)) ≠ 0`. So `c_φ` is not an isomorphism of presheaves.
2. *(the same with `U = ℙ¹ × ℙ¹ ∖ Δ`)* With `π = pr₁ : U ⟶ ℙ¹`, smooth with fibres `𝔸¹`, and `U`
   affine: every `s : U ⟶ V'` over `ℙ¹` with `V'` étale factors as `σ ∘ π` (the fibres are
   geometrically connected and `V' ⟶ ℙ¹` is unramified, so its diagonal is open; then fpqc
   descent), so the presheaf inverse image at `U` is `Γ(ℙ¹, 𝒪(-1)) ⊗ 𝒪(U) = 0`, while
   `Γ(U, π^*𝒪(-1)) ≠ 0`. Note that the restriction of `𝒪(-1)` to the chart `𝔸¹ ⊔ 𝔸¹` is
   isomorphic to `𝒪`, which *does* have the presheaf-level property; so that property is not
   even local on the stack.
3. *(refuting Stacks 0771 (4)(b) in the presheaf reading)* Let `i : pt ⟶ ℙ¹` be a closed point
   and `G = i_*𝒪`, a quasi-coherent module, which is `R⁰i_*` of a module in `LQCoh^fbc` of the
   point. With `π` as in (2), the presheaf inverse image at `U` is `𝒪(U) ⊗_k k = 𝒪(U)` while
   the target is `Γ(U ∩ π⁻¹(pt), 𝒪) = k[t]`.

In each case the *sheafified* comparison is an isomorphism, as it must be for a quasi-coherent
module (flat base change for quasi-coherent modules on schemes).

## The reading of this file

`AlgebraicGeometry.Stack.HasSheafFlatBaseChangeProperty` keeps the same comparison map
`restrictModulePullbackComparisonUnivLE` and asks of it, for every arrow over a flat morphism,
that it be *locally injective and locally surjective* for the étale topology of the small site,
i.e. a local isomorphism. For a module which is an étale sheaf — the situation of the source —
the target `F|_{U_ét}` is a sheaf (`AlgebraicGeometry.Stack.restrictModuleToSmallEtale_isSheaf`),
and the condition says exactly that the map from the étale sheafification of the presheaf inverse
image, which is the inverse image `a_{small}^*` of sheaves of modules, to `F|_{U_ét}` is an
isomorphism: `AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_iff_isIso_presheafToSheaf`.
So this is **Stacks 0762**.

The predicate is stated for an arbitrary topology `τ` below the fppf one and an arbitrary module
universe `m` above the universe of the schemes, as `HasFlatBaseChangePropertyUnivLE` is, and the
base predicate implies it
(`AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_of_hasFlatBaseChangePropertyUnivLE`).

## Main definitions

* `AlgebraicGeometry.Stack.HasSheafFlatBaseChangeProperty`: **Stacks 0762**.
* `AlgebraicGeometry.Stack.IsLocallyQuasicoherentWithSheafFlatBaseChange`: membership in
  `LQCoh^fbc(𝒪_𝒳)` for a presheaf of modules on the étale site: locally quasi-coherent
  (**Stacks 06WJ**) with the flat base change property of **Stacks 0762**.
* `AlgebraicGeometry.Stack.lqcohSheafFbcEtaleModules`: `LQCoh^fbc(𝒪_𝒳)` as an object property
  of `Mod(𝒳_ét, 𝒪_𝒳)`, the étale sheaves of modules of an algebraic stack.
* `AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules`: `LQCoh^fbc(𝒪_𝒳)` as an object property of
  `Mod(𝒪_𝒳)`, the fppf sheaves of modules of an algebraic stack.
* `AlgebraicGeometry.Stack.sheafFlatBaseChangePropertyRule` and
  `AlgebraicGeometry.Stack.locallyQuasicoherentSheafFlatBaseChangeRule`: the corresponding rules
  in the sense of **Stacks 076Z**, at section universe `u + 1`.

## Main results

* `AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_of_iso`: the property is invariant
  under isomorphism.
* `AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_iff_isIso_presheafToSheaf`: for an
  étale sheaf, the property is that the sheafified comparison maps are isomorphisms.
* `AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_of_hasFlatBaseChangePropertyUnivLE`,
  `AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_of_hasFlatBaseChangeProperty`,
  `AlgebraicGeometry.Stack.isLocallyQuasicoherentWithSheafFlatBaseChange_of_flatBaseChange` and
  `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE_le`: the
  presheaf-level notions of the library imply these.

## References

* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK)
* [Stacks Project, Tag 0761](https://stacks.math.columbia.edu/tag/0761)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w m t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

section Predicate

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- **Stacks 0762.** A presheaf of modules over the structure sheaf of a category fibred in
groupoids *has the flat base change property* when, for every arrow `φ : x ⟶ y` of `𝒳` lying
over a flat morphism of schemes `a : U ⟶ V`, the comparison map
`c_φ : a_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of **Stacks 0761** is a local isomorphism for the
étale topology of the small site of `U`, that is locally injective and locally surjective.

For an étale sheaf this says that the comparison map of *sheaves* of modules, out of the
sheafified inverse image, is an isomorphism, which is the source's condition; see
`AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_iff_isIso_presheafToSheaf`. -/
abbrev HasSheafFlatBaseChangeProperty [UnivLE.{u, m}]
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ).obj) : Prop :=
  ∀ {x y : 𝒳} (φ : x ⟶ y), Flat (B.inclusion.map (p.map φ).left) →
    Presheaf.IsLocallyInjective
        (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
        ((PresheafOfModules.toPresheaf _).map
          (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F)) ∧
      Presheaf.IsLocallySurjective
        (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
        ((PresheafOfModules.toPresheaf _).map
          (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F))

/-- The presheaf-level flat base change property of the library implies **Stacks 0762**: an
isomorphism of presheaves is locally injective and locally surjective. -/
theorem hasSheafFlatBaseChangeProperty_of_hasFlatBaseChangePropertyUnivLE [UnivLE.{u, m}]
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ).obj)
    (hF : HasFlatBaseChangePropertyUnivLE B E h S hS p hp τ hτ F) :
    HasSheafFlatBaseChangeProperty B E h S hS p hp τ hτ F := fun φ hφ =>
  have := hF φ hφ
  ⟨inferInstance, inferInstance⟩

/-- `AlgebraicGeometry.Stack.HasFlatBaseChangeProperty`, at module universe `u`, implies
**Stacks 0762**. -/
theorem hasSheafFlatBaseChangeProperty_of_hasFlatBaseChangeProperty
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj)
    (hF : HasFlatBaseChangeProperty B E h S hS p hp τ hτ F) :
    HasSheafFlatBaseChangeProperty B E h S hS p hp τ hτ F :=
  hasSheafFlatBaseChangeProperty_of_hasFlatBaseChangePropertyUnivLE B E h S hS p hp τ hτ F hF

/-- For an étale sheaf `F` the flat base change property of **Stacks 0762** says that, along
every arrow `φ` over a flat morphism, the comparison map becomes an isomorphism after étale
sheafification on the small site — equivalently, since its target `F|_{U_ét}` is already a sheaf,
that the map of sheaves `a_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` out of the sheafified inverse image is
an isomorphism. -/
theorem hasSheafFlatBaseChangeProperty_iff_isIso_presheafToSheaf [UnivLE.{u, m}]
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ).obj) :
    HasSheafFlatBaseChangeProperty B E h S hS p hp τ hτ F ↔
      ∀ {x y : 𝒳} (φ : x ⟶ y), Flat (B.inclusion.map (p.map φ).left) →
        haveI : EssentiallySmall.{m}
            (SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)) :=
          essentiallySmall_trans_univLE inferInstance
        haveI := hasSheafifyEssentiallySmallSite.{_, _, _, _, m}
          (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
          AddCommGrpCat.{m}
        IsIso ((presheafToSheaf
          (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
          AddCommGrpCat.{m}).map ((PresheafOfModules.toPresheaf _).map
            (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F))) := by
  refine forall_congr' fun x => forall_congr' fun y => forall_congr' fun φ =>
    imp_congr_right fun _ => ?_
  have : EssentiallySmall.{m}
      (SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)) :=
    essentiallySmall_trans_univLE inferInstance
  have := hasSheafifyEssentiallySmallSite.{_, _, _, _, m}
    (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x)) AddCommGrpCat.{m}
  have : (SmallEtale.topology E (p.obj x).left.1
      (contains_base B E h S hS p x)).WEqualsLocallyBijective AddCommGrpCat.{m} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, m} _
  rw [← GrothendieckTopology.W_iff, GrothendieckTopology.W_iff_isLocallyBijective]

/-- In a commutative square `a ≫ c' = c ≫ r` of presheaves whose sides `a` and `r` are
isomorphisms, `c'` is locally injective and locally surjective as soon as `c` is. -/
private theorem isLocallyBijective_of_fac {C : Type*} [Category C] (J : GrothendieckTopology C)
    {P₁ P₂ Q₁ Q₂ : Cᵒᵖ ⥤ AddCommGrpCat.{m}} {a : P₁ ⟶ P₂} {c' : P₂ ⟶ Q₂} {c : P₁ ⟶ Q₁}
    {r : Q₁ ⟶ Q₂} (hfac : a ≫ c' = c ≫ r) (ha : IsIso a) (hr : IsIso r)
    (h₁ : Presheaf.IsLocallyInjective J c) (h₂ : Presheaf.IsLocallySurjective J c) :
    Presheaf.IsLocallyInjective J c' ∧ Presheaf.IsLocallySurjective J c' := by
  rw [← Presheaf.comp_isLocallyInjective_iff J a c', ← Presheaf.comp_isLocallySurjective_iff J a c',
    hfac]
  exact ⟨inferInstance, inferInstance⟩

/-- The flat base change property of **Stacks 0762** transports along an isomorphism of
presheaves of modules. -/
theorem hasSheafFlatBaseChangeProperty_of_iso [UnivLE.{u, m}]
    {F F' : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ).obj} (e : F ≅ F')
    (hF : HasSheafFlatBaseChangeProperty B E h S hS p hp τ hτ F) :
    HasSheafFlatBaseChangeProperty B E h S hS p hp τ hτ F' := by
  intro x y φ hflat
  obtain ⟨h₁, h₂⟩ := hF φ hflat
  let T := PresheafOfModules.toPresheaf
    (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj
  let a := T.map
    ((PresheafOfModules.pullback.{m}
        (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).map
      ((restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp τ hτ y).map e.hom))
  let c := T.map (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F)
  let c' := T.map (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F')
  let r := T.map ((restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp τ hτ x).map
    e.hom)
  have hfac : a ≫ c' = c ≫ r := by
    simp only [a, c', c, r]
    exact congrArg T.map
      (restrictModulePullbackComparisonUnivLE_naturality B E h S hS p hp τ hτ φ e.hom)
  have hr : IsIso r := by
    dsimp only [r]
    infer_instance
  have ha : IsIso a := by
    dsimp only [a]
    infer_instance
  exact isLocallyBijective_of_fac _ hfac ha hr h₁ h₂

end Predicate

section Membership

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- **Membership in `LQCoh^fbc(𝒪_𝒳)`** (Stacks, Section 0GQG): a presheaf of modules over the
structure sheaf of a category fibred in groupoids, on its étale site, which is locally
quasi-coherent (**Stacks 06WJ**, which includes the étale sheaf condition) and has the flat base
change property of **Stacks 0762**. -/
abbrev IsLocallyQuasicoherentWithSheafFlatBaseChange [UnivLE.{u, m}]
    (F : PresheafOfModules.{m}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj) :
    Prop :=
  IsLocallyQuasicoherent B E h S hS p hp F ∧
    HasSheafFlatBaseChangeProperty B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) F

/-- The presheaf-level membership condition of the library implies membership in
`LQCoh^fbc(𝒪_𝒳)`. -/
theorem isLocallyQuasicoherentWithSheafFlatBaseChange_of_flatBaseChange
    (F : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : IsLocallyQuasicoherentWithFlatBaseChange B E h S hS p hp F) :
    IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS p hp F :=
  ⟨hF.1, hasSheafFlatBaseChangeProperty_of_hasFlatBaseChangeProperty B E h S hS p hp _ _ F hF.2⟩

end Membership

section Stack

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **`LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒳_ét, 𝒪_𝒳)`** (Stacks, Section 0GQG), at a module universe `t` above
the universe of the schemes: the étale sheaves of `𝒪_𝒳`-modules on an algebraic stack which are
locally quasi-coherent (**Stacks 06WJ**) and have the flat base change property
(**Stacks 0762**). -/
abbrev lqcohSheafFbcEtaleModules [UnivLE.{u, t}] :
    ObjectProperty (SheafOfModules.{t} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B))) :=
  fun F => IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids F.val

/-- **`LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`** (Stacks, Section 0GQG), at a module universe `t` above the
universe of the schemes: the fppf sheaves of `𝒪_𝒳`-modules on an algebraic stack whose underlying
presheaf, read on the étale site, is locally quasi-coherent (**Stacks 06WJ**) and has the flat
base change property (**Stacks 0762**).

The fppf and étale structure sheaves have the same underlying presheaf of rings
(`AlgebraicGeometry.Stack.fibredSite_ringStructureSheafCore_eq`), so no transport is involved. -/
abbrev lqcohSheafFbcFppfModules [UnivLE.{u, t}] :
    ObjectProperty (fppfModulesUnivLE.{u, w, t} B S hS 𝒳) :=
  fun F => IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids F.val

/-- The presheaf-level `LQCoh^fbc` of the library,
`AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE`, is contained in
`AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules`. -/
theorem locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE_le [UnivLE.{u, t}] :
    locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE.{u, w, t} B E h S hS 𝒳 ≤
      lqcohSheafFbcFppfModules.{u, w, t} B E h S hS 𝒳 := fun F hF =>
  ⟨hF.1, hasSheafFlatBaseChangeProperty_of_hasFlatBaseChangePropertyUnivLE B E h S hS _ _
    (etaleTopology B) (etaleTopology_le_topology B) F.val hF.2⟩

end Stack

section Rules

/-- **The rule of the flat base change property**, in the sense of **Stacks 076Z**: it assigns
to a category fibred in groupoids the modules on its étale site with the flat base change
property of **Stacks 0762**, at section universe `u + 1`. -/
noncomputable abbrev sheafFlatBaseChangePropertyRule : StackEtaleModuleRule B S hS :=
  fun {𝒳 : Type (u + 1)} [Category.{u} 𝒳] p hp F =>
    HasSheafFlatBaseChangeProperty B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) F

/-- **The rule `LQCoh^fbc`**, in the sense of **Stacks 076Z**: it assigns to a category fibred in
groupoids the modules on its étale site which are locally quasi-coherent (**Stacks 06WJ**) and
have the flat base change property of **Stacks 0762**, at section universe `u + 1`. -/
noncomputable abbrev locallyQuasicoherentSheafFlatBaseChangeRule : StackEtaleModuleRule B S hS :=
  fun {𝒳 : Type (u + 1)} [Category.{u} 𝒳] p hp F =>
    IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS p hp F

end Rules

end AlgebraicGeometry.Stack

end
