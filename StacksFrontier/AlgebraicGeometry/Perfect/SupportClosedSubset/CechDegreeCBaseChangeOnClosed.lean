module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinDifferentialCompatibility
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechDegreeCBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.PushforwardRestrictMate

/-!
# The first diagram of Stacks 0G7U on the closed subscheme

Let `g : X' ⟶ X` be a morphism of schemes, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` with `c = d + 1`, put
`f'ⱼ = g^♯(fⱼ)`, and let `Z ⊆ X`, `Z' ⊆ X'` be the closed subsets they cut out, made into ringed
spaces `(Z, i^{-1}𝒪_X)` and `(Z', (i')^{-1}𝒪_{X'})`; `h : Z' ⟶ Z` is the induced morphism.  For a
quasi-coherent `𝒪_X`-module `ℱ` with `ℱ' = g^*ℱ`, [Stacks, Tag 0G7U] asserts that the diagram

```
(i')^{-1}𝒪_{X'} ⊗_{h^{-1}i^{-1}𝒪_X} h^{-1}ℋ^c_Z(ℱ)  ---->  ℋ^c_{Z'}(ℱ')
              ^                                              ^
       c_{f₁,…,f_c}                                   c_{f'₁,…,f'_c}
              |                                              |
           h^*i^*ℱ             ------------------->      (i')^*ℱ'
```

of `(i')^{-1}𝒪_{X'}`-modules on `Z'` commutes, the top arrow being the map of Cohomology,
Remark 0G78 on cohomology sheaves in degree `c`.  This file proves it on `Z'` itself:
`Stacks.Perfect.CechDegreeCBaseChangeOnClosed.fractionClassOnClosed_baseChange`.  The left-hand
top corner is the inverse image `h^*ℋ^c_Z(ℱ)` of modules along the morphism of ringed spaces `h`,
which is `(i')^{-1}𝒪_{X'} ⊗_{h^{-1}i^{-1}𝒪_X} h^{-1}ℋ^c_Z(ℱ)` by definition.

## Main definitions

* `closedRestriction`: the morphism `h : Z' ⟶ Z` of ringed spaces.
* `bottomArrow`: the canonical `h^*i^*ℱ ⟶ (i')^*ℱ'`.
* `topArrow`: the top arrow `h^*ℋ^c_Z(ℱ) ⟶ ℋ^c_{Z'}(ℱ')`, the arrow on `Z'` that corresponds to the
  degree-`c` comparison `Stacks.Perfect.CechDegreeCBaseChange.degreeCBaseChange` on `X'`, which is
  the map of [Stacks, Tag 0G78] in degree `c` by
  `Stacks.Perfect.CechDegreeCBaseChange.degreeCBaseChange_eq_homology_zeroG78`.
* `transposeTop`: the abstract construction behind `topArrow`, for any commutative square of
  adjunctions with `i_*` fully faithful.

## Main results

* `comp_transposeTop`: a square read on `X'` through the transposes of its vertical arrows
  descends to `Z'`.
* `transposeTop_spec`, `transposeTop_unique`: `transposeTop D` is the unique arrow with that
  transport.
* `fractionClassOnClosed_baseChange`: **the first diagram of [Stacks, Tag 0G7U] on `Z'`.**

## Implementation notes

The vertical arrows are the components of
`Stacks.Perfect.GysinLocalCohomology.fractionClassOnClosed`, the map of [Stacks, Tag 0G7Q] on the
closed subset, whose source is the remark's presentation `i^*(ℱ/(f₁, …, f_c)ℱ)` of `i^*ℱ`.

The descent from `X'` to `Z'` is pure adjunction calculus: the comparison of iterated inverse
images `i^* ⋙ h^* ⟶ g^* ⋙ (i')^*` is conjugate to the comparison of iterated direct images
(`Stacks.Cohomology.conjugateEquiv_pullbackCompSquare`), so transposing along the two composite
adjunctions turns the square on `Z'` into the square on `X'`, which is
`Stacks.Perfect.CechDegreeCBaseChange.fractionClassTrans_baseChange`.  It is done once over
arbitrary categories (`comp_transposeTop`) and instantiated once.

`h` is `Stacks.Cohomology.SupportedComplexes.closedSubsetRestriction`, which is stated at the
preimage `g^{-1}(Z)`, transported to the zero locus of the `f'ⱼ` along
`Stacks.Perfect.SupportedDerivedBaseChange.equationsClosedSet_pullback`; that is what lets the
right-hand vertical arrow be the class map of [Stacks, Tag 0G7Q] for `f'` itself.

The inverse image along `g` is written `Scheme.Modules.pullback g` throughout, also in
`pullbackSquare` where the underlying comparison is stated for the inverse image along the
underlying morphism of ringed spaces; the two functors are equal by `rfl`, but leaving the
crossing to the unifier inside the instantiation of `comp_transposeTop` exhausts the default
heartbeat budget.

## References

* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G78](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Tag 0097](https://stacks.math.columbia.edu/tag/0097)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Perfect.CechDegreeCBaseChangeOnClosed

section Abstract

variable {MX MX' MZ MZ' : Type*} [Category MX] [Category MX'] [Category MZ] [Category MZ']
  {gs : MX ⥤ MX'} {gp : MX' ⥤ MX} (adjg : gs ⊣ gp)
  {is : MX ⥤ MZ} {ip : MZ ⥤ MX} (adji : is ⊣ ip)
  {js : MX' ⥤ MZ'} {jp : MZ' ⥤ MX'} (adjj : js ⊣ jp)
  {hs : MZ ⥤ MZ'} {hp : MZ' ⥤ MZ} (adjh : hs ⊣ hp)
  (ψ : is ⋙ hs ⟶ gs ⋙ js)

/-- The arrow `h^*H ⟶ H'` determined by an arrow `D : g^*(i_*H) ⟶ i'_*H'`, for a commutative
square of ringed spaces `i ∘ h = g ∘ i'` with `i_*` fully faithful.  It is the transpose of `D`
along `g^* ⊣ g_*`, carried by the conjugate `i'_* ⋙ g_* ⟶ h_* ⋙ i_*` of the comparison
`ψ : i^* ⋙ h^* ⟶ g^* ⋙ i'^*`, descended along `i_*` and transposed along `h^* ⊣ h_*`. -/
def transposeTop (hip : ip.FullyFaithful) {H : MZ} {H' : MZ'}
    (D : gs.obj (ip.obj H) ⟶ jp.obj H') : hs.obj H ⟶ H' :=
  (adjh.homEquiv _ _).symm (hip.preimage (adjg.homEquiv _ _ D ≫
    (conjugateEquiv (adjg.comp adjj) (adji.comp adjh) ψ).app H'))

/-- Transposing along a composite adjunction after the comparison `ψ` is transposing along the
other composite adjunction and then applying the conjugate of `ψ`. -/
theorem compHomEquiv_comp_conjugate {Q : MX} {H' : MZ'} (y : js.obj (gs.obj Q) ⟶ H') :
    (adji.comp adjh).homEquiv Q H' (ψ.app Q ≫ y) =
      (adjg.comp adjj).homEquiv Q H' y ≫
        (conjugateEquiv (adjg.comp adjj) (adji.comp adjh) ψ).app H' := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv (adjg.comp adjj) (adji.comp adjh) ψ Q, Category.assoc,
    Category.assoc]
  exact congrArg (fun t => (adjg.comp adjj).unit.app Q ≫ t)
    ((conjugateEquiv (adjg.comp adjj) (adji.comp adjh) ψ).naturality y).symm

/-- **A commutative square read through `i'_*` descends to `Z'`.**  Let `c : i^*Q ⟶ H` and
`c' : i'^*Q' ⟶ H'` be maps on `Z` and `Z'`, `e : g^*Q ⟶ Q'` a map on `X'` and
`D : g^*(i_*H) ⟶ i'_*H'`.  If the square on `X'` with vertical arrows the transposes of `c` and
`c'` commutes, `g^*(ĉ) ≫ D = e ≫ ĉ'`, then so does the square on `Z'`:
`h^*c ≫ transposeTop D = ψ_Q ≫ i'^*e ≫ c'`. -/
theorem comp_transposeTop (hip : ip.FullyFaithful)
    {Q : MX} {H : MZ} (c : is.obj Q ⟶ H) {Q' : MX'} {H' : MZ'} (c' : js.obj Q' ⟶ H')
    (e : gs.obj Q ⟶ Q') (D : gs.obj (ip.obj H) ⟶ jp.obj H')
    (hX : gs.map (adji.homEquiv _ _ c) ≫ D = e ≫ adjj.homEquiv _ _ c') :
    hs.map c ≫ transposeTop adjg adji adjj adjh ψ hip D = ψ.app Q ≫ js.map e ≫ c' := by
  apply ((adji.comp adjh).homEquiv Q H').injective
  rw [compHomEquiv_comp_conjugate, Adjunction.comp_homEquiv, Adjunction.comp_homEquiv,
    Equiv.trans_apply, Equiv.trans_apply, Adjunction.homEquiv_naturality_left, transposeTop,
    Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right, hip.map_preimage,
    Adjunction.homEquiv_naturality_left, ← hX, Adjunction.homEquiv_naturality_left,
    Category.assoc]

/-- `transposeTop D` is characterised by `D`: its transpose along `h^* ⊣ h_*`, read through
`i_*`, is the transpose of `D` along `g^* ⊣ g_*` followed by the conjugate of `ψ`; and by full
faithfulness of `i_*` and the two adjunctions, no other arrow `h^*H ⟶ H'` has this property. -/
theorem transposeTop_spec (hip : ip.FullyFaithful) {H : MZ} {H' : MZ'}
    (D : gs.obj (ip.obj H) ⟶ jp.obj H') :
    ip.map (adjh.homEquiv _ _ (transposeTop adjg adji adjj adjh ψ hip D)) =
      adjg.homEquiv _ _ D ≫ (conjugateEquiv (adjg.comp adjj) (adji.comp adjh) ψ).app H' := by
  rw [transposeTop, Equiv.apply_symm_apply, hip.map_preimage]

/-- The uniqueness half of `transposeTop_spec`. -/
theorem transposeTop_unique (hip : ip.FullyFaithful) {H : MZ} {H' : MZ'}
    (D : gs.obj (ip.obj H) ⟶ jp.obj H') (t : hs.obj H ⟶ H')
    (ht : ip.map (adjh.homEquiv _ _ t) =
      adjg.homEquiv _ _ D ≫ (conjugateEquiv (adjg.comp adjj) (adji.comp adjh) ψ).app H') :
    t = transposeTop adjg adji adjj adjh ψ hip D :=
  (adjh.homEquiv _ _).injective (hip.map_injective
    (ht.trans (transposeTop_spec adjg adji adjj adjh ψ hip D).symm))

end Abstract

section Concrete

attribute [local instance 10000] HasDerivedCategory.standard

-- Restated instances of
-- `StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDifferentialCompatibility.lean`, needed for
-- the cohomology functor on modules over a closed subset; see the implementation notes there.
attribute [local instance] Stacks.Perfect.GysinLocalCohomology.abelian_sheafOfModules_ringSheaf
  Stacks.Perfect.GysinLocalCohomology.additive_modulePushforward

open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet isClosed_equationsClosedSet)
open Stacks.Perfect.SupportedFraction (fractionClassTrans equationsQuotientFunctor)
open Stacks.Perfect.GysinLocalCohomology (fractionClassOnClosed fractionClassPushTrans
  supportCohomologySheafFunctorIso)
open Stacks.Perfect.CechDegreeCBaseChange (degreeCBaseChange equationsQuotientBaseChange
  fractionClassTrans_baseChange)

variable {X X' : Scheme.{u}} (g : X' ⟶ X) {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤)) (F : X.Modules)

/-- **The morphism `h : Z' ⟶ Z` of [Stacks, Tag 0G7U], as a morphism of ringed spaces
`(Z', (i')^{-1}𝒪_{X'}) ⟶ (Z, i^{-1}𝒪_X)`**, with `Z ⊆ X` the common zero locus of the `fⱼ` and
`Z' ⊆ X'` that of the `f'ⱼ = g^♯(fⱼ)`.  It is
`Stacks.Cohomology.SupportedComplexes.closedSubsetRestriction`, the restriction of `g` to the
preimage `g^{-1}(Z)`, read at the zero locus of the `f'ⱼ`, which is that preimage by
`Stacks.Perfect.SupportedDerivedBaseChange.equationsClosedSet_pullback`. -/
def closedRestriction :
    closedSubsetRingedSpace X'.toRingedSpace (equationsClosedSet (fun j => g.appTop (f j))) ⟶
      closedSubsetRingedSpace X.toRingedSpace (equationsClosedSet f) :=
  (Stacks.Perfect.SupportedDerivedBaseChange.equationsClosedSet_pullback g f).symm ▸
    closedSubsetRestriction g.toLRSHom.toShHom (equationsClosedSet f)

/-- The square `h ≫ i = i' ≫ g` of [Stacks, Tag 0G7U], as morphisms of ringed spaces. -/
theorem closedRestriction_comp :
    closedSubsetInclusion X'.toRingedSpace (equationsClosedSet (fun j => g.appTop (f j))) ≫
        g.toLRSHom.toShHom =
      closedRestriction g f ≫ closedSubsetInclusion X.toRingedSpace (equationsClosedSet f) := by
  have key : ∀ (T : Set X'.carrier)
      (hT : closedSubsetPreimage g.toLRSHom.toShHom (equationsClosedSet f) = T),
      closedSubsetInclusion X'.toRingedSpace T ≫ g.toLRSHom.toShHom =
        (hT ▸ closedSubsetRestriction g.toLRSHom.toShHom (equationsClosedSet f)) ≫
          closedSubsetInclusion X.toRingedSpace (equationsClosedSet f) := by
    intro T hT
    subst hT
    exact (closedSubsetRestriction_comp_closedSubsetInclusion _ _).symm
  exact key _ _

/-- The comparison `i^* ⋙ h^* ≅ g^* ⋙ (i')^*` of the two iterated inverse images around the square
`h ≫ i = i' ≫ g`: pseudofunctoriality of inverse images, [Stacks, Tag 0097] part (2). -/
def pullbackSquare :
    modulePullback (closedSubsetInclusion X.toRingedSpace (equationsClosedSet f)) ⋙
        modulePullback (closedRestriction g f) ⟶
      Scheme.Modules.pullback g ⋙
        modulePullback (closedSubsetInclusion X'.toRingedSpace
          (equationsClosedSet (fun j => g.appTop (f j)))) :=
  (Stacks.Cohomology.pullbackCompSquare g.toLRSHom.toShHom
    (closedSubsetInclusion X'.toRingedSpace (equationsClosedSet (fun j => g.appTop (f j))))
    (closedSubsetInclusion X.toRingedSpace (equationsClosedSet f)) (closedRestriction g f)
    (closedRestriction_comp g f))

/-- **The bottom arrow of the first diagram of [Stacks, Tag 0G7U]**, `h^*i^*ℱ ⟶ (i')^*ℱ'`, on the
presentations `i^*(ℱ/(f₁, …, f_c)ℱ)` and `(i')^*(ℱ'/(f'₁, …, f'_c)ℱ')` of [Stacks, Tag 0G7Q]: the
comparison of the iterated inverse images followed by `(i')^*` of the comparison of the two
quotients. -/
def bottomArrow :
    (modulePullback (closedRestriction g f)).obj
        ((modulePullback (closedSubsetInclusion X.toRingedSpace (equationsClosedSet f))).obj
          ((equationsQuotientFunctor f).obj F)) ⟶
      (modulePullback (closedSubsetInclusion X'.toRingedSpace
          (equationsClosedSet (fun j => g.appTop (f j))))).obj
        ((equationsQuotientFunctor (fun j => g.appTop (f j))).obj
          ((Scheme.Modules.pullback g).obj F)) :=
  (pullbackSquare g f).app _ ≫
    (modulePullback (closedSubsetInclusion X'.toRingedSpace
      (equationsClosedSet (fun j => g.appTop (f j))))).map (equationsQuotientBaseChange g f F)

/-- The degree-`c` comparison `degreeCBaseChange` with its source and target spelled with the
cohomology sheaf on the closed subset taken first, `g^*(i_*ℋ^c_Z(ℱ)) ⟶ i'_*ℋ^c_{Z'}(ℱ')`. -/
def degreeCBaseChangePush [F.IsQuasicoherent] :
    (Scheme.Modules.pullback g).obj
        ((Stacks.Perfect.GysinLocalCohomology.localCohomologyPushforwardFunctor
          (isClosed_equationsClosedSet f) ((d + 1 : ℕ) : ℤ)).obj F) ⟶
      (Stacks.Perfect.GysinLocalCohomology.localCohomologyPushforwardFunctor
          (isClosed_equationsClosedSet (fun j => g.appTop (f j))) ((d + 1 : ℕ) : ℤ)).obj
        ((Scheme.Modules.pullback g).obj F) :=
  (Scheme.Modules.pullback g).map
      ((supportCohomologySheafFunctorIso (isClosed_equationsClosedSet f)
        ((d + 1 : ℕ) : ℤ)).inv.app F) ≫
    degreeCBaseChange g f F ≫
      (supportCohomologySheafFunctorIso (isClosed_equationsClosedSet (fun j => g.appTop (f j)))
        ((d + 1 : ℕ) : ℤ)).hom.app ((Scheme.Modules.pullback g).obj F)

/-- **The top arrow of the first diagram of [Stacks, Tag 0G7U]**,
`(i')^{-1}𝒪_{X'} ⊗_{h^{-1}i^{-1}𝒪_X} h^{-1}ℋ^c_Z(ℱ) = h^*ℋ^c_Z(ℱ) ⟶ ℋ^c_{Z'}(ℱ')`, on `Z'`: the
arrow whose image under the fully faithful `i'_*`-reading is the degree-`c` comparison
`degreeCBaseChange`, which is the map of [Stacks, Tag 0G78] on cohomology sheaves in degree `c` by
`Stacks.Perfect.CechDegreeCBaseChange.degreeCBaseChange_eq_homology_zeroG78`.  Explicitly it is
the transpose of `degreeCBaseChangePush` along `g^* ⊣ g_*`, carried along `g_*i'_* = i_*h_*`,
descended along the fully faithful `i_*` ([Stacks, Tag 08KS]) and transposed along
`h^* ⊣ h_*`. -/
def topArrow [F.IsQuasicoherent] :
    (modulePullback (closedRestriction g f)).obj
        ((DerivedCategory.singleFunctor X.Modules 0 ⋙
          derivedSupportedSectionsOnClosed X.toRingedSpace (equationsClosedSet f)
            (isClosed_equationsClosedSet f) ⋙
          DerivedCategory.homologyFunctor _ ((d + 1 : ℕ) : ℤ)).obj F) ⟶
      (DerivedCategory.singleFunctor X'.Modules 0 ⋙
          derivedSupportedSectionsOnClosed X'.toRingedSpace
            (equationsClosedSet (fun j => g.appTop (f j)))
            (isClosed_equationsClosedSet (fun j => g.appTop (f j))) ⋙
          DerivedCategory.homologyFunctor _ ((d + 1 : ℕ) : ℤ)).obj
        ((Scheme.Modules.pullback g).obj F) :=
  transposeTop (Scheme.Modules.pullbackPushforwardAdjunction g)
    (modulePullbackPushforwardAdjunction
      (closedSubsetInclusion X.toRingedSpace (equationsClosedSet f)))
    (modulePullbackPushforwardAdjunction (closedSubsetInclusion X'.toRingedSpace
      (equationsClosedSet (fun j => g.appTop (f j)))))
    (modulePullbackPushforwardAdjunction (closedRestriction g f)) (pullbackSquare g f)
    (Stacks.SheafOfModules.SupportedSections.fullyFaithfulModulePushforwardClosedSubset
      X.toRingedSpace (equationsClosedSet f) (isClosed_equationsClosedSet f))
    (degreeCBaseChangePush g f F)

/-- The transpose along `i^* ⊣ i_*` of the map `c_{f₁,…,f_c}` of [Stacks, Tag 0G7Q] on `Z` is the
transformation on `X` it was descended from. -/
theorem homEquiv_fractionClassOnClosed (e : Fin (d + 1) → Γ(X, ⊤)) :
    (modulePullbackPushforwardAdjunction
        (closedSubsetInclusion X.toRingedSpace (equationsClosedSet e))).homEquiv _ _
        ((fractionClassOnClosed e).app F) =
      (fractionClassPushTrans e).app F :=
  ((modulePullbackPushforwardAdjunction
    (closedSubsetInclusion X.toRingedSpace (equationsClosedSet e))).homEquiv _ _).apply_symm_apply _

/-- The square on `X'` behind the first diagram of [Stacks, Tag 0G7U], with the class maps of
[Stacks, Tag 0G7Q] spelled with the cohomology sheaf on the closed subset taken first. -/
theorem fractionClassPushTrans_baseChange [F.IsQuasicoherent] :
    (Scheme.Modules.pullback g).map ((fractionClassPushTrans f).app F) ≫
        degreeCBaseChangePush g f F =
      equationsQuotientBaseChange g f F ≫
        (fractionClassPushTrans (fun j => g.appTop (f j))).app
          ((Scheme.Modules.pullback g).obj F) := by
  have glue : ∀ {W₀ W₁ W₂ W₃ W₄ W₅ : X'.Modules} (a : W₀ ⟶ W₁) (b : W₁ ⟶ W₂) (b' : W₂ ⟶ W₁)
      (c : W₁ ⟶ W₃) (k : W₃ ⟶ W₄) (e : W₀ ⟶ W₅) (c' : W₅ ⟶ W₃),
      b ≫ b' = 𝟙 _ → a ≫ c = e ≫ c' → (a ≫ b) ≫ b' ≫ c ≫ k = e ≫ c' ≫ k := by
    intro W₀ W₁ W₂ W₃ W₄ W₅ a b b' c k e c' h₁ h₂
    rw [Category.assoc, ← Category.assoc b, h₁, Category.id_comp, ← Category.assoc, h₂,
      Category.assoc]
  exact Eq.trans (congrArg (fun t => t ≫ degreeCBaseChangePush g f F)
      ((Scheme.Modules.pullback g).map_comp _ _))
    (glue _ _ _ _ _ _ _
      (((Scheme.Modules.pullback g).map_comp _ _).symm.trans
        ((congrArg (Scheme.Modules.pullback g).map
          ((supportCohomologySheafFunctorIso (isClosed_equationsClosedSet f)
            ((d + 1 : ℕ) : ℤ)).hom_inv_id_app F)).trans
          ((Scheme.Modules.pullback g).map_id _)))
      (fractionClassTrans_baseChange g f F))

/-- **[Stacks, Tag 0G7U], the first diagram, on the closed subscheme `Z'`.**  Let `g : X' ⟶ X` be
a morphism of schemes, `f₁, …, f_c ∈ Γ(X, 𝒪_X)`, `f'ⱼ = g^♯(fⱼ)`, `Z ⊆ X` and `Z' ⊆ X'` the
closed subsets cut out by them, made into ringed spaces `(Z, i^{-1}𝒪_X)` and
`(Z', (i')^{-1}𝒪_{X'})`, and `h : Z' ⟶ Z` the induced morphism (`closedRestriction`).  For a
quasi-coherent `𝒪_X`-module `ℱ`, with `ℱ' = g^*ℱ`, the diagram

```
h^*ℋ^c_Z(ℱ)   --topArrow-->   ℋ^c_{Z'}(ℱ')
     ^                              ^
h^*c_{f₁,…,f_c}               c_{f'₁,…,f'_c}
     |                              |
h^*i^*ℱ      --bottomArrow-->   (i')^*ℱ'
```

commutes.  Here `c_{f₁,…,f_c}` and `c_{f'₁,…,f'_c}` are the components at `ℱ` and at `ℱ'` of
`Stacks.Perfect.GysinLocalCohomology.fractionClassOnClosed`, the map of [Stacks, Tag 0G7Q] on the
closed subset, with source the remark's presentation `i^*(ℱ/(f₁, …, f_c)ℱ)` of `i^*ℱ`; the
left-hand top corner is `h^*ℋ^c_Z(ℱ) = (i')^{-1}𝒪_{X'} ⊗_{h^{-1}i^{-1}𝒪_X} h^{-1}ℋ^c_Z(ℱ)`, the
inverse image of modules along the morphism of ringed spaces `h`; the bottom arrow is the
canonical comparison `h^*i^*ℱ ≅ (i')^*g^*ℱ = (i')^*ℱ'`; and the top arrow is the one determined by
the degree-`c` comparison `degreeCBaseChange`, which is the map of Cohomology, Remark 0G78 on
cohomology sheaves in degree `c`
(`Stacks.Perfect.CechDegreeCBaseChange.degreeCBaseChange_eq_homology_zeroG78`).

The proof is the remark's: the diagram read on `X'` is
`Stacks.Perfect.CechDegreeCBaseChange.fractionClassTrans_baseChange`, and `comp_transposeTop`
descends it to `Z'`, the comparison of inverse images being conjugate to the comparison of direct
images by `Stacks.Cohomology.conjugateEquiv_pullbackCompSquare`. -/
@[stacks 0G7U "the first diagram of the remark on the closed subscheme Z', for quasi-coherent F: \
  h^*c_{f_1,...,f_c} followed by the top arrow h^*H^c_Z(F) -> H^c_{Z'}(F') equals the canonical \
  h^*i^*F -> (i')^*F' followed by c_{f'_1,...,f'_c}, with c the Tag 0G7Q map on the closed subset"]
theorem fractionClassOnClosed_baseChange [F.IsQuasicoherent] :
    (modulePullback (closedRestriction g f)).map ((fractionClassOnClosed f).app F) ≫
        topArrow g f F =
      bottomArrow g f F ≫
        (fractionClassOnClosed (fun j => g.appTop (f j))).app
          ((Scheme.Modules.pullback g).obj F) := by
  have hX := fractionClassPushTrans_baseChange g f F
  rw [← homEquiv_fractionClassOnClosed, ← homEquiv_fractionClassOnClosed] at hX
  have h1 := comp_transposeTop (Scheme.Modules.pullbackPushforwardAdjunction g)
    (modulePullbackPushforwardAdjunction
      (closedSubsetInclusion X.toRingedSpace (equationsClosedSet f)))
    (modulePullbackPushforwardAdjunction (closedSubsetInclusion X'.toRingedSpace
      (equationsClosedSet (fun j => g.appTop (f j)))))
    (modulePullbackPushforwardAdjunction (closedRestriction g f)) (pullbackSquare g f)
    (Stacks.SheafOfModules.SupportedSections.fullyFaithfulModulePushforwardClosedSubset
      X.toRingedSpace (equationsClosedSet f) (isClosed_equationsClosedSet f))
    ((fractionClassOnClosed f).app F)
    ((fractionClassOnClosed (fun j => g.appTop (f j))).app ((Scheme.Modules.pullback g).obj F))
    (equationsQuotientBaseChange g f F) (degreeCBaseChangePush g f F) hX
  -- The two sides are those of `h1` up to unfolding `topArrow` and `bottomArrow`; that is checked
  -- by `rfl` against the goal, which is immediate, while `exact` against the goal is not.
  refine Eq.trans ?_ (h1.trans (Category.assoc _ _ _).symm)
  rfl

end Concrete

end Stacks.Perfect.CechDegreeCBaseChangeOnClosed

end
