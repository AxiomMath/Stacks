module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullbackCycles.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardCoherent.StalkProduct
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ResidueTrdeg
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.FiniteFibreVanishing
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.RightDerivedPlus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionDominant
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.FunctionFieldDegree
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.Reflexive.ExtensionChain.StalkCriterion
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.ProperPushforwardUnconditional
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.RelativeFrobeniusDegree
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Components

/-!
# Intersection numbers and pullback along a morphism of proper schemes

Let `k` be a field, let `f : Y ⟶ X` be a morphism of schemes proper over `k`, let `Z ⊂ Y` be an
integral closed subscheme of dimension `d` and let `𝓛_1, …, 𝓛_d` be invertible `𝒪_X`-modules.
[Stacks, Tag 0BET] computes the intersection number of the pullbacks against `Z` in terms of the
intersection number against the scheme-theoretic image `f(Z)`:

`(f^*𝓛_1 ⋯ f^*𝓛_d · Z) = deg(f|_Z : Z → f(Z)) (𝓛_1 ⋯ 𝓛_d · f(Z))`

when `dim f(Z) = d`, and `(f^*𝓛_1 ⋯ f^*𝓛_d · Z) = 0` when `dim f(Z) < d`.

## Main results

* `AlgebraicGeometry.intersectionNumber_pullback_eq_degreeOver_mul`: **[Stacks, Tag 0BET]**, the
  equal-dimensional case.
* `AlgebraicGeometry.intersectionNumber_pullback_eq_zero`: **[Stacks, Tag 0BET]**, the vanishing
  case `dim f(Z) < d`.

## Implementation notes

**The route.** Write `g = Z ⟶ Y ⟶ X` for the composite, `T = g(Z)` for its scheme-theoretic
image with its integral structure, `h : Z ⟶ T` for the induced proper dominant morphism and
`ι : T ⟶ X` for the closed immersion.  The intersection number on the left is the `d`-fold mixed
finite difference of `χ(Z, ⨂_j (g^*𝓛_j)^{⊗ n_j})`; [Stacks, Tag 0BEK] expands that Euler
characteristic as the alternating sum of `χ(T, R^q h_*(⨂_j (h^*ι^*𝓛_j)^{⊗ n_j}))`, and the
projection formula for the higher direct images ([Stacks, Tag 01E8], available here as
`Stacks.ProjectionFormula.higherDirectImageTwistedSheafIso`) rewrites those as
`χ(T, (R^q h_*𝒪_Z) ⊗ ⨂_j (ι^*𝓛_j)^{⊗ n_j})`, which is `χ(X, (ι_*R^q h_*𝒪_Z) ⊗ ⨂_j 𝓛_j^{⊗ n_j})`
by [Stacks, Tag 089W].  Each of those is interpolated by the numerical polynomial of
[Stacks, Tag 0BEM], of total degree at most the dimension of the support, so the mixed difference
is the coefficient of `n_1 ⋯ n_d` in that polynomial.

**Which terms survive.**  The support of `ι_*R^q h_*𝒪_Z` is contained in `T`.  If `dim T < d`
every term has a polynomial of total degree `< d`, whose coefficient of `n_1 ⋯ n_d` vanishes:
that is the second conclusion.  If `dim T = d` then the generic fibre of `h` is the single
generic point of `Z` — this is the dimension-theoretic step of the source, proved here as
`AlgebraicGeometry.eq_genericPoint_of_map_eq_genericPoint_of_dim_eq` — so `R^q h_*𝒪_Z` has
vanishing stalk at the generic point of `T` for `q > 0` by [Stacks, Tag 02OE], its support is a
proper closed subset of `T` and again the coefficient vanishes.  Only `q = 0` contributes, and
there [Stacks, Tag 0BEN] identifies the coefficient as the multiplicity of `g_*𝒪_Z` at the generic
point of `T` times the coefficient for `𝒪_T`, which is `(𝓛_1 ⋯ 𝓛_d · f(Z))`.

**The degree.**  That multiplicity is the length of the stalk of `g_*𝒪_Z` at the generic point
of `T`; the generic fibre being a single point, the stalk is the function field of `Z`, and its
length over the local ring of `X` is the residue degree of `g` there, which is
`AlgebraicGeometry.degreeOver h = [R(Z) : R(T)]`, the degree of
[Stacks, Morphisms, Definition 02NY], by
`AlgebraicGeometry.residueDegree_genericPoint_eq_degreeOver`.

## References

* [Stacks Project, Tag 0BET](https://stacks.math.columbia.edu/tag/0BET)
* [Stacks Project, Tag 0BEP](https://stacks.math.columbia.edu/tag/0BEP)
* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
* [Stacks Project, Tag 0BEN](https://stacks.math.columbia.edu/tag/0BEN)
* [Stacks Project, Tag 0BEK](https://stacks.math.columbia.edu/tag/0BEK)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 02OE](https://stacks.math.columbia.edu/tag/02OE)
* [Stacks Project, Tag 02NY](https://stacks.math.columbia.edu/tag/02NY)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance] twistedSheaf_isCoherent isCoherent_pushforward_of_isClosedImmersion
  Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent


/-! ### The generic fibre of a proper morphism which does not drop the dimension -/

/-- **A proper morphism of integral schemes of the same dimension has a one-point generic
fibre.** If `h : Z ⟶ T` is closed and `Z` and `T` are integral of the same finite dimension `d`,
then the only point of `Z` above the generic point of `T` is the generic point of `Z`.

Indeed a chain of irreducible closed subsets of `T` lifts to a chain of specializations of any
point `z` above the generic point of `T`, so the closure of `z` has height at least `d`; if `z`
were not the generic point its closure would not be maximal, hence would have positive coheight,
and the dimension of `Z` would exceed `d`. -/
public theorem eq_genericPoint_of_map_eq_genericPoint_of_dim_eq {Z T : Scheme.{u}} (h : Z ⟶ T)
    [IsIntegral Z] [IsIntegral T] (hcl : IsClosedMap (ConcreteCategory.hom h.base)) {d : ℕ}
    (hZ : topologicalKrullDim Z = (d : WithBot ℕ∞))
    (hT : topologicalKrullDim T = (d : WithBot ℕ∞))
    {z : Z} (hz : h.base z = genericPoint T) : z = genericPoint Z := by
  by_contra hne
  have : IrreducibleSpace Z := irreducibleSpace_of_isIntegral Z
  set Q : IrreducibleCloseds Z := IrreducibleCloseds.closureSingleton z with hQdef
  have hQne : (Q : Set Z) ≠ Set.univ := fun hfull =>
    hne ((show IsGenericPoint z (Set.univ : Set Z) from hfull).eq
      (Set.top_eq_univ (α := Z) ▸ genericPoint_spec Z))
  have hnotmax : ¬ IsMax Q := by
    intro hmax
    refine hQne (Set.eq_univ_of_univ_subset ?_)
    exact (hmax (Set.subset_univ _) : (⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z,
      isClosed_univ⟩ : IrreducibleCloseds Z) ≤ Q)
  have hheight : topologicalKrullDim T ≤ (Order.height Q : WithBot ℕ∞) :=
    Topology.topologicalKrullDim_le_height_closureSingleton_of_specializingMap
      (fun x : Z => h.base x) h.continuous hcl.specializingMap
      (Set.top_eq_univ (α := T) ▸ genericPoint_spec T) hz
  have hco : (1 : ℕ∞) ≤ Order.coheight Q :=
    Order.one_le_iff_ne_zero.mpr (Order.coheight_ne_zero.mpr hnotmax)
  have hsum : (Order.height Q : WithBot ℕ∞) + (Order.coheight Q : WithBot ℕ∞) ≤
      topologicalKrullDim Z := by
    have _ : Nonempty (IrreducibleCloseds Z) := ⟨Q⟩
    show _ ≤ Order.krullDim (IrreducibleCloseds Z)
    rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact WithBot.coe_mono
      (le_iSup (fun W : IrreducibleCloseds Z => Order.height W + Order.coheight W) Q)
  rw [hT] at hheight
  rw [hZ] at hsum
  have hheight' : (d : ℕ∞) ≤ Order.height Q := WithBot.coe_le_coe.mp hheight
  have hsum' : Order.height Q + Order.coheight Q ≤ (d : ℕ∞) := by
    rw [← WithBot.coe_add] at hsum
    exact WithBot.coe_le_coe.mp hsum
  have hfinal : ((d : ℕ∞) + 1) ≤ (d : ℕ∞) :=
    le_trans (add_le_add hheight' hco) hsum'
  have hd : d + 1 ≤ d := by exact_mod_cast hfinal
  omega

/-! ### The degree as the multiplicity of the direct image of the structure sheaf -/

/-- **The structure sheaf is supported everywhere**: its stalk at a point is the local ring
there, which is not the zero ring. -/
private theorem supp_unitModule (Z : Scheme.{u}) :
    _root_.SheafOfModules.supp (Stacks.Ample.unitModule Z) = Set.univ :=
  Set.eq_univ_of_forall fun x =>
    (_root_.SheafOfModules.mem_supp_iff_nontrivial_stalk _ x).mpr
      (Stacks.Ample.unitStalkEquiv Z x).symm.injective.nontrivial

/-- **The structure sheaf of an integral scheme has multiplicity one at the generic point**: the
local ring there is a field, hence a simple module over itself. -/
@[ega "IV 3.2.1" "a) ⇒ c)"]
private theorem length_unitModule_stalk_genericPoint (Z : Scheme.{u}) [IsIntegral Z] :
    (Module.length (Z.presheaf.stalk (genericPoint Z))
      ((Stacks.Ample.unitModule Z).presheaf.stalk (genericPoint Z))).toNat = 1 := by
  let : Field (Z.presheaf.stalk (genericPoint Z)) := inferInstanceAs (Field Z.functionField)
  rw [(Stacks.Ample.unitStalkEquiv Z (genericPoint Z)).length_eq,
    Module.length_eq_one_iff.2 (inferInstance : IsSimpleModule _ _)]
  rfl

/-- The underlying space of a module supported everywhere is the scheme itself. -/
private def suppUnitHomeomorph (Z : Scheme.{u}) :
    ↥(_root_.SheafOfModules.supp (Stacks.Ample.unitModule Z)) ≃ₜ Z :=
  (Homeomorph.setCongr (supp_unitModule Z)).trans (Homeomorph.Set.univ Z)

/-- **Every point of the fibre of the support of `𝒪_Z` over the image of the generic point is the
generic point of a component of the support**, when that fibre is a single point. -/
private theorem exists_component_isGenericPoint_fibre_unitModule {Z X : Scheme.{u}} (g : Z ⟶ X)
    [IsIntegral Z] (hfib : ∀ z : Z, g.base z = g.base (genericPoint Z) → z = genericPoint Z) :
    ∀ z : ↥{z : Z | g.base z = g.base (genericPoint Z) ∧
        z ∈ _root_.SheafOfModules.supp (Stacks.Ample.unitModule Z)},
      ∃ W : irreducibleComponents
        (_root_.SheafOfModules.supp (Stacks.Ample.unitModule Z) : Set Z),
      IsGenericPoint z.1 (Subtype.val '' W.1 : Set Z) := by
  have hsupp : _root_.SheafOfModules.supp (Stacks.Ample.unitModule Z) = Set.univ :=
    supp_unitModule Z
  have hirr : IrreducibleSpace ↥(_root_.SheafOfModules.supp (Stacks.Ample.unitModule Z)) :=
    (suppUnitHomeomorph Z).symm.surjective.irreducibleSpace
      (suppUnitHomeomorph Z).symm.continuous
  have hcomp : (Set.univ : Set ↥(_root_.SheafOfModules.supp (Stacks.Ample.unitModule Z))) ∈
      irreducibleComponents ↥(_root_.SheafOfModules.supp (Stacks.Ample.unitModule Z)) := by
    rw [irreducibleComponents_eq_singleton]
    rfl
  intro z
  refine ⟨⟨Set.univ, hcomp⟩, ?_⟩
  have hz : z.1 = genericPoint Z := hfib z.1 z.2.1
  have himg : (Subtype.val ''
      (Set.univ : Set ↥(_root_.SheafOfModules.supp (Stacks.Ample.unitModule Z))) : Set Z) =
      Set.univ := by
    rw [Subtype.coe_image_univ]
    exact hsupp
  rw [hz, himg]
  exact Set.top_eq_univ (α := Z) ▸ genericPoint_spec Z

/-- **The multiplicity of `g_*𝒪_Z` at the image of the generic point, when that point is the
only point of the fibre.** The stalk of `g_*𝒪_Z` there is the stalk of `𝒪_Z` at the generic
point, by the product decomposition of [Stacks, Tag 02R6] along the fibre of the support, and
the length of that stalk over the local ring downstairs is its length upstairs — namely one —
times the residue degree of `g`. -/
private theorem sheafMultiplicity_pushforward_unitModule {Z X : Scheme.{u}} (g : Z ⟶ X)
    [IsProper g] [IsIntegral Z] [IsLocallyNoetherian Z]
    (hfib : ∀ z : Z, g.base z = g.base (genericPoint Z) → z = genericPoint Z) :
    Stacks.Chow.sheafMultiplicity ((Scheme.Modules.pushforward g).obj
        (Stacks.Ample.unitModule Z)) (g.base (genericPoint Z)) =
      g.residueDegree (genericPoint Z) := by
  classical
  have hsupp : _root_.SheafOfModules.supp (Stacks.Ample.unitModule Z) = Set.univ :=
    supp_unitModule Z
  have hηmem : genericPoint Z ∈ _root_.SheafOfModules.supp (Stacks.Ample.unitModule Z) := by
    rw [hsupp]; trivial
  let : Unique ↥{z : Z | g.base z = g.base (genericPoint Z) ∧
      z ∈ _root_.SheafOfModules.supp (Stacks.Ample.unitModule Z)} :=
    { default := ⟨genericPoint Z, rfl, hηmem⟩
      uniq := fun z => Subtype.ext (hfib z.1 z.2.1) }
  let : Fintype ↥{z : Z | g.base z = g.base (genericPoint Z) ∧
      z ∈ _root_.SheafOfModules.supp (Stacks.Ample.unitModule Z)} :=
    Fintype.ofSubsingleton ⟨genericPoint Z, rfl, hηmem⟩
  let : ∀ z : ↥{z : Z | g.base z = g.base (genericPoint Z) ∧
        z ∈ _root_.SheafOfModules.supp (Stacks.Ample.unitModule Z)},
      Module (X.presheaf.stalk (g.base (genericPoint Z)))
        ((Stacks.Ample.unitModule Z).presheaf.stalk z.1) :=
    Stacks.Chow.supportFibreStalkModule g (Stacks.Ample.unitModule Z)
      (g.base (genericPoint Z))
  let : Module (X.presheaf.stalk (g.base (genericPoint Z)))
      ((Stacks.Ample.unitModule Z).presheaf.stalk (genericPoint Z)) :=
    Module.compHom _ (g.stalkMap (genericPoint Z)).hom
  -- the support is the whole irreducible space, so its only component is everything
  have hgen := exists_component_isGenericPoint_fibre_unitModule g hfib
  -- the stalk of the direct image is the stalk at the generic point upstairs
  have hA : Module.length (X.presheaf.stalk (g.base (genericPoint Z)))
      (((Scheme.Modules.pushforward g).obj (Stacks.Ample.unitModule Z)).presheaf.stalk
        (g.base (genericPoint Z))) =
      Module.length (X.presheaf.stalk (g.base (genericPoint Z)))
        ((Stacks.Ample.unitModule Z).presheaf.stalk (genericPoint Z)) := by
    refine (Stacks.Chow.pushforwardStalkLinearEquivPi g (Stacks.Ample.unitModule Z)
      (_root_.SheafOfModules.isClosed_supp _) (g.base (genericPoint Z))
      (Stacks.Chow.locallyFinite_irreducibleComponents_supp _) hgen).length_eq.trans ?_
    rw [Module.length_pi_of_fintype, Finset.univ_unique, Finset.sum_singleton]
    rfl
  have hB := Stacks.Chow.length_stalk_restrictScalars_toNat g (Stacks.Ample.unitModule Z)
    (genericPoint Z)
  have hfin : (Module.length (X.presheaf.stalk (g.base (genericPoint Z)))
      (((Scheme.Modules.pushforward g).obj (Stacks.Ample.unitModule Z)).presheaf.stalk
        (g.base (genericPoint Z)))).toNat = g.residueDegree (genericPoint Z) := by
    rw [hA, hB, length_unitModule_stalk_genericPoint Z, one_mul]
  show ((Module.length (X.presheaf.stalk (g.base (genericPoint Z)))
      (((Scheme.Modules.pushforward g).obj (Stacks.Ample.unitModule Z)).presheaf.stalk
        (g.base (genericPoint Z)))).toNat : ℤ) = (g.residueDegree (genericPoint Z) : ℤ)
  exact_mod_cast hfin

/-! ### Twists along isomorphic families of invertible modules -/

open Stacks.SheafOfModules.Invertible in
/-- **Isomorphic families of invertible modules give isomorphic twists**, at nonnegative
exponents: the fold of `AlgebraicGeometry.twistList` is carried along factor by factor, the
factors being compared by `Stacks.SheafOfModules.Invertible.tensorPowerCongr`. -/
private def twistListFamilyIso {X : Scheme.{u}} {r : ℕ} (L M : Fin r → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M j)]
    (e : ∀ j, L j ≅ M j) (m : Fin r → ℕ) (l : List (Fin r)) :
    ∀ {F G : X.Modules}, (F ≅ G) →
      (twistList L (fun j => (m j : ℤ)) l F ≅ twistList M (fun j => (m j : ℤ)) l G) := by
  induction l with
  | nil => exact fun ε => ε
  | cons j t ih =>
    exact fun ε => ih (tensorProductIso X.presheaf X.ringCatSheaf.2 ε
      (tensorPowerCongr X.presheaf X.ringCatSheaf.2 (L j) (M j) (e j) (m j)))

/-- **Isomorphic families of invertible modules give isomorphic twisted sheaves**, at
nonnegative exponents. -/
private def twistedSheafFamilyIso {X : Scheme.{u}} {r : ℕ} (L M : Fin r → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M j)]
    (e : ∀ j, L j ≅ M j) (m : Fin r → ℕ) {F G : X.Modules} (ε : F ≅ G) :
    twistedSheaf F L (fun j => (m j : ℤ)) ≅ twistedSheaf G M (fun j => (m j : ℤ)) :=
  twistListFamilyIso L M e m (List.finRange r) ε

/-! ### The numerical polynomial of Tag 0BEM, as a function of the module -/

/-- The coefficient of the squarefree monomial `n_1 ⋯ n_d` in a rational polynomial. -/
private def mixedCoeff {d : ℕ} (P : MvPolynomial (Fin d) ℚ) : ℚ :=
  P.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1)

/-- The coefficient of `n_1 ⋯ n_d` in a polynomial of total degree less than `d` vanishes. -/
private theorem mixedCoeff_eq_zero_of_totalDegree_lt {d : ℕ} (P : MvPolynomial (Fin d) ℚ)
    (hP : P.totalDegree < d) : mixedCoeff P = 0 := by
  have hsupp : (Finsupp.equivFunOnFinite.symm (fun _ : Fin d => 1) : Fin d →₀ ℕ).support =
      Finset.univ := by
    ext j
    simp
  have hval : ∀ j : Fin d,
      (Finsupp.equivFunOnFinite.symm (fun _ : Fin d => 1) : Fin d →₀ ℕ) j = 1 := fun _ => rfl
  simp only [mixedCoeff]
  refine MvPolynomial.coeff_eq_zero_of_totalDegree_lt ?_
  rw [hsupp]
  simp only [hval, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  exact hP

/-- The coefficient of `n_1 ⋯ n_d` vanishes for a polynomial that is zero or of total degree less
than `d`. -/
private theorem mixedCoeff_eq_zero_of_eq_zero_or_totalDegree_lt {d : ℕ}
    (P : MvPolynomial (Fin d) ℚ)
    (hP : P = 0 ∨ ((P.totalDegree : ℕ) : WithBot ℕ∞) < (d : WithBot ℕ∞)) :
    mixedCoeff P = 0 := by
  rcases hP with h0 | hlt
  · rw [h0]
    simp [mixedCoeff]
  · exact mixedCoeff_eq_zero_of_totalDegree_lt _ (by exact_mod_cast hlt)

/-- The polynomial of [Stacks, Tag 0BEM] attached to a coherent module: its values at the
integer vectors are the Euler characteristics of its twists. -/
@[ega "III 2.5.3" "(i), special case", sga "6 X 2.3.1"]
private noncomputable def twistEulerPolynomial (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] {r : ℕ} (L : Fin r → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (F : X.Modules) [F.IsCoherent] : MvPolynomial (Fin r) ℚ :=
  (exists_eulerPolynomial_twistedSheaf_of_isProper k p L F inferInstance).choose

/-- The values of `AlgebraicGeometry.twistEulerPolynomial` are the Euler characteristics of the
twists. -/
@[ega "III 7.9.11" "special case"]
private theorem twistEulerPolynomial_eval (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] {r : ℕ} (L : Fin r → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (F : X.Modules) [F.IsCoherent] (n : Fin r → ℤ) :
    MvPolynomial.eval (fun j => (n j : ℚ)) (twistEulerPolynomial k p L F) =
      ((eulerCharacteristic k p (twistedSheaf F L n) : ℤ) : ℚ) :=
  (exists_eulerPolynomial_twistedSheaf_of_isProper k p L F inferInstance).choose_spec.2 n

/-- The total degree of `AlgebraicGeometry.twistEulerPolynomial` is at most the dimension of the
support. -/
private theorem twistEulerPolynomial_degree (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] {r : ℕ} (L : Fin r → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (F : X.Modules) [F.IsCoherent] :
    twistEulerPolynomial k p L F = 0 ∨
      (((twistEulerPolynomial k p L F).totalDegree : ℕ) : WithBot ℕ∞) ≤
        topologicalKrullDim (_root_.SheafOfModules.supp F) :=
  (exists_eulerPolynomial_twistedSheaf_of_isProper k p L F inferInstance).choose_spec.1

/-- If the support has dimension at most `d`, the polynomial of [Stacks, Tag 0BEM] has total
degree at most `d`, so its coefficient of `n_1 ⋯ n_d` is the mixed finite difference of the
Euler characteristics at the indicator vectors. -/
@[sga "6 XIII 2.1" "more general"]
private theorem sum_indicator_eulerCharacteristic_eq_mixedCoeff (k : Type u) [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p] {d : ℕ} (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (F : X.Modules) [F.IsCoherent]
    (hsupp : topologicalKrullDim (_root_.SheafOfModules.supp F) ≤ (d : WithBot ℕ∞)) :
    ∑ T : Finset (Fin d), (-1 : ℚ) ^ (d - T.card) *
        ((eulerCharacteristic k p
          (twistedSheaf F L (fun j => if j ∈ T then 1 else 0)) : ℤ) : ℚ) =
      mixedCoeff (twistEulerPolynomial k p L F) := by
  have hdeg : (twistEulerPolynomial k p L F).totalDegree ≤ d := by
    rcases twistEulerPolynomial_degree k p L F with h | h
    · simp [h]
    · have hle : (((twistEulerPolynomial k p L F).totalDegree : ℕ) : WithBot ℕ∞) ≤
          (d : WithBot ℕ∞) := h.trans hsupp
      exact_mod_cast ENat.natCast_le_natCast.mp (WithBot.coe_le_coe.mp hle)
  simp only [mixedCoeff]
  rw [← MvPolynomial.sum_neg_one_pow_mul_eval_indicator_eq_coeff_one _ hdeg]
  refine Finset.sum_congr rfl fun T _ => ?_
  congr 1
  have h := twistEulerPolynomial_eval k p L F (fun j => if j ∈ T then 1 else 0)
  rw [show (fun j : Fin d => (((if j ∈ T then (1 : ℤ) else 0) : ℤ) : ℚ)) =
      fun j : Fin d => if j ∈ T then (1 : ℚ) else 0 from
    funext fun j => by split_ifs <;> simp] at h
  exact h.symm

/-! ### Coherence of the higher direct images -/

/-- The `q`-th higher direct image `R^q h_*`, in Mathlib's `ℕ`-indexed spelling, which is
defined from an injective resolution and so mentions no model of the derived category.  The
statements imported below use three different models, and
`Stacks.DerivedIndexing.rightDerivedIso` compares each of them with this one. -/
private abbrev higherDirectImage {Z T : Scheme.{u}} (h : Z ⟶ T) (q : ℕ) :
    Z.Modules ⥤ T.Modules :=
  (Scheme.Modules.pushforward h).rightDerived q

/-- Coherence transfers across an isomorphism. -/
private theorem isCoherent_of_iso_coherent {W : Scheme.{u}} {M N : W.Modules} (e : M ≅ N)
    (h : N.IsCoherent) : M.IsCoherent := by
  have := isWeakSerreClass_coherentModules W
  exact ObjectProperty.prop_of_iso (P := fun P : W.Modules => P.IsCoherent) e.symm h

/-- **[Stacks, Tag 02O5]** as an instance: the higher direct images of a coherent module along a
proper morphism to a locally Noetherian scheme are coherent. -/
private instance isCoherent_higherDirectImage {Z T : Scheme.{u}} (h : Z ⟶ T) [IsProper h]
    [IsLocallyNoetherian T] (F : Z.Modules) [F.IsCoherent] (q : ℕ) :
    ((higherDirectImage h q).obj F).IsCoherent := by
  let : HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 1} T.Modules := HasDerivedCategory.standard _
  exact isCoherent_of_iso_coherent
    ((Stacks.DerivedIndexing.rightDerivedIso.{u, u, u + 1, u + 1, u + 1, u + 1}
      (Scheme.Modules.pushforward h) q).app F)
    (ProperCoherenceWitness.higherDirectImageIsCoherent Z T h inferInstance inferInstance F
      inferInstance q)

/-- **The projection formula of [Stacks, Tag 01E8] for the `ℕ`-indexed higher direct images**:
`R^q h_*(𝒪_Z ⊗ ⨂_j (h^*ι^*𝓛_j)^{⊗ n_j}) ≅ (R^q h_*𝒪_Z) ⊗ ⨂_j (ι^*𝓛_j)^{⊗ n_j}`. -/
private def higherDirectImageTwistIso {Z T X : Scheme.{u}} (ι : T ⟶ X) (h : Z ⟶ T)
    {d : ℕ} (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (n : Fin d → ℤ) (q : ℕ) :
    (higherDirectImage h q).obj
        (twistedSheaf (Stacks.Ample.unitModule Z)
          (fun j => (Scheme.Modules.pullback h).obj
            ((Scheme.Modules.pullback ι).obj (L j))) n) ≅
      twistedSheaf ((higherDirectImage h q).obj (Stacks.Ample.unitModule Z))
        (fun j => (Scheme.Modules.pullback ι).obj (L j)) n :=
  (Stacks.DerivedIndexing.rightDerivedIso.{u, u, u + 1, u + 1, u, u}
      (Scheme.Modules.pushforward h) q).app _ ≪≫
    Stacks.ProjectionFormula.higherDirectImageTwistedSheafIso h
        (fun j => (Scheme.Modules.pullback ι).obj (L j)) (Stacks.Ample.unitModule Z) n (q : ℤ) ≪≫
      twistedSheafIsoOfIso (fun j => (Scheme.Modules.pullback ι).obj (L j))
        ((Stacks.DerivedIndexing.rightDerivedIso.{u, u, u + 1, u + 1, u, u}
          (Scheme.Modules.pushforward h) q).app _).symm n

/-- The dimension of the support of a direct image along a closed immersion is at most the
dimension of the subscheme. -/
private theorem topologicalKrullDim_supp_pushforward_le {T X : Scheme.{u}} (ι : T ⟶ X)
    [IsClosedImmersion ι] (N : T.Modules) :
    topologicalKrullDim (_root_.SheafOfModules.supp
        ((Scheme.Modules.pushforward ι).obj N)) ≤ topologicalKrullDim T := by
  rw [topologicalKrullDim_supp_pushforward_of_isClosedImmersion ι N]
  exact Topology.IsInducing.subtypeVal.topologicalKrullDim_le

/-! ### The intersection number as an alternating sum over the higher direct images -/

/-- A closed subscheme of a scheme proper over a field is proper over the target of any
morphism over that field. -/
public theorem isProper_comp_of_structureMap (k : Type u) [Field k] {Y X Z : Scheme.{u}}
    (pY : Y ⟶ Spec (.of k)) (pX : X ⟶ Spec (.of k)) [IsProper pY] [IsProper pX]
    (f : Y ⟶ X) (hf : f ≫ pX = pY) (i : Z ⟶ Y) [IsClosedImmersion i] : IsProper (i ≫ f) := by
  have : IsProper ((i ≫ f) ≫ pX) := by
    rw [Category.assoc, hf]
    infer_instance
  exact IsProper.of_comp (i ≫ f) pX

/-- The Euler characteristic does not depend on which of two equal structure morphisms is
used. -/
private theorem eulerCharacteristic_congr_structureMap (k : Type u) [Field k] {W : Scheme.{u}}
    {p q : W ⟶ Spec (.of k)} (hpq : p = q) [IsProper p] [IsProper q] (G : W.Modules)
    (hG : G.IsCoherent) :
    @eulerCharacteristic k _ W p _ G hG = @eulerCharacteristic k _ W q _ G hG := by
  subst hpq
  rfl

/-- **[Stacks, Tag 0BEK] and the projection formula of [Stacks, Tag 01E8], combined.** For a
proper morphism `h : Z ⟶ T` onto a closed subscheme `ι : T ⟶ X` of a scheme proper over `k`,
the Euler characteristic of a twist of `𝒪_Z` by the pullbacks of invertible `𝒪_X`-modules is the
alternating sum of the Euler characteristics of the twists of the direct images of the higher
direct images `R^q h_*𝒪_Z`. -/
private theorem eulerCharacteristic_twist_eq_finsum (k : Type u) [Field k]
    {Z T X : Scheme.{u}} (pX : X ⟶ Spec (.of k)) [IsProper pX] (ι : T ⟶ X)
    [IsClosedImmersion ι] (h : Z ⟶ T) [IsProper h] {d : ℕ} (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] (n : Fin d → ℤ) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
    haveI : IsLocallyNoetherian T := isLocallyNoetherian_of_isClosedImmersion ι
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian h
    eulerCharacteristic k (h ≫ ι ≫ pX)
        (twistedSheaf (Stacks.Ample.unitModule Z)
          (fun j => (Scheme.Modules.pullback h).obj
            ((Scheme.Modules.pullback ι).obj (L j))) n) =
      ∑ᶠ q : ℕ, (-1 : ℤ) ^ q * eulerCharacteristic k pX
        (twistedSheaf ((Scheme.Modules.pushforward ι).obj
          ((higherDirectImage h q).obj (Stacks.Ample.unitModule Z))) L n) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
  have : IsLocallyNoetherian T := isLocallyNoetherian_of_isClosedImmersion ι
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian h
  let : HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 1} T.Modules := HasDerivedCategory.standard _
  rw [eulerCharacteristic_eq_finsum_higherDirectImage k h (ι ≫ pX) _]
  refine finsum_congr fun q => ?_
  congr 1
  refine Eq.trans ?_ (eulerCharacteristic_twistedSheaf_pushforward_of_isClosedImmersion k ι pX L
    ((higherDirectImage h q).obj (Stacks.Ample.unitModule Z)) n inferInstance
    inferInstance).symm
  exact @eulerCharacteristic_eq_of_iso k _ T (ι ≫ pX) _ _ _
    (ProperCoherenceWitness.higherDirectImageIsCoherent Z T h inferInstance inferInstance _
      inferInstance q)
    inferInstance
    (((Stacks.DerivedIndexing.rightDerivedIso.{u, u, u + 1, u + 1, u + 1, u + 1}
        (Scheme.Modules.pushforward h) q).app
        (twistedSheaf (Stacks.Ample.unitModule Z)
          (fun j => (Scheme.Modules.pullback h).obj
            ((Scheme.Modules.pullback ι).obj (L j))) n)).symm ≪≫
      higherDirectImageTwistIso ι h L n q)

/-- **The intersection number of the pullbacks, as an alternating sum of the coefficients of the
polynomials of [Stacks, Tag 0BEM] attached to the higher direct images.** -/
private theorem intersectionNumber_pullback_eq_sum_mixedCoeff (k : Type u) [Field k]
    {Y X Z T : Scheme.{u}} (pY : Y ⟶ Spec (.of k)) (pX : X ⟶ Spec (.of k))
    [IsProper pY] [IsProper pX] (f : Y ⟶ X) (hf : f ≫ pX = pY) (i : Z ⟶ Y)
    [IsClosedImmersion i] [IsIntegral Z] (ι : T ⟶ X) [IsClosedImmersion ι] (h : Z ⟶ T)
    [IsProper h] (hfac : h ≫ ι = i ≫ f) (d : ℕ)
    (hd : topologicalKrullDim Z ≤ (d : WithBot ℕ∞))
    (hT : topologicalKrullDim T ≤ (d : WithBot ℕ∞)) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
    haveI : IsLocallyNoetherian T := isLocallyNoetherian_of_isClosedImmersion ι
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian h
    ∃ N : ℕ, 0 < N ∧ ((intersectionNumber k pY i d hd
        (fun j => (Scheme.Modules.pullback f).obj (L j)) : ℤ) : ℚ) =
      ∑ q ∈ Finset.range N, (-1 : ℚ) ^ q *
        mixedCoeff (twistEulerPolynomial k pX L
          ((Scheme.Modules.pushforward ι).obj
            ((higherDirectImage h q).obj (Stacks.Ample.unitModule Z)))) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
  have : IsLocallyNoetherian T := isLocallyNoetherian_of_isClosedImmersion ι
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian h
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (ι ≫ pX)
  obtain ⟨B, hB⟩ :=
    Stacks.AlgebraicGeometry.HigherDirectImageQcoh.exists_isZero_rightDerivedNat_pushforward h
  refine ⟨B + 1, Nat.succ_pos B, ?_⟩
  -- the structure morphisms of `Z` agree
  have hstruct : i ≫ pY = h ≫ ι ≫ pX := by
    rw [← Category.assoc, hfac, Category.assoc, hf]
  -- the two families of restrictions of the `𝓛_j` to `Z` are isomorphic
  have efam : ∀ j : Fin d,
      (Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback f).obj (L j)) ≅
        (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback ι).obj (L j)) := fun j =>
    (Scheme.Modules.pullbackComp i f).app (L j) ≪≫
      (Scheme.Modules.pullbackCongr hfac.symm).app (L j) ≪≫
      ((Scheme.Modules.pullbackComp h ι).app (L j)).symm
  -- the Euler characteristic of each twist, expanded over the higher direct images
  have key : ∀ S : Finset (Fin d),
      (eulerCharacteristic k (i ≫ pY)
          (twistedSheaf (Stacks.Ample.unitModule Z)
            (fun j => (Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback f).obj (L j)))
            (fun j => if j ∈ S then 1 else 0)) : ℤ) =
        ∑ᶠ q : ℕ, (-1 : ℤ) ^ q * eulerCharacteristic k pX
          (twistedSheaf ((Scheme.Modules.pushforward ι).obj
            ((higherDirectImage h q).obj (Stacks.Ample.unitModule Z))) L
            (fun j => if j ∈ S then 1 else 0)) := by
    intro S
    have hexp : (fun j : Fin d => ((if j ∈ S then 1 else 0 : ℕ) : ℤ)) =
        (fun j : Fin d => if j ∈ S then (1 : ℤ) else 0) :=
      funext fun j => by split_ifs <;> simp
    have hiso := twistedSheafFamilyIso
      (fun j => (Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback f).obj (L j)))
      (fun j => (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback ι).obj (L j)))
      efam (fun j => if j ∈ S then 1 else 0) (Iso.refl (Stacks.Ample.unitModule Z))
    rw [hexp] at hiso
    refine Eq.trans (eulerCharacteristic_congr_structureMap k hstruct _ inferInstance) ?_
    refine Eq.trans (eulerCharacteristic_eq_of_iso k (h ≫ ι ≫ pX) hiso) ?_
    exact eulerCharacteristic_twist_eq_finsum k pX ι h L (fun j => if j ∈ S then 1 else 0)
  -- only finitely many degrees contribute, uniformly in the twist
  have hsupport : ∀ S : Finset (Fin d), (Function.support fun q : ℕ => (-1 : ℤ) ^ q *
      eulerCharacteristic k pX
        (twistedSheaf ((Scheme.Modules.pushforward ι).obj
          ((higherDirectImage h q).obj (Stacks.Ample.unitModule Z))) L
          (fun j => if j ∈ S then 1 else 0))) ⊆
      (Finset.range (B + 1) : Set ℕ) := by
    intro S q hq
    by_contra hnot
    have hqB : B ≤ q := by
      have : B + 1 ≤ q := Nat.le_of_not_lt (by simpa using hnot)
      omega
    have hzero := hB (Stacks.Ample.unitModule Z) (isQuasicoherent_of_isCoherent _) q hqB
    have hzero' : IsZero ((Scheme.Modules.pushforward ι).obj
        ((higherDirectImage h q).obj (Stacks.Ample.unitModule Z))) :=
      (Scheme.Modules.pushforward ι).map_isZero hzero
    have htw : IsZero (twistedSheaf ((Scheme.Modules.pushforward ι).obj
        ((higherDirectImage h q).obj (Stacks.Ample.unitModule Z))) L
        (fun j => if j ∈ S then 1 else 0)) :=
      isZero_twistedSheaf_of_isZero L hzero' _
    refine hq ?_
    show (-1 : ℤ) ^ q * eulerCharacteristic k pX
      (twistedSheaf ((Scheme.Modules.pushforward ι).obj
        ((higherDirectImage h q).obj (Stacks.Ample.unitModule Z))) L
        (fun j => if j ∈ S then 1 else 0)) = 0
    rw [eulerCharacteristic_eq_zero_of_isZero k pX _ inferInstance htw, mul_zero]
  -- assemble
  have hstepZ : intersectionNumber k pY i d hd
      (fun j => (Scheme.Modules.pullback f).obj (L j)) =
      ∑ S : Finset (Fin d), ∑ q ∈ Finset.range (B + 1), (-1 : ℤ) ^ (d - S.card) * ((-1 : ℤ) ^ q *
        eulerCharacteristic k pX (twistedSheaf ((Scheme.Modules.pushforward ι).obj
          ((higherDirectImage h q).obj (Stacks.Ample.unitModule Z))) L
          (fun j => if j ∈ S then 1 else 0))) := by
    rw [intersectionNumber_eq_sum_eulerCharacteristic]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    rw [← finsum_eq_finsetSum_of_support_subset _ (hsupport S)]
    exact key S
  rw [hstepZ, Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← sum_indicator_eulerCharacteristic_eq_mixedCoeff k pX L _
    ((topologicalKrullDim_supp_pushforward_le ι _).trans hT), Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  ring

/-! ### Supports and generic points of a scheme-theoretic image -/

/-- **The direct image of the structure sheaf is supported at the image of the generic point**,
when that point is the only point of its fibre: the stalk there is the function field of the
source, which is not the zero ring. -/
private theorem mem_supp_pushforward_unitModule {Z X : Scheme.{u}} (g : Z ⟶ X)
    [IsProper g] [IsIntegral Z] [IsLocallyNoetherian Z]
    (hfib : ∀ z : Z, g.base z = g.base (genericPoint Z) → z = genericPoint Z) :
    g.base (genericPoint Z) ∈ _root_.SheafOfModules.supp
      ((Scheme.Modules.pushforward g).obj (Stacks.Ample.unitModule Z)) := by
  classical
  have hsupp : _root_.SheafOfModules.supp (Stacks.Ample.unitModule Z) = Set.univ :=
    supp_unitModule Z
  have hηmem : genericPoint Z ∈ _root_.SheafOfModules.supp (Stacks.Ample.unitModule Z) := by
    rw [hsupp]; trivial
  let : Unique ↥{z : Z | g.base z = g.base (genericPoint Z) ∧
      z ∈ _root_.SheafOfModules.supp (Stacks.Ample.unitModule Z)} :=
    { default := ⟨genericPoint Z, rfl, hηmem⟩
      uniq := fun z => Subtype.ext (hfib z.1 z.2.1) }
  let : ∀ z : ↥{z : Z | g.base z = g.base (genericPoint Z) ∧
        z ∈ _root_.SheafOfModules.supp (Stacks.Ample.unitModule Z)},
      Module (X.presheaf.stalk (g.base (genericPoint Z)))
        ((Stacks.Ample.unitModule Z).presheaf.stalk z.1) :=
    Stacks.Chow.supportFibreStalkModule g (Stacks.Ample.unitModule Z)
      (g.base (genericPoint Z))
  have hgen := exists_component_isGenericPoint_fibre_unitModule g hfib
  refine (_root_.SheafOfModules.mem_supp_iff_nontrivial_stalk _ _).mpr ?_
  have : Nontrivial ((Stacks.Ample.unitModule Z).presheaf.stalk (genericPoint Z)) :=
    (Stacks.Ample.unitStalkEquiv Z (genericPoint Z)).symm.injective.nontrivial
  have : Nontrivial (∀ z : ↥{z : Z | g.base z = g.base (genericPoint Z) ∧
      z ∈ _root_.SheafOfModules.supp (Stacks.Ample.unitModule Z)},
      (Stacks.Ample.unitModule Z).presheaf.stalk z.1) :=
    (Equiv.piUnique (fun z : ↥{z : Z | g.base z = g.base (genericPoint Z) ∧
      z ∈ _root_.SheafOfModules.supp (Stacks.Ample.unitModule Z)} =>
      (Stacks.Ample.unitModule Z).presheaf.stalk z.1)).symm.injective.nontrivial
  exact (Stacks.Chow.pushforwardStalkLinearEquivPi g (Stacks.Ample.unitModule Z)
    (_root_.SheafOfModules.isClosed_supp _) (g.base (genericPoint Z))
    (Stacks.Chow.locallyFinite_irreducibleComponents_supp _)
    hgen).symm.injective.nontrivial

/-! ### Tag 0BET -/

/-- **[Stacks, Tag 0BET], the case of a scheme-theoretic image of smaller dimension.** Let `k`
be a field, let `f : Y ⟶ X` be a morphism of schemes proper over `k`, let `i : Z ⟶ Y` be an
integral closed subscheme of dimension at most `d` and let `𝓛_1, …, 𝓛_d` be invertible
`𝒪_X`-modules.  If the scheme-theoretic image `f(Z)` has dimension less than `d`, then

`(f^*𝓛_1 ⋯ f^*𝓛_d · Z) = 0`. -/
@[stacks 0BET "the right-hand side is zero when the scheme-theoretic image has dimension less \
than d"]
public theorem intersectionNumber_pullback_eq_zero (k : Type u) [Field k] {Y X Z : Scheme.{u}}
    (pY : Y ⟶ Spec (.of k)) (pX : X ⟶ Spec (.of k)) [IsProper pY] [IsProper pX]
    (f : Y ⟶ X) (hf : f ≫ pX = pY) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ (d : WithBot ℕ∞)) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (hIm : topologicalKrullDim (i ≫ f).image < (d : WithBot ℕ∞)) :
    intersectionNumber k pY i d hd (fun j => (Scheme.Modules.pullback f).obj (L j)) = 0 := by
  have := isProper_comp_of_structureMap k pY pX f hf i
  have := Stacks.Chow.isProper_toImage (i ≫ f)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
  have : IsLocallyNoetherian (i ≫ f).image :=
    isLocallyNoetherian_of_isClosedImmersion (i ≫ f).imageι
  have : IsLocallyNoetherian Z :=
    LocallyOfFiniteType.isLocallyNoetherian (i ≫ f).toImage
  obtain ⟨N, -, hsum⟩ := intersectionNumber_pullback_eq_sum_mixedCoeff k pY pX f hf i
    (i ≫ f).imageι (i ≫ f).toImage (i ≫ f).toImage_imageι d hd hIm.le L
  have hzero : ∀ q ∈ Finset.range N, (-1 : ℚ) ^ q *
      mixedCoeff (twistEulerPolynomial k pX L
        ((Scheme.Modules.pushforward (i ≫ f).imageι).obj
          ((higherDirectImage (i ≫ f).toImage q).obj (Stacks.Ample.unitModule Z)))) = 0 := by
    intro q _
    refine mul_eq_zero_of_right _ (mixedCoeff_eq_zero_of_eq_zero_or_totalDegree_lt _ ?_)
    refine (twistEulerPolynomial_degree k pX L _).imp_right fun hle => ?_
    exact lt_of_le_of_lt (hle.trans (topologicalKrullDim_supp_pushforward_le _ _)) hIm
  rw [Finset.sum_eq_zero hzero] at hsum
  exact_mod_cast hsum

/-- **[Stacks, Tag 0BET], the equal-dimensional case.** Let `k` be a field, let `f : Y ⟶ X` be a
morphism of schemes proper over `k`, let `i : Z ⟶ Y` be an integral closed subscheme of
dimension `d` and let `𝓛_1, …, 𝓛_d` be invertible `𝒪_X`-modules.  If the scheme-theoretic image
`f(Z)` again has dimension `d`, then

`(f^*𝓛_1 ⋯ f^*𝓛_d · Z) = deg(f|_Z : Z → f(Z)) (𝓛_1 ⋯ 𝓛_d · f(Z))`,

the degree being the one of [Stacks, Morphisms, Definition 02NY]. -/
@[stacks 0BET "the degree formula when the scheme-theoretic image has the same dimension"]
public theorem intersectionNumber_pullback_eq_degreeOver_mul (k : Type u) [Field k]
    {Y X Z : Scheme.{u}} (pY : Y ⟶ Spec (.of k)) (pX : X ⟶ Spec (.of k))
    [IsProper pY] [IsProper pX] (f : Y ⟶ X) (hf : f ≫ pX = pY) (i : Z ⟶ Y)
    [IsClosedImmersion i] [IsIntegral Z] (d : ℕ)
    (hZ : topologicalKrullDim Z = (d : WithBot ℕ∞)) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (hIm : topologicalKrullDim (i ≫ f).image = (d : WithBot ℕ∞)) :
    haveI : IsProper (i ≫ f) := isProper_comp_of_structureMap k pY pX f hf i
    haveI : IsIntegral (i ≫ f).image := Stacks.Chow.isIntegral_image (i ≫ f)
    haveI : IsProper (i ≫ f).toImage := Stacks.Chow.isProper_toImage (i ≫ f)
    intersectionNumber k pY i d hZ.le (fun j => (Scheme.Modules.pullback f).obj (L j)) =
      degreeOver (i ≫ f).toImage *
        intersectionNumber k pX (i ≫ f).imageι d hIm.le L := by
  classical
  have := isProper_comp_of_structureMap k pY pX f hf i
  have hint : IsIntegral (i ≫ f).image := Stacks.Chow.isIntegral_image (i ≫ f)
  have := Stacks.Chow.isProper_toImage (i ≫ f)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
  have : IsLocallyNoetherian (i ≫ f).image :=
    isLocallyNoetherian_of_isClosedImmersion (i ≫ f).imageι
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ f).toImage
  have hG₀coh : ((Scheme.Modules.pushforward (i ≫ f)).obj
      (Stacks.Ample.unitModule Z)).IsCoherent :=
    ProperCoherenceWitness.isCoherent_pushforward (i ≫ f) (Stacks.Ample.unitModule Z)
  have : ((Scheme.Modules.pushforward (i ≫ f)).obj
      (Stacks.Ample.unitModule Z)).IsFiniteType :=
    _root_.SheafOfModules.IsCoherent.isFiniteType
  -- the generic fibre of `Z ⟶ f(Z)` is the generic point of `Z`
  have hfibT : ∀ z : Z, (i ≫ f).toImage.base z = genericPoint (i ≫ f).image →
      z = genericPoint Z := fun z hz =>
    eq_genericPoint_of_map_eq_genericPoint_of_dim_eq (i ≫ f).toImage
      (i ≫ f).toImage.isClosedMap hZ hIm hz
  have hgη : (i ≫ f).base (genericPoint Z) =
      (i ≫ f).imageι.base (genericPoint (i ≫ f).image) := by
    have h0 : (i ≫ f).toImage.base (genericPoint Z) = genericPoint (i ≫ f).image :=
      map_genericPoint_of_isDominant (i ≫ f).toImage
    conv_lhs => rw [← (i ≫ f).toImage_imageι]
    show (i ≫ f).imageι.base ((i ≫ f).toImage.base (genericPoint Z)) = _
    rw [h0]
  have hfibg : ∀ z : Z, (i ≫ f).base z = (i ≫ f).base (genericPoint Z) →
      z = genericPoint Z := by
    intro z hz
    refine hfibT z ?_
    have h1 : (i ≫ f).imageι.base ((i ≫ f).toImage.base z) =
        (i ≫ f).imageι.base (genericPoint (i ≫ f).image) := by
      rw [← hgη, ← hz]
      conv_rhs => rw [← (i ≫ f).toImage_imageι]
      rfl
    exact (i ≫ f).imageι.isEmbedding.injective h1
  -- the support of `g_*𝒪_Z` is the scheme-theoretic image
  have hξsupp : (i ≫ f).imageι.base (genericPoint (i ≫ f).image) ∈
      _root_.SheafOfModules.supp
        ((Scheme.Modules.pushforward (i ≫ f)).obj (Stacks.Ample.unitModule Z)) := by
    rw [← hgη]
    exact mem_supp_pushforward_unitModule (i ≫ f) hfibg
  have hsuppG : _root_.SheafOfModules.supp
      ((Scheme.Modules.pushforward (i ≫ f)).obj (Stacks.Ample.unitModule Z)) =
      ((i ≫ f).ker.support : Set X) := by
    have hiso : (Scheme.Modules.pushforward (i ≫ f).imageι).obj
        ((Scheme.Modules.pushforward (i ≫ f).toImage).obj (Stacks.Ample.unitModule Z)) ≅
        (Scheme.Modules.pushforward (i ≫ f)).obj (Stacks.Ample.unitModule Z) :=
      (Scheme.Modules.pushforwardComp (i ≫ f).toImage (i ≫ f).imageι).app
          (Stacks.Ample.unitModule Z) ≪≫
        (Scheme.Modules.pushforwardCongr (i ≫ f).toImage_imageι).app
          (Stacks.Ample.unitModule Z)
    refine Set.Subset.antisymm ?_ ?_
    · rw [← _root_.SheafOfModules.supp_eq_of_iso hiso,
        supp_pushforward_of_isClosedImmersion, ← (i ≫ f).ker.range_subschemeι]
      exact Set.image_subset_range _ _
    · rw [← Stacks.AlgebraicGeometry.CoherentDevissageGlue.isGenericPoint_subschemeι_genericPoint
        (i ≫ f).ker]
      exact closure_minimal (Set.singleton_subset_iff.mpr hξsupp)
        (_root_.SheafOfModules.isClosed_supp _)
  have hkd : topologicalKrullDim ((i ≫ f).ker.support : Set X) = (d : WithBot ℕ∞) :=
    (topologicalKrullDim_support_eq (i ≫ f).ker).trans hIm
  have hdimG : topologicalKrullDim (_root_.SheafOfModules.supp
      ((Scheme.Modules.pushforward (i ≫ f)).obj (Stacks.Ample.unitModule Z))) =
      (d : WithBot ℕ∞) := by rw [hsuppG, hkd]
  -- the scheme-theoretic image is the only top-dimensional integral component of that support
  have hirrS : IsIrreducible ((i ≫ f).ker.support : Set X) := by
    rw [← Stacks.AlgebraicGeometry.CoherentDevissageGlue.isGenericPoint_subschemeι_genericPoint
      (i ≫ f).ker]
    exact isIrreducible_singleton.closure
  let W₀ : TopDimIntegralSubscheme
      ((Scheme.Modules.pushforward (i ≫ f)).obj (Stacks.Ample.unitModule Z)) :=
    ⟨(i ≫ f).ker, hint, hsuppG.ge, hIm.trans hdimG.symm⟩
  have huniq : ∀ W : TopDimIntegralSubscheme
      ((Scheme.Modules.pushforward (i ≫ f)).obj (Stacks.Ample.unitModule Z)), W = W₀ := by
    intro W
    refine TopDimIntegralSubscheme.val_injective _ ?_
    have hWsub : (W.1.support : Set X) ⊆ ((i ≫ f).ker.support : Set X) := by
      rw [← hsuppG]
      exact W.2.2.1
    show (W.1.support : Set X) = ((i ≫ f).ker.support : Set X)
    refine Set.Subset.antisymm hWsub ?_
    have hξW : (i ≫ f).imageι.base (genericPoint (i ≫ f).image) ∈
        (W.1.support : Set X) := by
      by_contra hnot
      have : IrreducibleSpace ↥((i ≫ f).ker.support : Set X) := Subtype.irreducibleSpace hirrS
      have hA : IsClosed ((Subtype.val : ((i ≫ f).ker.support : Set X) → X) ⁻¹'
          (W.1.support : Set X)) := W.1.support.isClosed.preimage continuous_subtype_val
      have hAne : ((Subtype.val : ((i ≫ f).ker.support : Set X) → X) ⁻¹'
          (W.1.support : Set X)) ≠ Set.univ := by
        intro he
        refine hnot ?_
        have hmem : ((i ≫ f).imageι.base (genericPoint (i ≫ f).image)) ∈
            ((i ≫ f).ker.support : Set X) := by
          rw [← hsuppG]; exact hξsupp
        exact (Set.ext_iff.mp he ⟨_, hmem⟩).mpr (Set.mem_univ _)
      have hfin : topologicalKrullDim ((i ≫ f).ker.support : Set X) < ⊤ := by
        rw [hkd]
        exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _)
      have hlt := topologicalKrullDim_lt_of_isClosed_ne_univ hA hAne hfin
      have hpre : topologicalKrullDim ((Subtype.val : ((i ≫ f).ker.support : Set X) → X) ⁻¹'
          (W.1.support : Set X)) = (d : WithBot ℕ∞) := by
        rw [← (subsetInclusionHomeomorph hWsub).isHomeomorph.topologicalKrullDim_eq _,
          topologicalKrullDim_support_eq, W.2.2.2]
        exact hdimG
      rw [hpre, hkd] at hlt
      exact absurd hlt (lt_irrefl _)
    rw [← Stacks.AlgebraicGeometry.CoherentDevissageGlue.isGenericPoint_subschemeι_genericPoint
      (i ≫ f).ker]
    exact closure_minimal (Set.singleton_subset_iff.mpr hξW) W.1.support.isClosed
  let : Unique (TopDimIntegralSubscheme
      ((Scheme.Modules.pushforward (i ≫ f)).obj (Stacks.Ample.unitModule Z))) :=
    { default := W₀, uniq := huniq }
  -- the multiplicity at the generic point is the degree
  have hmult : Stacks.Chow.sheafMultiplicity
      ((Scheme.Modules.pushforward (i ≫ f)).obj (Stacks.Ample.unitModule Z)) W₀.genericPt =
      (degreeOver (i ≫ f).toImage : ℤ) := by
    have hpt : W₀.genericPt = (i ≫ f).base (genericPoint Z) := by
      rw [hgη]
      rfl
    rw [hpt, sheafMultiplicity_pushforward_unitModule (i ≫ f) hfibg]
    have hdeg : (i ≫ f).residueDegree (genericPoint Z) = degreeOver (i ≫ f).toImage := by
      conv_lhs => rw [← (i ≫ f).toImage_imageι]
      rw [Stacks.Chow.residueDegree_comp,
        Stacks.Chow.residueDegree_eq_one_of_isPreimmersion (i ≫ f).imageι, one_mul,
        residueDegree_genericPoint_eq_degreeOver]
    exact_mod_cast hdeg
  -- the alternating sum over the degrees, with only `q = 0` contributing
  obtain ⟨N, hNpos, hsum⟩ := intersectionNumber_pullback_eq_sum_mixedCoeff k pY pX f hf i
    (i ≫ f).imageι (i ≫ f).toImage (i ≫ f).toImage_imageι d hZ.le hIm.le L
  -- only the degree-zero term survives
  have hposvanish : ∀ q ∈ Finset.range N, q ≠ 0 → (-1 : ℚ) ^ q *
      mixedCoeff (twistEulerPolynomial k pX L
        ((Scheme.Modules.pushforward (i ≫ f).imageι).obj
          ((higherDirectImage (i ≫ f).toImage q).obj (Stacks.Ample.unitModule Z)))) = 0 := by
    intro q _ hq0
    refine mul_eq_zero_of_right _ ?_
    have hfinfib : ((i ≫ f).toImage.base ⁻¹' {genericPoint (i ≫ f).image}).Finite :=
      (Set.finite_singleton (genericPoint Z)).subset fun z hz => hfibT z hz
    let : HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _
    let : HasDerivedCategory.{u + 1} (i ≫ f).image.Modules := HasDerivedCategory.standard _
    have hz0 := Stacks.FormalFunctions.isZero_stalk_higherDirectImage_of_finite_fibre
      (i ≫ f).toImage (genericPoint (i ≫ f).image) hfinfib (Stacks.Ample.unitModule Z)
      (q : ℤ) (by exact_mod_cast Nat.pos_of_ne_zero hq0)
    have hnotmem : genericPoint (i ≫ f).image ∉ _root_.SheafOfModules.supp
        ((higherDirectImage (i ≫ f).toImage q).obj (Stacks.Ample.unitModule Z)) := by
      rw [_root_.SheafOfModules.supp_eq_of_iso
        ((Stacks.DerivedIndexing.rightDerivedIso.{u, u, u + 1, u + 1, u + 1, u + 1}
          (Scheme.Modules.pushforward (i ≫ f).toImage) q).app (Stacks.Ample.unitModule Z))]
      intro hmem
      exact (not_nontrivial_iff_subsingleton.mpr (AddCommGrpCat.subsingleton_of_isZero hz0))
        ((_root_.SheafOfModules.mem_supp_iff_nontrivial_stalk _ _).mp hmem)
    have : ((higherDirectImage (i ≫ f).toImage q).obj
        (Stacks.Ample.unitModule Z)).IsFiniteType :=
      _root_.SheafOfModules.IsCoherent.isFiniteType
    have hne : _root_.SheafOfModules.supp ((higherDirectImage (i ≫ f).toImage q).obj
        (Stacks.Ample.unitModule Z)) ≠ Set.univ := fun he => hnotmem (he ▸ Set.mem_univ _)
    have hlt := topologicalKrullDim_lt_of_isClosed_ne_univ
      (_root_.SheafOfModules.isClosed_supp
        ((higherDirectImage (i ≫ f).toImage q).obj (Stacks.Ample.unitModule Z))) hne
      (by rw [hIm]; exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _))
    rw [hIm] at hlt
    refine mixedCoeff_eq_zero_of_eq_zero_or_totalDegree_lt _
      ((twistEulerPolynomial_degree k pX L _).imp_right fun hle => ?_)
    rw [topologicalKrullDim_supp_pushforward_of_isClosedImmersion] at hle
    exact hle.trans_lt hlt
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hNpos)
    (fun q hq hq0 => hposvanish q hq hq0), pow_zero, one_mul] at hsum
  -- in degree zero the higher direct image is the direct image
  have e0 : (Scheme.Modules.pushforward (i ≫ f).imageι).obj
      ((higherDirectImage (i ≫ f).toImage 0).obj (Stacks.Ample.unitModule Z)) ≅
      (Scheme.Modules.pushforward (i ≫ f)).obj (Stacks.Ample.unitModule Z) :=
    (Scheme.Modules.pushforward (i ≫ f).imageι).mapIso
        ((Functor.rightDerivedZeroIsoSelf
          (Scheme.Modules.pushforward (i ≫ f).toImage)).app (Stacks.Ample.unitModule Z)) ≪≫
      (Scheme.Modules.pushforwardComp (i ≫ f).toImage (i ≫ f).imageι).app
        (Stacks.Ample.unitModule Z) ≪≫
      (Scheme.Modules.pushforwardCongr (i ≫ f).toImage_imageι).app (Stacks.Ample.unitModule Z)
  have hA : mixedCoeff (twistEulerPolynomial k pX L
        ((Scheme.Modules.pushforward (i ≫ f).imageι).obj
          ((higherDirectImage (i ≫ f).toImage 0).obj (Stacks.Ample.unitModule Z)))) =
      mixedCoeff (twistEulerPolynomial k pX L
        ((Scheme.Modules.pushforward (i ≫ f)).obj (Stacks.Ample.unitModule Z))) := by
    rw [← sum_indicator_eulerCharacteristic_eq_mixedCoeff k pX L _
        ((topologicalKrullDim_supp_pushforward_le (i ≫ f).imageι _).trans hIm.le),
      ← sum_indicator_eulerCharacteristic_eq_mixedCoeff k pX L _ hdimG.le]
    refine Finset.sum_congr rfl fun S _ => ?_
    congr 1
    exact congrArg (fun m : ℤ => (m : ℚ))
      (eulerCharacteristic_eq_of_iso k pX (twistedSheafIsoOfIso L e0 _))
  -- the leading coefficient is the multiplicity times the intersection number of the image
  obtain ⟨R, hRdeg, hReval⟩ := exists_eulerPolynomial_sub_topDimComponents_totalDegree_lt k pX L
    ((Scheme.Modules.pushforward (i ≫ f)).obj (Stacks.Ample.unitModule Z))
  rw [hdimG] at hRdeg
  have hRdegle : R.totalDegree ≤ d := by
    rcases hRdeg with h0 | hlt
    · simp [h0]
    · exact le_of_lt (by exact_mod_cast hlt)
  have hRc : mixedCoeff R = 0 := mixedCoeff_eq_zero_of_eq_zero_or_totalDegree_lt R hRdeg
  have hdiff : ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
      MvPolynomial.eval (fun j => if j ∈ S then (1 : ℚ) else 0) R = 0 := by
    rw [MvPolynomial.sum_neg_one_pow_mul_eval_indicator_eq_coeff_one R hRdegle]
    exact hRc
  have hvals : ∀ S : Finset (Fin d),
      MvPolynomial.eval (fun j => if j ∈ S then (1 : ℚ) else 0) R =
        ((eulerCharacteristic k pX (twistedSheaf
            ((Scheme.Modules.pushforward (i ≫ f)).obj (Stacks.Ample.unitModule Z)) L
            (fun j => if j ∈ S then 1 else 0)) : ℤ) : ℚ) -
          ((Stacks.Chow.sheafMultiplicity
            ((Scheme.Modules.pushforward (i ≫ f)).obj (Stacks.Ample.unitModule Z))
            W₀.genericPt : ℤ) : ℚ) *
            ((componentTwistEulerCharacteristic k pX L W₀
              (fun j => if j ∈ S then 1 else 0) : ℤ) : ℚ) := by
    intro S
    have hh := hReval (fun j => if j ∈ S then (1 : ℤ) else 0)
    rw [show (fun j : Fin d => (((if j ∈ S then (1 : ℤ) else 0) : ℤ) : ℚ)) =
        fun j : Fin d => if j ∈ S then (1 : ℚ) else 0 from
      funext fun j => by split_ifs <;> simp] at hh
    rw [hh, finsum_unique]
    rfl
  have hfinal : mixedCoeff (twistEulerPolynomial k pX L
        ((Scheme.Modules.pushforward (i ≫ f)).obj (Stacks.Ample.unitModule Z))) =
      ((Stacks.Chow.sheafMultiplicity
        ((Scheme.Modules.pushforward (i ≫ f)).obj (Stacks.Ample.unitModule Z))
        W₀.genericPt : ℤ) : ℚ) *
        ((intersectionNumber k pX (i ≫ f).imageι d hIm.le L : ℤ) : ℚ) := by
    rw [← sum_indicator_eulerCharacteristic_eq_mixedCoeff k pX L _ hdimG.le]
    have hcomp : ((intersectionNumber k pX (i ≫ f).imageι d hIm.le L : ℤ) : ℚ) =
        ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
          ((componentTwistEulerCharacteristic k pX L W₀
            (fun j => if j ∈ S then 1 else 0) : ℤ) : ℚ) := by
      rw [intersectionNumber_eq_sum_eulerCharacteristic]
      push_cast
      exact Finset.sum_congr rfl fun S _ => rfl
    have h1 : ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
        (((eulerCharacteristic k pX (twistedSheaf
              ((Scheme.Modules.pushforward (i ≫ f)).obj (Stacks.Ample.unitModule Z)) L
              (fun j => if j ∈ S then 1 else 0)) : ℤ) : ℚ) -
          ((Stacks.Chow.sheafMultiplicity
            ((Scheme.Modules.pushforward (i ≫ f)).obj (Stacks.Ample.unitModule Z))
            W₀.genericPt : ℤ) : ℚ) *
            ((componentTwistEulerCharacteristic k pX L W₀
              (fun j => if j ∈ S then 1 else 0) : ℤ) : ℚ)) = 0 := by
      rw [← hdiff]
      exact Finset.sum_congr rfl fun S _ => by rw [hvals S]
    simp only [mul_sub] at h1
    rw [Finset.sum_sub_distrib, sub_eq_zero] at h1
    rw [h1, hcomp, Finset.mul_sum]
    exact Finset.sum_congr rfl fun S _ => by ring
  rw [hA, hfinal, hmult] at hsum
  exact_mod_cast hsum

end AlgebraicGeometry

end
