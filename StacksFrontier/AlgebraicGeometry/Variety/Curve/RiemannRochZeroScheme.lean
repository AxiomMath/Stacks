module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.ClosedSubschemeZeroCycle
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegreeClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeRegularSection
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree

/-!
# The Chern-class side of the degree formula: the zero scheme of a section

Let `k` be a field, let `X` be proper over `k` of dimension at most one and let `ℒ` be an
invertible `𝒪_X`-module with a global section `s`. By [Stacks, Tag 02SQ] the cap product
`c₁(ℒ) ∩ [X]_1` is the class of the zero cycle `[Z(s)]_0` of the zero scheme of `s`, so

`deg(c₁(ℒ) ∩ [X]_1) = deg([Z(s)]_0)`,

where the left-hand side is `AlgebraicGeometry.curveChernDegree` and the right-hand side is
`Stacks.Chow.cycleDegree`. When `X` is integral and `s` is nonzero, `deg([Z(s)]_0)` is
`dim_k H⁰(Z(s), ℒ|_{Z(s)})`, which gives the degree formula [Stacks, Tag 0BRY]
`deg(ℒ) = deg(c₁(ℒ) ∩ [X]_1)` and the Riemann-Roch formula [Stacks, Tag 0BRZ] for such an `ℒ`.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `relativeDimension_fieldChowSituation_le_of_topologicalKrullDim_le`: over a field the relative
  dimension at a point is bounded by the topological dimension of the scheme.
* `schemeDeltaDimension_fieldChowSituation_le_of_topologicalKrullDim_le`: over a field the
  delta-dimension of a closed subscheme is bounded by its topological dimension.
* `curveChernDegree_eq_cycleDegree_zeroScheme`: the displayed equation, under the hypotheses of
  [Stacks, Tag 02SQ].
* `curveChernDegree_eq_cycleDegree_zeroScheme_of_isIntegral`: the same on an integral `X` for a
  nonzero section.
* `degree_zeroCycle_zeroScheme_eq_finrank_cohomologyOverField`: the degree of the zero cycle of
  a nonzero section is `dim_k H⁰(Z(s), ℒ|_{Z(s)})`.
* `invertibleCurveDegree_eq_curveChernDegree_of_isIntegral`: the degree formula for an
  invertible module with a nonzero global section on a proper integral curve.
* `curveDegree_one_eq_curveChernDegree_of_isIntegral`: equation [Stacks, Tag 0BRY] for such a
  module, in the `AlgebraicGeometry.curveDegree` spelling.
* `eulerCharacteristic_eq_curveChernDegree_add_of_isIntegral`: equation [Stacks, Tag 0BRZ] for
  such a module, `χ(X, ℒ) = deg(c₁(ℒ) ∩ [X]_1) + χ(X, 𝒪_X)`.

## References

* [Stacks Project, Tag 0BRY](https://stacks.math.columbia.edu/tag/0BRY)
* [Stacks Project, Tag 0BRZ](https://stacks.math.columbia.edu/tag/0BRZ)
* [Stacks Project, Tag 0AZ3](https://stacks.math.columbia.edu/tag/0AZ3)
* [Stacks Project, Tag 02SQ](https://stacks.math.columbia.edu/tag/02SQ)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Chow Opposite

universe u

namespace AlgebraicGeometry

/-- **Over a field the relative dimension at a point is bounded by the topological dimension**:
if `dim X ≤ n` then the relative dimension of `X` over `Spec k` at every point is at most `n`. -/
public theorem relativeDimension_fieldChowSituation_le_of_topologicalKrullDim_le
    (k : Type u) [Field k] {X : Scheme.{u}} (q : X ⟶ (fieldChowSituation k).S)
    [LocallyOfFiniteType q] (n : ℕ) (hdim : topologicalKrullDim X ≤ (n : WithBot ℕ∞)) (x : X) :
    relativeDimension (fieldChowSituation k).dimensionFunction q x ≤ (n : ℤ) := by
  have : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  have hgen : IsGenericPoint (genericPoint (integralComponentAt x).subscheme)
      (Set.univ : Set (integralComponentAt x).subscheme) :=
    (IrreducibleSpace.isIrreducible_univ _).isGenericPoint_genericPoint isClosed_univ
  have hkey := topologicalKrullDim_eq_relativeDimension_toNat (fieldChowSituation k)
    (fun _ _ ↦ rfl) q (integralComponentAt x).subschemeι
    (genericPoint (integralComponentAt x).subscheme) hgen
  rw [show (integralComponentAt x).subschemeι.base
      (genericPoint (integralComponentAt x).subscheme) = x from
    genericPointOf_integralComponentAt x] at hkey
  have hle : topologicalKrullDim (integralComponentAt x).subscheme ≤ topologicalKrullDim X :=
    (IsClosedImmersion.isClosedEmbedding
      (integralComponentAt x).subschemeι).isInducing.topologicalKrullDim_le
  rw [hkey] at hle
  have hnn := relativeDimension_nonneg (fieldChowSituation k) (fun _ _ ↦ rfl) q x
  have hnat : (relativeDimension (fieldChowSituation k).dimensionFunction q x).toNat ≤ n := by
    exact_mod_cast hle.trans hdim
  lia

/-- **Over a field the delta-dimension of a closed subscheme is bounded by its topological
dimension**: if `dim Z ≤ n` for a closed immersion `i : Z ⟶ X`, then `Z` has delta-dimension at
most `n` over `Spec k`. -/
public theorem schemeDeltaDimension_fieldChowSituation_le_of_topologicalKrullDim_le
    (k : Type u) [Field k] {X Z : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
    [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ)
    (hdim : topologicalKrullDim Z ≤ (n : WithBot ℕ∞)) :
    schemeDeltaDimension (fieldChowSituation k) (i ≫ sX) ≤ ((n : ℤ) : EInt) := by
  refine schemeDeltaDimension_le_of_forall_point (fieldChowSituation k) sX i fun z ↦ ?_
  rw [← relativeDimension_comp_closedImmersion (fieldChowSituation k).dimensionFunction i sX z]
  exact relativeDimension_fieldChowSituation_le_of_topologicalKrullDim_le k (i ≫ sX) n hdim z

variable (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]

/-- The delta-dimension of an effective Cartier divisor on a scheme of dimension at most one is at
most zero. -/
private theorem schemeDeltaDimension_divisor_le_zero
    (k : Type u) [Field k] {X : Scheme.{u}} (q : X ⟶ (fieldChowSituation k).S)
    [LocallyOfFiniteType q] (hdim : topologicalKrullDim X ≤ 1) (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    schemeDeltaDimension (fieldChowSituation k) (D.subschemeι ≫ q) ≤ ((0 : ℤ) : EInt) :=
  schemeDeltaDimension_fieldChowSituation_le_of_topologicalKrullDim_le k q D.subschemeι 0
    (topologicalKrullDim_divisorSubscheme_le_zero hdim D)

/-- **The Chern side of the degree formula is the degree of the zero cycle of a section**: for
`ℒ` invertible on `X` and a section `t` of `(𝟙 X)^*ℒ`,

`deg(c₁(ℒ) ∩ [X]_1) = deg([Z(t)]_0)`,

given the two delta-dimension bounds and the stalk-injectivity hypothesis of
[Stacks, Tag 02SQ]. -/
public theorem curveChernDegree_eq_cycleDegree_zeroScheme
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      ((Scheme.Modules.pullback (𝟙 X)).obj L)]
    (t : ((Scheme.Modules.pullback (𝟙 X)).obj L).sections)
    (hY : schemeDeltaDimension (fieldChowSituation k) (𝟙 X ≫ p) ≤ ((0 + 1 : ℤ) : EInt))
    (hD : schemeDeltaDimension (fieldChowSituation k)
      ((Stacks.Divisors.zeroScheme X ((Scheme.Modules.pullback (𝟙 X)).obj L)
        (t.eval (op ⊤))).subschemeι ≫ (𝟙 X ≫ p)) ≤ ((0 : ℤ) : EInt))
    (hs : ∀ ξ : genericPoints (Stacks.Divisors.zeroScheme X
        ((Scheme.Modules.pullback (𝟙 X)).obj L) (t.eval (op ⊤))).subscheme,
      relativeDimension (fieldChowSituation k).dimensionFunction (𝟙 X ≫ p)
          ((Stacks.Divisors.zeroScheme X ((Scheme.Modules.pullback (𝟙 X)).obj L)
            (t.eval (op ⊤))).subschemeι ξ.1) = 0 →
        Function.Injective (ConcreteCategory.hom
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
            ((Stacks.Divisors.zeroScheme X ((Scheme.Modules.pullback (𝟙 X)).obj L)
              (t.eval (op ⊤))).subschemeι ξ.1)).map
            ((Scheme.Modules.toPresheaf X).map
              (((Scheme.Modules.pullback (𝟙 X)).obj L).unitHomEquiv.symm t))))) :
    curveChernDegree k p hdim (firstChernComponentCycleRule (fieldChowSituation k) p 0 L) =
      cycleDegree (fieldChowSituation k) p (IsLocalRing.closedPoint k)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
          ((Stacks.Divisors.zeroScheme X ((Scheme.Modules.pullback (𝟙 X)).obj L)
            (t.eval (op ⊤))).subschemeι ≫ 𝟙 X) 0) := by
  have h02SQ := Stacks.ChernCap42.firstChernClassCapOfInvertible_closedSubscheme_eq_zeroScheme
    (fieldChowSituation k) p (𝟙 X) 0 L t hY hD hs
  show chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) p
      (IsLocalRing.closedPoint k)
      (firstChernClassCapOfInvertible (fieldChowSituation k) p 0 L
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p (𝟙 X) (0 + 1))) = _
  rw [h02SQ]
  exact chowDegree_mk (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) p
    (IsLocalRing.closedPoint k) _

/-- **The Chern side of the degree formula on an integral scheme**: for `ℒ` invertible on an
integral `X` of dimension at most one and a nonzero section `t` of `(𝟙 X)^*ℒ`,
`deg(c₁(ℒ) ∩ [X]_1) = deg([Z(t)]_0)`. -/
public theorem curveChernDegree_eq_cycleDegree_zeroScheme_of_isIntegral [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      ((Scheme.Modules.pullback (𝟙 X)).obj L)]
    (t : ((Scheme.Modules.pullback (𝟙 X)).obj L).sections) (ht : t.eval (op ⊤) ≠ 0) :
    curveChernDegree k p hdim (firstChernComponentCycleRule (fieldChowSituation k) p 0 L) =
      cycleDegree (fieldChowSituation k) p (IsLocalRing.closedPoint k)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
          ((Stacks.Divisors.zeroScheme X ((Scheme.Modules.pullback (𝟙 X)).obj L)
            (t.eval (op ⊤))).subschemeι ≫ 𝟙 X) 0) := by
  have hD : Stacks.Divisors.IsEffectiveCartierDivisor
      (Stacks.Divisors.zeroScheme X ((Scheme.Modules.pullback (𝟙 X)).obj L) (t.eval (op ⊤))) :=
    Stacks.Divisors.isEffectiveCartierDivisor_zeroScheme_of_eval_top_ne_zero X _ t ht
  refine curveChernDegree_eq_cycleDegree_zeroScheme k p hdim L t ?_ ?_
    fun ξ _ => injective_stalkFunctor_map_unitHomEquiv_symm_of_eval_top_ne_zero
      ((Scheme.Modules.pullback (𝟙 X)).obj L) t ht _
  · exact schemeDeltaDimension_fieldChowSituation_le_of_topologicalKrullDim_le k p (𝟙 X) 1 hdim
  · exact schemeDeltaDimension_divisor_le_zero k (𝟙 X ≫ p) hdim _

/-- Equal quasi-coherent ideal sheaves have equal associated cycles. -/
private theorem cycleAssociatedToClosedSubscheme_congr_ideal
    {C : Stacks.Chow.ChowSituation.{u}} {Y : Scheme.{u}} (q : Y ⟶ C.S) [LocallyOfFiniteType q]
    {I J : Y.IdealSheafData} (hIJ : I = J) (d : ℤ)
    [LocallyOfFiniteType (I.subschemeι ≫ q)] [LocallyOfFiniteType (J.subschemeι ≫ q)] :
    cycleAssociatedToClosedSubscheme C q I.subschemeι d =
      cycleAssociatedToClosedSubscheme C q J.subschemeι d := by
  subst hIJ
  rfl

/-- Equal closed immersions have equal associated cycles. -/
private theorem cycleAssociatedToClosedSubscheme_congr_hom
    {C : Stacks.Chow.ChowSituation.{u}} {Y Z : Scheme.{u}} (q : Y ⟶ C.S) [LocallyOfFiniteType q]
    {a b : Z ⟶ Y} [IsClosedImmersion a] [IsClosedImmersion b] (hab : a = b) (d : ℤ)
    [LocallyOfFiniteType (a ≫ q)] [LocallyOfFiniteType (b ≫ q)] :
    cycleAssociatedToClosedSubscheme C q a d = cycleAssociatedToClosedSubscheme C q b d := by
  subst hab
  rfl

/-- **The degree of the zero cycle of a nonzero section is the dimension of `H⁰` of the module
restricted to the zero scheme**: for `ℒ` invertible on an integral `X` of dimension at most one
and a nonzero global section `s`, `deg([Z(s)]_0) = dim_k H⁰(Z(s), ℒ|_{Z(s)})`. -/
public theorem degree_zeroCycle_zeroScheme_eq_finrank_cohomologyOverField [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hs : s.eval (op ⊤) ≠ 0) :
    cycleDegree (fieldChowSituation k) p (IsLocalRing.closedPoint k)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
          (Stacks.Divisors.zeroScheme X L (s.eval (op ⊤))).subschemeι 0) =
      (Module.finrank k (cohomologyOverField k
        ((Stacks.Divisors.zeroScheme X L (s.eval (op ⊤))).subschemeι ≫ p)
        ((Scheme.Modules.pullback
          (Stacks.Divisors.zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L) 0) : ℤ) := by
  have : Stacks.Divisors.IsEffectiveCartierDivisor
      (Stacks.Divisors.zeroScheme X L (s.eval (op ⊤))) :=
    Stacks.Divisors.isEffectiveCartierDivisor_zeroScheme_of_eval_top_ne_zero X L s hs
  have : IsFinite ((Stacks.Divisors.zeroScheme X L (s.eval (op ⊤))).subschemeι ≫ p) :=
    isFinite_divisorSubscheme k p hdim _
  obtain ⟨e⟩ := nonempty_pullback_zeroScheme_iso_unit k p hdim L s hs
  rw [finrank_cohomologyOverField_eq_of_iso k _ e 0,
    finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections k _]
  exact cycleDegree_cycleAssociatedToClosedSubscheme_eq_finrank_globalSections k p _
    (schemeDeltaDimension_divisor_le_zero k p hdim _) _

/-- **The degree formula [Stacks, Tag 0BRY] for an invertible module with a nonzero global
section on a proper integral curve.** For `X` integral and proper of dimension at most one over
`k`, `ℒ` invertible with a nonzero global section `s`, and `t` the section of `(𝟙 X)^*ℒ`
corresponding to `s`,

`deg(ℒ) = deg(c₁(ℒ) ∩ [X]_1)`. -/
public theorem invertibleCurveDegree_eq_curveChernDegree_of_isIntegral [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      ((Scheme.Modules.pullback (𝟙 X)).obj L)]
    (s : L.sections) (hs : s.eval (op ⊤) ≠ 0)
    (t : ((Scheme.Modules.pullback (𝟙 X)).obj L).sections)
    (ht : Scheme.Modules.Hom.app ((Scheme.Modules.pullbackId X).app L).hom ⊤ (t.eval (op ⊤)) =
      s.eval (op ⊤)) :
    @invertibleCurveDegree k _ X p _ hdim L hL =
      curveChernDegree k p hdim (firstChernComponentCycleRule (fieldChowSituation k) p 0 L) := by
  have hdeg := degree_zeroCycle_zeroScheme_eq_finrank_cohomologyOverField k p hdim L s hs
  have hZeq : Stacks.Divisors.zeroScheme X ((Scheme.Modules.pullback (𝟙 X)).obj L)
      (t.eval (op ⊤)) = Stacks.Divisors.zeroScheme X L (s.eval (op ⊤)) :=
    AlgebraicGeometry.zeroScheme_eq_of_iso ((Scheme.Modules.pullbackId X).app L) ht
  have htne : t.eval (op ⊤) ≠ 0 := fun h ↦ hs (by rw [← ht, h]; exact map_zero _)
  have h1 := curveChernDegree_eq_cycleDegree_zeroScheme_of_isIntegral k p hdim L t htne
  have hcyc := (cycleAssociatedToClosedSubscheme_congr_hom (C := fieldChowSituation k) p
      (Category.comp_id (Stacks.Divisors.zeroScheme X ((Scheme.Modules.pullback (𝟙 X)).obj L)
        (t.eval (op ⊤))).subschemeι) 0).trans
    (cycleAssociatedToClosedSubscheme_congr_ideal (C := fieldChowSituation k) p hZeq 0)
  have h2 := congrArg (cycleDegree (fieldChowSituation k) p (IsLocalRing.closedPoint k)) hcyc
  exact (invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_zeroScheme k p hdim L s hs
    (forall_finiteDimensional_cohomologyOverField_unit k p)).trans
    ((h1.trans (h2.trans hdeg)).symm)

/-- **Equation [Stacks, Tag 0BRY] for an invertible module with a nonzero global section on a
proper integral curve**, with the degree of `ℒ` taken as `AlgebraicGeometry.curveDegree` at rank
one. -/
public theorem curveDegree_one_eq_curveChernDegree_of_isIntegral [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      ((Scheme.Modules.pullback (𝟙 X)).obj L)]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1]
    (s : L.sections) (hs : s.eval (op ⊤) ≠ 0)
    (t : ((Scheme.Modules.pullback (𝟙 X)).obj L).sections)
    (ht : Scheme.Modules.Hom.app ((Scheme.Modules.pullbackId X).app L).hom ⊤ (t.eval (op ⊤)) =
      s.eval (op ⊤)) :
    curveDegree k p hdim L 1 =
      curveChernDegree k p hdim (firstChernComponentCycleRule (fieldChowSituation k) p 0 L) :=
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := hL
  (invertibleCurveDegree_eq_curveDegree_one k p hdim L).symm.trans
    (invertibleCurveDegree_eq_curveChernDegree_of_isIntegral k p hdim L s hs t ht)

/-- **Riemann-Roch, equation [Stacks, Tag 0BRZ], for an invertible module with a nonzero global
section on a proper integral curve**:

`χ(X, ℒ) = deg(c₁(ℒ) ∩ [X]_1) + χ(X, 𝒪_X)`. -/
public theorem eulerCharacteristic_eq_curveChernDegree_add_of_isIntegral [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      ((Scheme.Modules.pullback (𝟙 X)).obj L)]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] [L.IsCoherent]
    [(SheafOfModules.unit X.ringCatSheaf).IsCoherent]
    (s : L.sections) (hs : s.eval (op ⊤) ≠ 0)
    (t : ((Scheme.Modules.pullback (𝟙 X)).obj L).sections)
    (ht : Scheme.Modules.Hom.app ((Scheme.Modules.pullbackId X).app L).hom ⊤ (t.eval (op ⊤)) =
      s.eval (op ⊤)) :
    eulerCharacteristic k p L =
      curveChernDegree k p hdim (firstChernComponentCycleRule (fieldChowSituation k) p 0 L) +
        eulerCharacteristic k p (SheafOfModules.unit X.ringCatSheaf) :=
  eulerCharacteristic_eq_curveChernDegree_add_of_isInvertible k p hdim L
    (curveDegree_one_eq_curveChernDegree_of_isIntegral k p hdim L s hs t ht)

end AlgebraicGeometry

end
