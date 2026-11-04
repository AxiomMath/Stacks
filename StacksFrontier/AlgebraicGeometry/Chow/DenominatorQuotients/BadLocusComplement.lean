module

public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentRatio
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.StalkFractionalIdeal

/-!
# Off the exceptional locus the local ratio is a unit and the component divisor vanishes

The exceptional subset of [Stacks, Tag 02P2] is
`AlgebraicGeometry.denominatorBadLocus`, the union of the supports of the cokernels of the two
projections of the ideal of denominators. At a point `ξ` outside it both projections are
surjective on stalks, so

* the germs of the ideal of denominators are all of `𝒪_{X, ξ}`, which by the colon-ideal
  presentation of [Stacks, Tag 02P0] says `germ(a) = v · germ(b)` for some `v`; and
* the germs of the values of multiplication by `s` are all of `ℒ_ξ`, which by the fractional
  colon-ideal presentation says `germ(b) = u · germ(a)` for some `u`.

Since `germ(b)` is a nonzerodivisor the two give `u · v = 1`, so the local ratio `a / b` is a
*unit* of `𝒪_{X, ξ}`: outside the exceptional locus `s` is an honest trivialization of `ℒ`. Its
restriction to a component through `ξ` is then a unit too, and the order of vanishing of a unit
is zero — so the coefficient at `ξ` of `(Xη → X)_* div_{ℒ|_{Xη}}(sη)` vanishes.

That is the second half of the coefficientwise comparison of part (4) of
[Stacks, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW): at a point of the exceptional
locus the comparison is the coefficient identity, and at a point outside it both sides are zero —
the left because both quotients are supported on the exceptional locus, the right by the result
below.

## Main results

* `Stacks.Chow.surjective_stalkLinearMap_of_notMem_supp_cokernel` — off the support of the
  cokernel the stalk map of a morphism of sheaves of modules is surjective.
* `Stacks.Chow.mem_germs_of_notMem_supp_cokernel` and
  `Stacks.Chow.mem_mulGerms_of_notMem_supp_cokernel` — consequently every germ is a germ of the
  ideal of denominators, resp. a value of multiplication by `s`.
* `Stacks.Chow.exists_isUnit_germ_mul_eq_of_notMem_denominatorBadLocus` — **the local ratio is a
  unit off the exceptional locus**.
* `Stacks.Chow.componentDivisorCycle_apply_eq_zero_of_notMem_denominatorBadLocus` — the
  coefficient of the pushforward of the component divisor vanishes off the exceptional locus.

## Implementation notes

`AlgebraicGeometry.denominatorBadLocus` is stated with
`AlgebraicGeometry.SheafOfModules.moduleSheafOfModules _ |>.supp`, and the surjectivity criterion
is re-proved here: the corresponding statement in
`StacksFrontier/AlgebraicGeometry/Meromorphic/IdealTimesModule.lean` is `private`. The proof is the
exactness of the stalk functor — the stalk of the cokernel is the cokernel of the stalk map, and
a cokernel that is zero makes the map epi.

The two colon-ideal presentations are those of
`Stacks.Chow.exists_affineOpen_sectionRatio_denominator_presentations`, so the same chart carries
the ratio equation and both presentations; that is what lets the unit found here be the one the
order computation of `StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentRatio`
uses.

## References

* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 02P2](https://stacks.math.columbia.edu/tag/02P2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Order Topology
open TopologicalSpace
open Stacks.DenominatorIdeal (sectionMap toK)

universe u

namespace Stacks.Chow

/-! ### Surjectivity of a stalk map off the support of the cokernel -/

/-- **Off the support of the cokernel the stalk map is surjective.** The stalk functor is exact,
so the stalk of the cokernel is the cokernel of the stalk map; that cokernel being zero makes the
stalk map an epimorphism of modules, hence surjective. -/
theorem surjective_stalkLinearMap_of_notMem_supp_cokernel {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) (x : X)
    (hx : x ∉ (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules (cokernel φ)).supp) :
    Function.Surjective (AlgebraicGeometry.stalkLinearMap M N φ x) := by
  let T := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x
  have hx' : x ∉ _root_.SheafOfModules.supp (cokernel φ) := fun hs =>
    hx (by rwa [_root_.SheafOfModules.supp_eq_moduleSheaf_supp])
  have hzero : IsZero (T.obj (cokernel φ)) := ModuleCat.isZero_iff_subsingleton.mpr
    ⟨fun α β => sub_eq_zero.mp (Classical.byContradiction fun hne => hx' ⟨α - β, hne⟩)⟩
  exact (ModuleCat.epi_iff_surjective (T.map φ)).mp <| Abelian.epi_of_cokernel_π_eq_zero _
    ((hzero.of_iso (PreservesCokernel.iso T φ).symm).eq_of_tgt _ _)

/-! ### Every germ is a denominator germ and a value of multiplication by the section -/

variable (X : Scheme.{u}) (L : X.Modules)
  (s : AlgebraicGeometry.MeromorphicSection.{u, u} X.sheaf L)

/-- Off the support of the cokernel of the inclusion of the ideal of denominators, every element
of the local ring is the germ of a denominator. -/
theorem mem_germs_of_notMem_supp_cokernel {x : X}
    (hx : x ∉ (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules
      (cokernel (AlgebraicGeometry.denominatorIdealι X L s))).supp)
    (z : X.presheaf.stalk x) : z ∈ DenominatorStalk.germs X L s x := by
  obtain ⟨c, hc⟩ := surjective_stalkLinearMap_of_notMem_supp_cokernel
    (DenominatorStalk.denominatorIdealιDecl X L s) x hx
    (Stacks.UnitStalk.unitStalkLinearEquiv X x z)
  exact (DenominatorStalk.mem_germs_iff_unitStalkLinearEquiv_mem_range X L s x z).mpr ⟨c, hc⟩

/-- Off the support of the cokernel of multiplication by `s` on the ideal of denominators, every
element of the stalk of `ℒ` is the germ of a value of that multiplication. -/
theorem mem_mulGerms_of_notMem_supp_cokernel {x : X}
    (hx : x ∉ (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules
      (cokernel (AlgebraicGeometry.denominatorIdealMul X L s))).supp)
    (z : L.presheaf.stalk x) : z ∈ DenominatorStalk.mulGerms X L s x := by
  obtain ⟨c, hc⟩ := surjective_stalkLinearMap_of_notMem_supp_cokernel
    (M := DenominatorStalk.denominatorIdealDecl X L s) (N := L)
    (AlgebraicGeometry.denominatorIdealMul X L s) x hx z
  obtain ⟨W, hxW, d, rfl⟩ :=
    (DenominatorStalk.denominatorIdealDecl X L s).presheaf.exists_germ_eq c
  exact ⟨W, hxW, _, ⟨d, rfl⟩,
    (AlgebraicGeometry.stalkLinearMap_germ (DenominatorStalk.denominatorIdealDecl X L s) L
      (AlgebraicGeometry.denominatorIdealMul X L s) W x hxW d).symm.trans hc⟩

/-! ### The local ratio is a unit off the exceptional locus -/

/-- **Off the exceptional locus of [Stacks, Tag 02P2] the local ratio of `s` is a unit.** The two
colon-ideal presentations of the ideal of denominators give `germ(a) = v · germ(b)` and
`germ(b) = u · germ(a)`; as `germ(b)` is a nonzerodivisor, `u · v = 1`. -/
theorem exists_isUnit_germ_mul_eq_of_notMem_denominatorBadLocus
    {V : X.Opens} (hV : IsAffineOpen V) {a b : Γ(X, V)} {e : Γ(L, V)}
    (hιpres : ∀ g : Γ(X, V),
      Set.range (ConcreteCategory.hom
          ((Stacks.DenominatorIdeal.denominatorIdealι X L s).val.app (op (X.basicOpen g)))) =
        {h : Γ(X, X.basicOpen g) | ∃ v : Γ(X, X.basicOpen g),
          h * algebraMap Γ(X, V) Γ(X, X.basicOpen g) a =
            algebraMap Γ(X, V) Γ(X, X.basicOpen g) b * v})
    (hmulpres : ∀ g : Γ(X, V),
      Set.range (ConcreteCategory.hom
          ((AlgebraicGeometry.denominatorIdealMul X L s).val.app (op (X.basicOpen g)))) =
        (fun y : Γ(X, X.basicOpen g) =>
            y • L.presheaf.map (homOfLE (X.basicOpen_le g)).op e) ''
          {y : Γ(X, X.basicOpen g) | ∃ w : Γ(X, X.basicOpen g),
            y * algebraMap Γ(X, V) Γ(X, X.basicOpen g) b =
              algebraMap Γ(X, V) Γ(X, X.basicOpen g) a * w})
    {ξ : X} (hξV : ξ ∈ V)
    (hbas : Stacks.Divisors.IsStalkBasis L ξ ((L.presheaf.germ V ξ hξV).hom e))
    (hb : (X.presheaf.germ V ξ hξV).hom b ∈ nonZeroDivisors (X.presheaf.stalk ξ))
    (hξ : ξ ∉ denominatorBadLocus X L s) :
    ∃ v : X.presheaf.stalk ξ, IsUnit v ∧
      (X.presheaf.germ V ξ hξV).hom a = v * (X.presheaf.germ V ξ hξV).hom b := by
  have hone : (1 : X.presheaf.stalk ξ) ∈
      Ideal.denominatorIdeal ((X.presheaf.germ V ξ hξV).hom a)
        ((X.presheaf.germ V ξ hξV).hom b) := by
    rw [← SetLike.mem_coe, ← DenominatorStalk.germs_eq_coe_denominatorIdeal X L s hV hιpres hξV]
    exact mem_germs_of_notMem_supp_cokernel X L s (fun h => hξ (Or.inl h)) 1
  obtain ⟨v, hv⟩ := Ideal.mem_denominatorIdeal_iff.mp hone
  have hav : (X.presheaf.germ V ξ hξV).hom a = v * (X.presheaf.germ V ξ hξV).hom b := by
    rw [← hv, one_mul]
  have honemul : (1 : X.presheaf.stalk ξ) ∈
      Ideal.fractionalProductIdeal ((X.presheaf.germ V ξ hξV).hom a)
        ((X.presheaf.germ V ξ hξV).hom b) := by
    have hcoord := (DenominatorStalk.mem_mulGerms_iff_coord_mem X L s hV hmulpres hξV hbas
      ((L.presheaf.germ V ξ hξV).hom e)).mp
        (mem_mulGerms_of_notMem_supp_cokernel X L s (fun h => hξ (Or.inr h)) _)
    rwa [show hbas.coord ((L.presheaf.germ V ξ hξV).hom e) = 1 from
      Eq.trans (congrArg hbas.coord (one_smul (X.presheaf.stalk ξ) _).symm)
        (hbas.coord_smul 1)] at hcoord
  obtain ⟨u, hu⟩ := Ideal.mem_fractionalProductIdeal_iff.mp honemul
  refine ⟨v, IsUnit.of_mul_eq_one u
    (sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hb).2 (v * u - 1) ?_)), hav⟩
  linear_combination (-u) * hav - hu

/-! ### The component divisor vanishes off the exceptional locus -/

/-- **A unit ratio restricts to a unit ratio on a closed subscheme, so the two orders of vanishing
there agree.** The point `z` of the subscheme and the point `ξ` of `X` are kept independent, tied
only by `hz`, because `z` is produced from `ξ` and neither can be rewritten; see the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentOrderIdentification`. -/
theorem ord_subschemeι_app_eq_of_isUnit (Z : X.IdealSheafData)
    [AlgebraicGeometry.IsIntegral Z.subscheme] [IsLocallyNoetherian Z.subscheme]
    (z : Z.subscheme) {ξ : X} (hz : Z.subschemeι z = ξ) (hco : Order.coheight z = 1)
    {V : X.Opens} (hξV : ξ ∈ V) [Nonempty (Z.subschemeι ⁻¹ᵁ V : Z.subscheme.Opens)]
    {a b : Γ(X, V)} {v : X.presheaf.stalk ξ} (hv : IsUnit v)
    (hav : (X.presheaf.germ V ξ hξV).hom a = v * (X.presheaf.germ V ξ hξV).hom b)
    (hBne : Z.subscheme.germToFunctionField (Z.subschemeι ⁻¹ᵁ V)
      ((Z.subschemeι.app V).hom b) ≠ 0) :
    Z.subscheme.ord (Z.subscheme.germToFunctionField (Z.subschemeι ⁻¹ᵁ V)
          ((Z.subschemeι.app V).hom a)) z =
      Z.subscheme.ord (Z.subscheme.germToFunctionField (Z.subschemeι ⁻¹ᵁ V)
        ((Z.subschemeι.app V).hom b)) z := by
  subst hz
  have hzV : z ∈ (Z.subschemeι ⁻¹ᵁ V : Z.subscheme.Opens) := hξV
  have hvZ : IsUnit ((Z.subschemeι.stalkMap z).hom v) := hv.map (Z.subschemeι.stalkMap z).hom
  have hAB : Z.subscheme.germToFunctionField (Z.subschemeι ⁻¹ᵁ V)
        ((Z.subschemeι.app V).hom a) =
      algebraMap (Z.subscheme.presheaf.stalk z) Z.subscheme.functionField
          ((Z.subschemeι.stalkMap z).hom v) *
        Z.subscheme.germToFunctionField (Z.subschemeι ⁻¹ᵁ V)
          ((Z.subschemeι.app V).hom b) := by
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField Z.subscheme hzV
        ((Z.subschemeι.app V).hom a),
      ← Scheme.algebraMap_germ_eq_germToFunctionField Z.subscheme hzV
        ((Z.subschemeι.app V).hom b),
      ← Scheme.Hom.germ_stalkMap_apply Z.subschemeι V z hξV a,
      ← Scheme.Hom.germ_stalkMap_apply Z.subschemeι V z hξV b, hav, map_mul, map_mul]
  rw [hAB, Scheme.ord_mul
      ((hvZ.map (algebraMap (Z.subscheme.presheaf.stalk z)
        Z.subscheme.functionField)).ne_zero) hBne,
    Scheme.ord_algebraMap_of_isUnit hco hvZ, zero_add]

/-- **The coefficient of `(Xη → X)_* div_{ℒ|_{Xη}}(sη)` vanishes off the exceptional locus.**
Outside `AlgebraicGeometry.denominatorBadLocus` the local ratio of `s` is a unit of the local
ring, so its restriction to the component is the image of a unit and the order of vanishing of
the image of a unit at a point of coheight one is zero. -/
theorem componentDivisorCycle_apply_eq_zero_of_notMem_denominatorBadLocus
    (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s) {k : ℤ} {ξ η : X}
    (hη : η ∈ genericPoints X)
    (hδη : relativeDimension C.dimensionFunction f η = k + 1)
    (hspec : η ⤳ ξ)
    (hδξ : relativeDimension C.dimensionFunction f ξ = k)
    (hmin : (integralComponentAt η).stalkIdeal ξ ∈ minimalPrimes (X.presheaf.stalk ξ))
    (hξ : ξ ∉ denominatorBadLocus X L s) :
    (componentDivisorCycle C f L s hL hs hη hδη).1 ξ = 0 := by
  have hNoeth := LocallyOfFiniteType.isLocallyNoetherian f
  have hint := isIntegral_integralComponentAt η
  have hLN := (integralComponentAt η).isLocallyNoetherian_subscheme
  obtain ⟨V, hξV, hVaff, a, b, e, ha, hb, hbas, hbt, hιpres, hmulpres⟩ :=
    exists_affineOpen_sectionRatio_denominator_presentations X L s hL hs ξ
  have hnz : ∀ {c : Γ(X, V)}, c ∈ nonZeroDivisors Γ(X, V) →
      (X.presheaf.germ V ξ hξV).hom c ∈ nonZeroDivisors (X.presheaf.stalk ξ) := fun hc =>
    Stacks.Divisors.germ_mem_nonZeroDivisors hVaff (isRegular_iff_mem_nonZeroDivisors.mpr hc) ξ hξV
  have ha' := hnz ha
  have hb' := hnz hb
  obtain ⟨v, hv, hav⟩ := exists_isUnit_germ_mul_eq_of_notMem_denominatorBadLocus X L s hVaff
    hιpres hmulpres hξV hbas hb' hξ
  obtain ⟨z, hz⟩ : ∃ w : (integralComponentAt η).subscheme,
      (integralComponentAt η).subschemeι w = ξ := by
    show ξ ∈ Set.range (integralComponentAt η).subschemeι.base
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt]
    exact specializes_iff_mem_closure.mp hspec
  have hzV : z ∈ ((integralComponentAt η).subschemeι ⁻¹ᵁ V :
      (integralComponentAt η).subscheme.Opens) := by
    show (integralComponentAt η).subschemeι.base z ∈ V
    rwa [hz]
  have hNE : Nonempty ((integralComponentAt η).subschemeι ⁻¹ᵁ V :
    (integralComponentAt η).subscheme.Opens) := ⟨⟨z, hzV⟩⟩
  have hgenV : genericPoint (integralComponentAt η).subscheme ∈
      ((integralComponentAt η).subschemeι ⁻¹ᵁ V : (integralComponentAt η).subscheme.Opens) := by
    show (integralComponentAt η).subschemeι.base
      (genericPoint (integralComponentAt η).subscheme) ∈ V
    rw [subschemeι_genericPoint_integralComponentAt η]
    exact hspec.mem_open V.isOpen hξV
  refine Eq.trans (ord_sub_eq_componentDivisorCycle_apply C f L s hL hs hη hδη z hz
    hδξ hmin hξV hbas hbt ha' hb').symm ?_
  rw [ord_subschemeι_app_eq_of_isUnit X (integralComponentAt η) z hz
      (coheight_eq_one_of_relativeDimension C f hδη z hz hδξ) hξV hv hav
      (germToFunctionField_subschemeι_app_ne_zero (integralComponentAt η) hξV hgenV hmin hb' z hz),
    sub_self]

end Stacks.Chow

end
