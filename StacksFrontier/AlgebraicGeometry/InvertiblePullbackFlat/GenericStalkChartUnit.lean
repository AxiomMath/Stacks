module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.GenericFibreChartUnit
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.GenericStalkComparison

/-!
# The penultimate paragraph of Tag 0BD7, read inside the function field

`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/GenericFibreChartUnit.lean` states the
penultimate paragraph of [Stacks, Tag 0BD7] at a point `x` as an equation `r s = g u` inside the
ring `Ideal.Fiber ⊥ 𝒪_{X, x}`, the source's `A ⊗_R K`. The first paragraph of the same proof
works instead inside the function field `K(X)`, where the meromorphic section lives. This file
moves the equation there, along the ring homomorphism
`AlgebraicGeometry.stalkFiberBotToGenericStalk` of
`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/GenericStalkComparison.lean`.

Nothing is lost in the move: that homomorphism was built with exactly these two defining
equations, one at each of the two `algebraMap`s occurring in the equation, so all three factors
keep their names and only the ambient ring changes.

The same homomorphism is then pinned down: the composite
`Ideal.Fiber ⊥ Γ(X, U) → Ideal.Fiber ⊥ 𝒪_{X, x} → K(X)` restricts on `Γ(X, U)` to the germ at the
generic point, and because the chart's generic fibre ring is a localization of `Γ(X, U)` that
one equation determines it. Any other description of the same composite — in particular one
reading a section of the generic fibre's structure sheaf through
`AlgebraicGeometry.genericFiberChartSections` — need only be checked on `Γ(X, U)`.

That second description is the one the first paragraph of the proof wants. The local ring of the
generic fibre at the point `x₀` lying over the generic point of `X` *is* `K(X)`, the inclusion of
the generic fibre being an isomorphism on local rings, and through that identification the
composite above is the germ at `x₀`. So the chart coordinate, read in `K(X)`, is the germ at `x₀`
of a section of the generic fibre — an element in which no ring of the chart occurs.

## Main results

* `AlgebraicGeometry.exists_isUnit_mul_eq_stalkFiberBotToGenericStalk`: the conclusion of the
  penultimate paragraph at `x`, as an equation in `K(X)`.
* `AlgebraicGeometry.stalkFiberBotToGenericStalk_chartFiberBotToStalkFiberBot_one_tmul`: the
  composite sends the image of `a ∈ Γ(X, U)` to `X.germToFunctionField U a`.
* `AlgebraicGeometry.eq_stalkFiberBotToGenericStalk_comp_chartFiberBotToStalkFiberBot`: that
  equation determines the composite.
* `AlgebraicGeometry.exists_fiberι_base_eq_genericPoint` and
  `AlgebraicGeometry.mem_genericFiberChartOpens_of_base_eq_genericPoint`: the point `x₀` of the
  generic fibre over the generic point of `X` exists and lies in the chart.
* `AlgebraicGeometry.genericFiberStalkIsoFunctionField`: the local ring of the generic fibre at
  `x₀` is `K(X)`.
* `AlgebraicGeometry.genericFiberStalkIsoFunctionField_inv_apply`: its inverse is
  `CategoryTheory.inv` of the stalk map followed by the specialization isomorphism — the form in
  which the named scalar of
  `AlgebraicGeometry.eq_smul_grpGerm_genericFiberTrivGenerator` appears.
* `stalkFiberBotToGenericStalk_chartFiberBotToStalkFiberBot_genericFiberChartSections`:
  **the composite is the germ at `x₀`**, read in `K(X)` through that identification.
* `AlgebraicGeometry.exists_isUnit_mul_eq_germ_generatorRatio`: hence the penultimate paragraph
  at `x` with its `s` displayed as that germ.

## Implementation notes

The two rewrites are done backwards, on the goal, and the two `map_mul`s forwards, as terms with
their expected type already fixed by the goal. `rw [map_mul] at` the hypothesis instead is a
deterministic timeout at 200000 heartbeats: the general lemma has to unify its
`MulHomClass` argument against the tensor-product ring before it can fire.

No goal mentioning `AlgebraicGeometry.genericFiberChartOpens` admits `rw` or `simp`, for the
reason `GenericFibreChartUnit.lean` records. The germ identification below is therefore an
`Eq.trans` chain of two morphism equations —
`TopCat.Presheaf.germ_stalkSpecializes` and `AlgebraicGeometry.germ_stalkMap_appLE`, neither of
which mentions the chart — closed by one `congrArg` with the motive written out; and the
inverse of `AlgebraicGeometry.genericFiberChartSections` is introduced by `obtain` with its
defining equation rather than by `set`, so that no occurrence in the goal is ever abstracted.

No tag attribute: the statement carries an affine chart and a point of `X`, neither of which
[Stacks, Tag 0BD7] has.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open Stacks.RingedSpace Stacks.SheafOfModules
open scoped TensorProduct

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsIntegral X] [IsIntegral Y] {x : X}
  {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U)
  (e : U ≤ f ⁻¹ᵁ V) (hx : x ∈ U)
  (L : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace))
  (hgen : AlgebraicGeometry.SheafOfModules.IsTrivial
    (f.fiber (genericPoint Y)).presheaf
    (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
      (f.fiber (genericPoint Y)).IsSheaf)
    ((Scheme.Modules.pullback (f.fiberι (genericPoint Y))).obj L))
  (hL : IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L)
  (genU : GeneratorSections X.toRingedSpace L U)

/-- **The penultimate paragraph of [Stacks, Tag 0BD7] at a point, inside `K(X)`.** The equation
`r s = g u` of `AlgebraicGeometry.exists_isUnit_mul_eq_genericFiberChartCoord`, carried from
`Ideal.Fiber ⊥ 𝒪_{X, x}` into the function field; `g` and `r` are still nonzero elements of
`𝒪_{Y, f x}` and `u` still a unit of `𝒪_{X, x}`. -/
theorem exists_isUnit_mul_eq_stalkFiberBotToGenericStalk [IsNormal Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (hfib : ∀ y : Y, IsIntegral (f.fiber y)) :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    letI : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    letI : Algebra ↑(Y.presheaf.stalk (f x)) X.functionField :=
      ((algebraMap ↑(X.presheaf.stalk x) X.functionField).comp
        (algebraMap ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x))).toAlgebra
    letI : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
    letI : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
    ∃ (g r : ↑(Y.presheaf.stalk (f x))) (u : ↑(X.presheaf.stalk x)),
      g ≠ 0 ∧ r ≠ 0 ∧ IsUnit u ∧
        algebraMap ↑(Y.presheaf.stalk (f x)) X.functionField r
            * stalkFiberBotToGenericStalk f x
              (chartFiberBotToStalkFiberBot f hV e hx
                (genericFiberChartCoord f hV hU e hx L hgen hL genU)) =
          algebraMap ↑(Y.presheaf.stalk (f x)) X.functionField g
            * algebraMap ↑(X.presheaf.stalk x) X.functionField u := by
  let : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  let : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
  let : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
  let : Algebra ↑(X.presheaf.stalk x)
      ((⊥ : Ideal ↑(Y.presheaf.stalk (f x))).Fiber ↑(X.presheaf.stalk x)) :=
    Algebra.TensorProduct.rightAlgebra
  obtain ⟨g, r, u, hg, hr, hu, heq⟩ :=
    exists_isUnit_mul_eq_genericFiberChartCoord f hV hU e hx L hgen hL genU hfib
  refine ⟨g, r, u, hg, hr, hu, ?_⟩
  have h1 := congrArg ⇑(stalkFiberBotToGenericStalk f x) heq
  rw [← stalkFiberBotToGenericStalk_algebraMap_base f x r,
    ← stalkFiberBotToGenericStalk_algebraMap_base f x g,
    ← stalkFiberBotToGenericStalk_algebraMap_stalk f x u]
  exact (map_mul _ _ _).symm.trans (h1.trans (map_mul _ _ _))

/-- **The defining equation of the chart-to-function-field map.** The composite
`Ideal.Fiber ⊥ Γ(X, U) → Ideal.Fiber ⊥ 𝒪_{X, x} → K(X)` sends the image of a section `a` of `ℒ`'s
structure sheaf on `U` to the germ of `a` at the generic point of `X`. -/
theorem stalkFiberBotToGenericStalk_chartFiberBotToStalkFiberBot_one_tmul (a : ↑Γ(X, U)) :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    letI : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    letI : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
    letI : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
    letI : Nonempty U := ⟨⟨x, hx⟩⟩
    stalkFiberBotToGenericStalk f x (chartFiberBotToStalkFiberBot f hV e hx
        ((1 : (⊥ : Ideal ↑Γ(Y, V)).ResidueField) ⊗ₜ[↑Γ(Y, V)] a))
      = X.germToFunctionField U a := by
  let : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  let : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
  let : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  let : Algebra ↑(X.presheaf.stalk x)
      ((⊥ : Ideal ↑(Y.presheaf.stalk (f x))).Fiber ↑(X.presheaf.stalk x)) :=
    Algebra.TensorProduct.rightAlgebra
  rw [chartFiberBotToStalkFiberBot_one_tmul f hV e hx a]
  exact (stalkFiberBotToGenericStalk_algebraMap_stalk f x ((X.presheaf.germ U x hx).hom a)).trans
    (Scheme.algebraMap_germ_eq_germToFunctionField X hx a)

/-- **That equation determines the map.** `Ideal.Fiber ⊥ Γ(X, U)` is the localization of
`Γ(X, U)` at the nonzero elements of `Γ(Y, V)` (`IsLocalization.tensorRight`), so a ring
homomorphism out of it that restricts to `AlgebraicGeometry.Scheme.germToFunctionField` on
`Γ(X, U)` is the composite of
`AlgebraicGeometry.chartFiberBotToStalkFiberBot` with
`AlgebraicGeometry.stalkFiberBotToGenericStalk`. -/
theorem eq_stalkFiberBotToGenericStalk_comp_chartFiberBotToStalkFiberBot :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    letI : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    letI : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
    letI : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
    letI : Nonempty U := ⟨⟨x, hx⟩⟩
    ∀ φ : ((⊥ : Ideal ↑Γ(Y, V)).Fiber ↑Γ(X, U)) →+* X.functionField,
      (∀ a : ↑Γ(X, U),
          φ ((1 : (⊥ : Ideal ↑Γ(Y, V)).ResidueField) ⊗ₜ[↑Γ(Y, V)] a)
            = X.germToFunctionField U a) →
        φ = (stalkFiberBotToGenericStalk f x).comp (chartFiberBotToStalkFiberBot f hV e hx) := by
  let : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  let : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
  let : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  let : Algebra ↑Γ(X, U) ((⊥ : Ideal ↑Γ(Y, V)).Fiber ↑Γ(X, U)) :=
    Algebra.TensorProduct.rightAlgebra
  have : IsLocalization
      (Algebra.algebraMapSubmonoid ↑Γ(X, U) (nonZeroDivisors ↑Γ(Y, V)))
      ((⊥ : Ideal ↑Γ(Y, V)).Fiber ↑Γ(X, U)) :=
    IsLocalization.tensorRight ((⊥ : Ideal ↑Γ(Y, V)).ResidueField) (nonZeroDivisors ↑Γ(Y, V))
  intro φ hφ
  refine IsLocalization.ringHom_ext
    (Algebra.algebraMapSubmonoid ↑Γ(X, U) (nonZeroDivisors ↑Γ(Y, V))) ?_
  ext a
  exact (hφ a).trans
    (stalkFiberBotToGenericStalk_chartFiberBotToStalkFiberBot_one_tmul f hV e hx a).symm

omit [Flat f] in
/-- **The chart of the generic fibre contains the point over the generic point of `X`.** `U` is a
nonempty open of an irreducible space, so the generic point of `X` lies in it, and the chart is
the whole of the part of the generic fibre lying over `U`. -/
theorem mem_genericFiberChartOpens_of_base_eq_genericPoint (x₀ : f.fiber (genericPoint Y))
    (hx₀ : (f.fiberι (genericPoint Y)).base x₀ = genericPoint X) :
    x₀ ∈ genericFiberChartOpens f hV hU e hx :=
  mem_genericFiberChartOpens f hV hU e hx x₀ (by
    rw [hx₀]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩)

omit [Flat f] in
/-- **The generic point of `X` lies in the generic fibre**, for a surjective `f`. This is what
makes the hypothesis `hx₀` below satisfiable. -/
theorem exists_fiberι_base_eq_genericPoint (hsurj : Function.Surjective f.base) :
    ∃ x₀ : f.fiber (genericPoint Y), (f.fiberι (genericPoint Y)).base x₀ = genericPoint X :=
  genericPoint_mem_range_fiberι_genericPoint f hsurj

/-- **The local ring of the generic fibre at a point over the generic point of `X` is `K(X)`.**
The inclusion of the generic fibre is an isomorphism on local rings
(`AlgebraicGeometry.bijective_stalkMap_fiberι_of_mem`), and the point of `X` below `x₀` is the
generic point. -/
def genericFiberStalkIsoFunctionField (x₀ : f.fiber (genericPoint Y))
    (hx₀ : (f.fiberι (genericPoint Y)).base x₀ = genericPoint X) :
    X.functionField ≅ (f.fiber (genericPoint Y)).presheaf.stalk x₀ :=
  haveI : IsIso ((f.fiberι (genericPoint Y)).stalkMap x₀) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (bijective_stalkMap_fiberι_of_mem f (maximalIdeal_stalk_genericPoint_eq_bot Y) x₀)
  X.presheaf.stalkCongr (Inseparable.of_eq hx₀.symm) ≪≫
    asIso ((f.fiberι (genericPoint Y)).stalkMap x₀)

omit [Flat f] in
/-- **The inverse of `AlgebraicGeometry.genericFiberStalkIsoFunctionField`, factored.** It is
`CategoryTheory.inv` of the stalk map of the fibre inclusion followed by the specialization
isomorphism of `𝒪_X` between `x₀`'s image and the generic point of `X`. -/
theorem genericFiberStalkIsoFunctionField_inv_apply (x₀ : f.fiber (genericPoint Y))
    (hx₀ : (f.fiberι (genericPoint Y)).base x₀ = genericPoint X)
    (w : (f.fiber (genericPoint Y)).presheaf.stalk x₀) :
    haveI : IsIso (((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.stalkMap x₀) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr
        (bijective_stalkMap_fiberι_of_mem f (maximalIdeal_stalk_genericPoint_eq_bot Y) x₀)
    (genericFiberStalkIsoFunctionField f x₀ hx₀).inv w =
      (X.presheaf.stalkCongr (Inseparable.of_eq hx₀)).hom
        (inv (((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.stalkMap x₀) w) := by
  have : IsIso (((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.stalkMap x₀) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (bijective_stalkMap_fiberι_of_mem f (maximalIdeal_stalk_genericPoint_eq_bot Y) x₀)
  have hsplit : (genericFiberStalkIsoFunctionField f x₀ hx₀).inv =
      inv (((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.stalkMap x₀) ≫
        (X.presheaf.stalkCongr (Inseparable.of_eq hx₀)).hom := rfl
  exact (ConcreteCategory.congr_hom hsplit w).trans (CategoryTheory.comp_apply _ _ w)

omit [Flat f] in
/-- **The germ at `x₀` read through the chart.** A section `a` of `𝒪_X` on `U`, restricted to the
chart of the generic fibre and taken at `x₀`, is the germ of `a` at the generic point of `X`
carried over by `AlgebraicGeometry.genericFiberStalkIsoFunctionField`. -/
theorem genericFiberStalkIsoFunctionField_hom_germToFunctionField
    (x₀ : f.fiber (genericPoint Y))
    (hx₀ : (f.fiberι (genericPoint Y)).base x₀ = genericPoint X) (a : ↑Γ(X, U)) :
    letI : Nonempty U := ⟨⟨x, hx⟩⟩
    (genericFiberStalkIsoFunctionField f x₀ hx₀).hom (X.germToFunctionField U a) =
      ((f.fiber (genericPoint Y)).presheaf.germ (genericFiberChartOpens f hV hU e hx) x₀
          (mem_genericFiberChartOpens_of_base_eq_genericPoint f hV hU e hx x₀ hx₀))
        (((f.fiberι (genericPoint Y)).appLE U (genericFiberChartOpens f hV hU e hx)
          (genericFiberChartOpens_le f hV hU e hx)).hom a) := by
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  have hmemU : (f.fiberι (genericPoint Y)).base x₀ ∈ U :=
    genericFiberChartOpens_le f hV hU e hx
      (mem_genericFiberChartOpens_of_base_eq_genericPoint f hV hU e hx x₀ hx₀)
  have step1 : X.presheaf.germ U (genericPoint X)
        (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩) ≫
      (X.presheaf.stalkCongr (Inseparable.of_eq hx₀.symm)).hom =
        X.presheaf.germ U ((f.fiberι (genericPoint Y)).base x₀) hmemU :=
    X.presheaf.germ_stalkSpecializes _ (Inseparable.of_eq hx₀.symm).ge
  have step2 := germ_stalkMap_appLE (f.fiberι (genericPoint Y)) U
    (genericFiberChartOpens f hV hU e hx) (genericFiberChartOpens_le f hV hU e hx) x₀
    (mem_genericFiberChartOpens_of_base_eq_genericPoint f hV hU e hx x₀ hx₀)
  have hmor : X.germToFunctionField U ≫
        (genericFiberStalkIsoFunctionField f x₀ hx₀).hom =
      (f.fiberι (genericPoint Y)).appLE U (genericFiberChartOpens f hV hU e hx)
          (genericFiberChartOpens_le f hV hU e hx) ≫
        (f.fiber (genericPoint Y)).presheaf.germ (genericFiberChartOpens f hV hU e hx) x₀
          (mem_genericFiberChartOpens_of_base_eq_genericPoint f hV hU e hx x₀ hx₀) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (f.fiberι (genericPoint Y)).stalkMap x₀) step1).trans step2)
  exact ConcreteCategory.congr_hom hmor a

/-- **The chart coordinate read in the function field.** The composite
`Γ(X_ξ, chart) → Ideal.Fiber ⊥ Γ(X, U) → Ideal.Fiber ⊥ 𝒪_{X, x} → K(X)` carries a section `b` of
the generic fibre over the chart to the germ of `b` at the point `x₀` of the generic fibre over
the generic point of `X`, read in `K(X)` through
`AlgebraicGeometry.genericFiberStalkIsoFunctionField`.

With it the equation of `AlgebraicGeometry.exists_isUnit_mul_eq_stalkFiberBotToGenericStalk`
becomes an equation about that germ, whose left-hand side no longer mentions the chart. -/
theorem stalkFiberBotToGenericStalk_chartFiberBotToStalkFiberBot_genericFiberChartSections
    (b : ↑Γ(f.fiber (genericPoint Y), genericFiberChartOpens f hV hU e hx))
    (x₀ : f.fiber (genericPoint Y))
    (hx₀ : (f.fiberι (genericPoint Y)).base x₀ = genericPoint X) :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    letI : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    letI : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
    letI : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
    stalkFiberBotToGenericStalk f x
        (chartFiberBotToStalkFiberBot f hV e hx
          (genericFiberChartSections f hV hU e hx b)) =
      (genericFiberStalkIsoFunctionField f x₀ hx₀).inv
        ((f.fiber (genericPoint Y)).presheaf.germ (genericFiberChartOpens f hV hU e hx) x₀
          (mem_genericFiberChartOpens_of_base_eq_genericPoint f hV hU e hx x₀ hx₀) b) := by
  let : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  let : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
  let : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ↑Γ(f.fiber (genericPoint Y), genericFiberChartOpens f hV hU e hx) ≃+*
      ((⊥ : Ideal ↑Γ(Y, V)).Fiber ↑Γ(X, U)),
      ∀ t, ε t = genericFiberChartSections f hV hU e hx t :=
    ⟨RingEquiv.ofBijective _ (bijective_genericFiberChartSections f hV hU e hx), fun _ => rfl⟩
  have hcongr : ∀ {t t' : ↑Γ(f.fiber (genericPoint Y), genericFiberChartOpens f hV hU e hx)},
      t = t' → (genericFiberStalkIsoFunctionField f x₀ hx₀).inv
        ((f.fiber (genericPoint Y)).presheaf.germ (genericFiberChartOpens f hV hU e hx) x₀
          (mem_genericFiberChartOpens_of_base_eq_genericPoint f hV hU e hx x₀ hx₀) t) =
      (genericFiberStalkIsoFunctionField f x₀ hx₀).inv
        ((f.fiber (genericPoint Y)).presheaf.germ (genericFiberChartOpens f hV hU e hx) x₀
          (mem_genericFiberChartOpens_of_base_eq_genericPoint f hV hU e hx x₀ hx₀) t') :=
    fun h => by rw [h]
  have hφ : ∀ a : ↑Γ(X, U),
      (((genericFiberStalkIsoFunctionField f x₀ hx₀).inv.hom.comp
          (((f.fiber (genericPoint Y)).presheaf.germ (genericFiberChartOpens f hV hU e hx) x₀
            (mem_genericFiberChartOpens_of_base_eq_genericPoint f hV hU e hx x₀
              hx₀)).hom.comp ε.symm.toRingHom))
        ((1 : (⊥ : Ideal ↑Γ(Y, V)).ResidueField) ⊗ₜ[↑Γ(Y, V)] a))
        = X.germToFunctionField U a := by
    intro a
    have ha : ε.symm ((1 : (⊥ : Ideal ↑Γ(Y, V)).ResidueField) ⊗ₜ[↑Γ(Y, V)] a) =
        ((f.fiberι (genericPoint Y)).appLE U (genericFiberChartOpens f hV hU e hx)
          (genericFiberChartOpens_le f hV hU e hx)).hom a :=
      ε.symm_apply_eq.mpr
        (((hε _).trans (genericFiberChartSections_appLE_fiberι f hV hU e hx a)).symm)
    exact (hcongr ha).trans
      (((congrArg (genericFiberStalkIsoFunctionField f x₀ hx₀).inv
        (genericFiberStalkIsoFunctionField_hom_germToFunctionField f hV hU e hx x₀ hx₀
          a)).symm).trans (Iso.hom_inv_id_apply _ _))
  have hcomp := eq_stalkFiberBotToGenericStalk_comp_chartFiberBotToStalkFiberBot f hV e hx _ hφ
  refine (DFunLike.congr_fun hcomp (genericFiberChartSections f hV hU e hx b)).symm.trans
    (hcongr (((congrArg ε.symm (hε b)).symm).trans (ε.symm_apply_apply b)))

/-- **The penultimate paragraph of [Stacks, Tag 0BD7] at a point, about the named section.** The
equation `r s = g u` of
`AlgebraicGeometry.exists_isUnit_mul_eq_stalkFiberBotToGenericStalk` with `s` displayed as the
germ, at the point `x₀` of the generic fibre over the generic point of `X`, of the ratio of the
trivializing generator of `ℒ_ξ` against the chart's generator. The chart still fixes which
section is taken, but no ring of the chart occurs any longer. -/
theorem exists_isUnit_mul_eq_germ_generatorRatio [IsNormal Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (hfib : ∀ y : Y, IsIntegral (f.fiber y)) (x₀ : f.fiber (genericPoint Y))
    (hx₀ : (f.fiberι (genericPoint Y)).base x₀ = genericPoint X) :
    letI : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    letI : Algebra ↑(Y.presheaf.stalk (f x)) X.functionField :=
      ((algebraMap ↑(X.presheaf.stalk x) X.functionField).comp
        (algebraMap ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x))).toAlgebra
    ∃ (g r : ↑(Y.presheaf.stalk (f x))) (u : ↑(X.presheaf.stalk x)),
      g ≠ 0 ∧ r ≠ 0 ∧ IsUnit u ∧
        algebraMap ↑(Y.presheaf.stalk (f x)) X.functionField r
            * (genericFiberStalkIsoFunctionField f x₀ hx₀).inv
              ((f.fiber (genericPoint Y)).presheaf.germ
                (genericFiberChartOpens f hV hU e hx) x₀
                (mem_genericFiberChartOpens_of_base_eq_genericPoint f hV hU e hx x₀ hx₀)
                (generatorRatio _ (genericFiberChartOpens f hV hU e hx)
                  (genericFiberChartGenerator f hV hU e hx L hL genU)
                  (genericFiberTrivGenerator f L hgen
                    (genericFiberChartOpens f hV hU e hx)))) =
          algebraMap ↑(Y.presheaf.stalk (f x)) X.functionField g
            * algebraMap ↑(X.presheaf.stalk x) X.functionField u := by
  let : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Algebra ↑(Y.presheaf.stalk (f x)) X.functionField :=
    ((algebraMap ↑(X.presheaf.stalk x) X.functionField).comp
      (algebraMap ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x))).toAlgebra
  obtain ⟨g, r, u, hg, hr, hu, heq⟩ :=
    exists_isUnit_mul_eq_stalkFiberBotToGenericStalk f hV hU e hx L hgen hL genU hfib
  refine ⟨g, r, u, hg, hr, hu, Eq.trans (congrArg
    (fun t : X.functionField =>
      algebraMap ↑(Y.presheaf.stalk (f x)) X.functionField r * t) ?_) heq⟩
  exact (stalkFiberBotToGenericStalk_chartFiberBotToStalkFiberBot_genericFiberChartSections
    f hV hU e hx _ x₀ hx₀).symm

end AlgebraicGeometry

end
