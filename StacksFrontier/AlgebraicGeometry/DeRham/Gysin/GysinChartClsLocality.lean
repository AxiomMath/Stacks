module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.ChartDataExcision
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartData
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinCocycleBaseChange

/-!
# The class map of Tag 0G7Q along an open immersion, and its locality inside a chart

`Stacks.Gysin.chartClsHom` is the class map of [Stacks, Tag 0G7Q] of the equations of a chart
`W : X.Opens`, transported to the restriction to `W` of `Stacks.Gysin.gysinTarget` by the derived
excision of [Stacks, Tag 0G78].  Both of its factors exist along an **arbitrary** open immersion
of schemes — the class map because `Stacks.Perfect.SupportedFraction.supportedFractionSource` only
asks for global sections of the source, and the excision because of
`Stacks.Gysin.supportCohomologyOpenImmersionIso`.  This file states the class map at that
generality and proves its locality along an open of the chart.

## Main definitions

* `Stacks.Gysin.openImmersionClsHom`: **the class map of [Stacks, Tag 0G7Q] along an arbitrary
  open immersion of schemes**, landing in the restriction of `Stacks.Gysin.gysinTarget` along that
  immersion.  At the inclusion `AlgebraicGeometry.Scheme.Opens.ι` of an open subscheme it *is*
  `Stacks.Gysin.chartClsHom`, by `openImmersionClsHom_ι`, which is `rfl`.

## Main results

* `Stacks.Gysin.openImmersionClsHom_det`: **the determinant rule of [Stacks, Tag 0G7S] along an
  arbitrary open immersion.**  This is `Stacks.Gysin.chartClsHom_det` with the chart replaced by an
  open immersion; the proof is the same, since the excision does not mention the equations.
* `Stacks.Gysin.openImmersionClsHom_comp_ι`: **the class map of a chart is local along an open of
  the chart.**  For `W : X.Opens` and `U : W.toScheme.Opens`, the class map along the composite
  `U.ι ≫ W.ι` for the restricted equations is the class map of the chart `W`, restricted along
  `U.ι`, with `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` mediating.

## Implementation notes

**What this is.**  `openImmersionClsHom_comp_ι` is the open-immersion case of
[Stacks, Tag 0G7U] assembled onto the chart transport, for a leg that is itself the inclusion of
an open subscheme.  What the two-chart comparison of [Stacks, Tag 0G86] consumes is the same
statement for the chart-to-chart leg `AlgebraicGeometry.Scheme.homOfLE`, an open immersion that is
not the inclusion of an open subscheme; that is `Stacks.Gysin.openImmersionClsHom_comp` and
`Stacks.Gysin.chartClsHom_homOfLE` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinChartClsImmersionComp.lean`, this statement with
the inner leg taken to be an arbitrary open immersion.

**The chase.**  Every re-association is a helper stated at a variable category and applied with
`exact`: the two spellings of the category of modules on the source of the composite make `rw` on
`Category.assoc` and on `Functor.map_comp` fail as not type-correct at `implicit` transparency.
The two definitions are unfolded by definitional equality rather than rewritten, exactly as in
`Stacks.Gysin.chartClsHom_det`.

## References

* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G7S](https://stacks.math.columbia.edu/tag/0G7S)
* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open Stacks.Perfect.SupportedFraction
open Stacks.Perfect.CechDerivedSupport
open Stacks.Cohomology.SupportedComplexes

universe u

namespace Stacks.Gysin

attribute [local instance 10000] HasDerivedCategory.standard

variable {Y Z X S : Scheme.{u}}

/-! ### The class map along an arbitrary open immersion -/

/-- **The class map `c_{f₁, …, f_c}` of [Stacks, Tag 0G7Q] along an arbitrary open immersion of
schemes.**  For `g : Y ⟶ X` an open immersion and `f₁, …, f_c ∈ Γ(Y, 𝒪_Y)` whose common zero locus
lies over the closed subscheme, the class map of [Stacks, Tag 0G7Q] on `Y` lands, after the derived
excision `Stacks.Gysin.supportCohomologyOpenImmersionIso` of [Stacks, Tag 0G78], in the restriction
along `g` of the global target `Stacks.Gysin.gysinTarget`.

At `g := W.ι` this is `Stacks.Gysin.chartClsHom W`, by `openImmersionClsHom_ι`; the point of the
extra generality is that the chart-to-chart leg of [Stacks, Tag 0G86] is an open immersion which is
not the canonical inclusion of an open subscheme. -/
def openImmersionClsHom (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ)
    (g : Y ⟶ X) [IsOpenImmersion g] (f : Fin (d + 1) → Γ(Y, ⊤))
    (hT : IsClosed (g ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ g ⁻¹' Set.range i.base) :
    (Scheme.Modules.restrictFunctor g).obj
        (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))) ⟶
      (Scheme.Modules.restrictFunctor g).obj (gysinTarget i π (d + 1) p) :=
  haveI : (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms_natCast_add π p (d + 1)
  supportedFractionSource f
      ((Scheme.Modules.restrictFunctor g).obj
        (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))) hT hTf ≫
    (supportCohomologyOpenImmersionIso g (isClosed_range_base i) hT ((d + 1 : ℕ) : ℤ)
      (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))).inv

/-- **At the inclusion of an open subscheme the class map along an open immersion is the class map
of the chart.**  True by definition: the two excisions agree by
`Stacks.Gysin.supportCohomologyRestrictIso_eq_openImmersionIso`, itself `rfl`. -/
theorem openImmersionClsHom_ι (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ)
    (W : X.Opens) (f : Fin (d + 1) → Γ(W.toScheme, ⊤))
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ W.ι ⁻¹' Set.range i.base) :
    openImmersionClsHom i π p W.ι f hT hTf = chartClsHom i π p W f hT hTf := rfl

/-! ### The determinant rule of Tag 0G7S along an open immersion -/

/-- **The determinant rule of [Stacks, Tag 0G7S] for the class map along an arbitrary open
immersion**: changing the equations by a matrix multiplies the class map by the determinant.

This is `Stacks.Gysin.chartClsHom_det` with the chart replaced by an open immersion, and the proof
is unchanged: the excision the class map is transported by does not mention the equations, so the
identity of `Stacks.Gysin.supportedFractionSource_eq_det_smul_of_eq` survives composition with
it. -/
theorem openImmersionClsHom_det (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ)
    (g : Y ⟶ X) [IsOpenImmersion g] (f f' : Fin (d + 1) → Γ(Y, ⊤))
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) Γ(Y, ⊤))
    (hf' : ∀ j, f' j = ∑ l, A j l * f l)
    (hT : IsClosed (g ⁻¹' Set.range i.base))
    (hfT : equationsClosedSet f = g ⁻¹' Set.range i.base)
    (hf'T : equationsClosedSet f' = g ⁻¹' Set.range i.base) :
    openImmersionClsHom i π p g f hT hfT.le =
      globalSmul A.det ((Scheme.Modules.restrictFunctor g).obj
          (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))) ≫
        openImmersionClsHom i π p g f' hT hf'T.le :=
  have : (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms_natCast_add π p (d + 1)
  Eq.trans
    (congrArg
      (fun ψ => ψ ≫
        (supportCohomologyOpenImmersionIso g (isClosed_range_base i) hT ((d + 1 : ℕ) : ℤ)
          (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))).inv)
      (supportedFractionSource_eq_det_smul_of_eq f f' A
        ((Scheme.Modules.restrictFunctor g).obj
          (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))) hf' hT hfT hf'T))
    (Category.assoc _ _ _)

/-! ### The class map of a chart is local along an open of the chart -/

/-- The chase behind `openImmersionClsHom_comp_ι`, at a variable category: a naturality square at
the head of a composite of five morphisms, with the tail re-associated. -/
theorem chaseNat {V : Type*} [Category* V] {o₁ o₂ o₃ o₄ o₅ o₆ o₇ : V}
    (sL : o₁ ⟶ o₂) (m : o₂ ⟶ o₃) (a : o₁ ⟶ o₄) (sR : o₄ ⟶ o₃)
    (u : o₃ ⟶ o₅) (v : o₅ ⟶ o₆) (w : o₆ ⟶ o₇) (h : a ≫ sR = sL ≫ m) :
    sL ≫ m ≫ u ≫ v ≫ w = a ≫ ((sR ≫ u) ≫ v) ≫ w := by
  rw [← Category.assoc sL m, ← h]
  simp only [Category.assoc]

/-- **The class map of a chart is local along an open of the chart.**  For `W : X.Opens` and
`U : W.toScheme.Opens`, the class map of [Stacks, Tag 0G7Q] along the composite `U.ι ≫ W.ι` for the
equations of the chart restricted to `U` is the class map of the chart `W`, restricted along `U.ι`,
with `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` mediating at the source and at the
target.

This is the open-immersion case of [Stacks, Tag 0G7U] assembled onto the chart transport.  Its two
inputs are the base change of the class map,
`Stacks.Gysin.map_supportedFractionSource_comp_supportCohomologyRestrictIso`, applied at the scheme
`W.toScheme` and the open `U`, and the transitivity of the excision along a composite of open
immersions, `Stacks.Gysin.supportCohomologyOpenImmersionIso_inv_comp`; what joins them is the
functoriality of [Stacks, Tag 0G7T] in the coefficient module,
`Stacks.Perfect.SupportedFraction.supportedFractionSource_natural`, which moves the comparison of
the two restrictions of the forms across the class map. -/
theorem openImmersionClsHom_comp_ι (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ)
    (W : X.Opens) (U : W.toScheme.Opens) (f : Fin (d + 1) → Γ(W.toScheme, ⊤))
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ W.ι ⁻¹' Set.range i.base)
    (hTU : IsClosed (U.ι ⁻¹' (W.ι ⁻¹' Set.range i.base)))
    (hTfU : equationsClosedSet (fun j => U.ι.appTop (f j)) ⊆
      U.ι ⁻¹' (W.ι ⁻¹' Set.range i.base)) :
    openImmersionClsHom i π p (U.ι ≫ W.ι) (fun j => U.ι.appTop (f j)) hTU hTfU =
      (Scheme.Modules.restrictFunctorComp U.ι W.ι).hom.app
          (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))) ≫
        (Scheme.Modules.restrictFunctor U.ι).map (chartClsHom i π p W f hT hTf) ≫
          (Scheme.Modules.restrictFunctorComp U.ι W.ι).inv.app (gysinTarget i π (d + 1) p) := by
  have : (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms_natCast_add π p (d + 1)
  have hbc := (Iso.eq_comp_inv (supportCohomologyRestrictIso U hT hTU ((d + 1 : ℕ) : ℤ)
      ((Scheme.Modules.restrictFunctor W.ι).obj
        (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))))).mpr
    (map_supportedFractionSource_comp_supportCohomologyRestrictIso U.ι
      ((Scheme.Modules.restrictFunctor W.ι).obj
        (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))) f hT hTf hTU hTfU)
  have : ((Scheme.Modules.restrictFunctor W.ι ⋙ Scheme.Modules.restrictFunctor U.ι).obj
      (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))).IsQuasicoherent :=
    inferInstanceAs (((Scheme.Modules.restrictFunctor U.ι).obj
      ((Scheme.Modules.restrictFunctor W.ι).obj
        (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))))).IsQuasicoherent)
  have hnat := supportedFractionSource_natural (fun j => U.ι.appTop (f j))
    ((Scheme.Modules.restrictFunctorComp U.ι W.ι).hom.app
      (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))) hTU hTfU
  refine Eq.trans (congrArg (fun ψ => supportedFractionSource (fun j => U.ι.appTop (f j))
      ((Scheme.Modules.restrictFunctor (U.ι ≫ W.ι)).obj
        (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))) hTU hTfU ≫ ψ)
    (supportCohomologyOpenImmersionIso_inv_comp U.ι W.ι (isClosed_range_base i) hT hTU
      ((d + 1 : ℕ) : ℤ) (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))))) ?_
  refine Eq.trans (chaseNat _ _ _ _ _ _ _ hnat) (Eq.symm ?_)
  refine Eq.trans (congrArg (fun ψ => (Scheme.Modules.restrictFunctorComp U.ι W.ι).hom.app
      (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))) ≫ ψ ≫
    (Scheme.Modules.restrictFunctorComp U.ι W.ι).inv.app (gysinTarget i π (d + 1) p))
    ((Scheme.Modules.restrictFunctor U.ι).map_comp _ _)) ?_
  exact congrArg (fun ψ => (Scheme.Modules.restrictFunctorComp U.ι W.ι).hom.app
      (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))) ≫
    (ψ ≫ (Scheme.Modules.restrictFunctor U.ι).map
        (supportCohomologyRestrictIso W (isClosed_range_base i) hT ((d + 1 : ℕ) : ℤ)
          (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))).inv) ≫
    (Scheme.Modules.restrictFunctorComp U.ι W.ι).inv.app (gysinTarget i π (d + 1) p)) hbc

end Stacks.Gysin

end
