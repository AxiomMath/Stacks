module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.MapOnSections
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.GradedForms
public import StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex

/-!
# The canonical map on relative differential forms is a map of de Rham complexes

For a commutative square of schemes

```
W → X
↓    ↓
S' → S
```

the canonical maps `f^*Ω^p_{X/S} ⟶ Ω^p_{W/S'}` of
`StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms` **commute with the relative de
Rham differential**: for every open `U` of `X` and every `ω ∈ Γ(Ω^p_{X/S}, U)`,

`d (f^* ω) = f^* (d ω)` in `Γ(Ω^{p+1}_{W/S'}, f⁻¹U)`,

where `f^*` denotes the unit of `f^* ⊣ f_*` followed by the canonical map, that is
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsPullback`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isExactWedge_relativeDifferentialFormsPullback`: **the pullback
  of an exact wedge `d b₁ ∧ ⋯ ∧ d bₚ` is the exact wedge `d (f^# b₁) ∧ ⋯ ∧ d (f^# bₚ)`.**
* `AlgebraicGeometry.Scheme.Hom.deRhamComplex_d_relativeDifferentialFormsPullback` and
  `deRhamComplex_d_relativeDifferentialFormsMap`: **the canonical map on relative differential
  forms commutes with the de Rham differential**, stated through
  `relativeDifferentialFormsPullback` and with that abbreviation unfolded.
* `AlgebraicGeometry.Scheme.Hom.preimageSieve_mem`: the preimages of the members of a covering
  sieve of `U` cover `f⁻¹U`.

## Implementation notes

The proof is the characterization of the de Rham differential by its value on multiples of
exact wedges, pushed through the three identities of
`StacksFrontier.AlgebraicGeometry.DeRham.Complex.MapOnSections`.

* `AlgebraicGeometry.SheafOfModules.exteriorPower_induction` reduces the identity to local
  sections of the form `b · (d b₁ ∧ ⋯ ∧ d bₚ)`, at the cost of a locality step. That step needs
  a covering sieve of `f⁻¹U` refining the preimages of a covering sieve of `U`, which is
  `preimageSieve`: a point of `f⁻¹U` maps into some member of the sieve downstairs, so its
  preimage is a member upstairs containing the point.
* On a multiple of an exact wedge both sides are computed outright. The left-hand side is
  `d (f^# b · f^* ω)`, and `f^* ω` is again an exact wedge, so the `generator` axiom of
  `AlgebraicGeometry.SheafOfModules.DeRhamDifferential` evaluates it as
  `d (f^# b) ∧ f^* ω`. The right-hand side is `f^* (d b ∧ ω)`, which the same axiom and
  multiplicativity of the pullback evaluate as `f^* (d b) ∧ f^* ω`, and
  `relativeDifferentialFormsPullback_exteriorGenerator_d` identifies `f^* (d b)` with
  `d (f^# b)`. So the generator axiom is used once on each side and nothing about the two
  differentials beyond it is needed.
* The degree bookkeeping is the one already present in
  `AlgebraicGeometry.SheafOfModules.IsExactWedge`: the product of a degree-one and a degree-`p`
  form lands in degree `1 + (p : ℤ)`, which is only propositionally `((p + 1 : ℕ) : ℤ)`. So the
  two evaluations are heterogeneous equalities, transported by
  `relativeDifferentialFormsPullback_heq` and compared with `eq_of_heq` at the end, where both
  sides do live in the same type.

**No `@[stacks]` attribute.** The statement proved here is asserted in the Stacks project as
*untagged prose*: in Modules, Section 0FKL — "The compatibility with differentials follows from
the characterization of the differentials by the formula (0FKN)" — and, at the scheme level, in
De Rham cohomology, Section 07HX — "there are canonical maps of complexes
`f^{-1}Ω^•_{X/S} → Ω^•_{X'/S'}` and `Ω^•_{X/S} → f_*Ω^•_{X'/S'}`". Neither paragraph carries a
tag of its own. Tag 0FKP, the only nearby lemma tag, is a different statement: the identification
`f^{-1}Ω^•_{B/A} = Ω^•_{f^{-1}B/f^{-1}A}` along a continuous map of topological spaces, with no
commutative square and no change of rings.

## References

* [Stacks Project, Section 17.26](https://stacks.math.columbia.edu/tag/0FKL)
* [Stacks Project, Section 50.2](https://stacks.math.columbia.edu/tag/07HX)
* [Stacks Project, Tag 0FKN](https://stacks.math.columbia.edu/tag/0FKN)
* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.SheafOfModules (IsExactWedge exactOne deRhamDifferential)
open Stacks.Tag01VSPullbackTensor

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S' S W : Scheme.{u}} (f : W ⟶ X) (a : X ⟶ S) (a' : W ⟶ S')

/-- The sieve on `f⁻¹U` whose members are the opens contained in the preimage of some member of
a sieve `Sv` on `U`. -/
def preimageSieve {U : X.Opens} (Sv : Sieve U) : Sieve (f ⁻¹ᵁ U) where
  arrows V' _ := ∃ (V₀ : X.Opens) (ι : V₀ ⟶ U), Sv ι ∧ V' ≤ f ⁻¹ᵁ V₀
  downward_closed := by
    rintro Y Z j ⟨V₀, ι, hι, hle⟩ k
    exact ⟨V₀, ι, hι, le_trans k.le hle⟩

/-- **The preimages of the members of a covering sieve of `U` cover `f⁻¹U`.** A point of `f⁻¹U`
maps into some member `V₀` of the sieve downstairs, and then lies in the member `f⁻¹V₀`
upstairs. -/
theorem preimageSieve_mem {U : X.Opens} (Sv : Sieve U)
    (hSv : Sv ∈ Opens.grothendieckTopology X.carrier U) :
    preimageSieve f Sv ∈ Opens.grothendieckTopology W.carrier (f ⁻¹ᵁ U) := by
  intro w hw
  obtain ⟨V₀, ι, hι, hmem⟩ := hSv (f.base w) hw
  exact ⟨f ⁻¹ᵁ V₀, homOfLE (fun z hz => ι.le hz), ⟨V₀, ι, hι, le_refl _⟩, hmem⟩

variable (g : S' ⟶ S) (hcomm : f ≫ a = a' ≫ g)

/-- **The pullback of the exact differential `d b` is the exact differential of the pullback.**
This is `relativeDifferentialFormsPullback_exteriorGenerator_d` with both sides read as
exterior-algebra sections of the chosen package of algebras. -/
theorem relativeDifferentialFormsPullback_exactOne (U : X.Opens) (b : Γ(X, U)) :
    relativeDifferentialFormsPullback f a a' g hcomm 1 U
        (exactOne (deRhamAlgebras a) (op U) b)
      = exactOne (deRhamAlgebras a') (op (f ⁻¹ᵁ U)) ((f.app U).hom b) :=
  relativeDifferentialFormsPullback_exteriorGenerator_d f a a' g hcomm U b

/-- The arrow of the relative de Rham complex out of degree `p` acts on a local section as the
relative de Rham differential. -/
theorem deRhamComplex_d_apply (p : ℕ) (V : X.Opens)
    (z : Γ(relativeDifferentialForms a (p : ℤ), V)) :
    ((deRhamComplex a).d p (p + 1)).val.app (op V) z =
      ((deRhamDifferential (deRhamAlgebras a)).differential p).val.app (op V) z :=
  _root_.SheafOfModules.hom_congr_app_apply (deRhamComplex_d a p) (op V) z

/-- Pulling back `d b ∧ η` gives `d (f^# b) ∧ f^* η`. -/
private theorem pullback_mul_exactOne (q : ℕ) (U : X.Opens) (b : Γ(X, U))
    (η : Γ(relativeDifferentialForms a (q : ℤ), U)) :
    relativeDifferentialFormsPullback f a a' g hcomm (1 + (q : ℤ)) U
        (((relativeDifferentialFormsAlgebra a).mul 1 (q : ℤ)).app (op U)
          (exactOne (deRhamAlgebras a) (op U) b) η)
      = ((relativeDifferentialFormsAlgebra a').mul 1 (q : ℤ)).app (op (f ⁻¹ᵁ U))
          (exactOne (deRhamAlgebras a') (op (f ⁻¹ᵁ U)) ((f.app U).hom b))
          (relativeDifferentialFormsPullback f a a' g hcomm (q : ℤ) U η) :=
  Eq.trans (relativeDifferentialFormsPullback_mul f a a' g hcomm 1 (q : ℤ) U _ η)
    (congrArg (fun z => ((relativeDifferentialFormsAlgebra a').mul 1 (q : ℤ)).app
        (op (f ⁻¹ᵁ U)) z (relativeDifferentialFormsPullback f a a' g hcomm (q : ℤ) U η))
      (relativeDifferentialFormsPullback_exactOne f a a' g hcomm U b))

/-- The differential of `b · ω` for an exact wedge `ω` is `d b ∧ ω`. -/
private theorem deRhamComplex_d_smul_heq (p : ℕ) (U : X.Opens) (b : Γ(X, U))
    (ω : Γ(relativeDifferentialForms a (p : ℤ), U))
    (hω : IsExactWedge (deRhamAlgebras a) (op U) p ω) :
    HEq (((deRhamComplex a).d p (p + 1)).val.app (op U) (b • ω))
      (((relativeDifferentialFormsAlgebra a).mul 1 (p : ℤ)).app (op U)
        (exactOne (deRhamAlgebras a) (op U) b) ω) :=
  HEq.trans (heq_of_eq (deRhamComplex_d_apply a p U _))
    ((deRhamDifferential (deRhamAlgebras a)).generator p (op U) b ω hω)

/-- **The pullback of an exact wedge is an exact wedge.** Pulling back is multiplicative and
unital, and in degree one it carries `d b` to `d (f^# b)`, so it carries
`d b₁ ∧ ⋯ ∧ d bₚ` to `d (f^# b₁) ∧ ⋯ ∧ d (f^# bₚ)`. -/
theorem isExactWedge_relativeDifferentialFormsPullback :
    ∀ (p : ℕ) (U : X.Opens) (ω : Γ(relativeDifferentialForms a (p : ℤ), U)),
      IsExactWedge (deRhamAlgebras a) (op U) p ω →
      IsExactWedge (deRhamAlgebras a') (op (f ⁻¹ᵁ U)) p
        (relativeDifferentialFormsPullback f a a' g hcomm (p : ℤ) U ω) := by
  intro p
  induction p with
  | zero =>
      intro U ω hω
      have hω' : ω = (relativeDifferentialFormsAlgebra a).one.eval (op U) := hω
      subst hω'
      exact relativeDifferentialFormsPullback_one f a a' g hcomm U
  | succ p ih =>
      intro U ω hω
      obtain ⟨b, η, hη, hheq⟩ := hω
      refine ⟨(f.app U).hom b, relativeDifferentialFormsPullback f a a' g hcomm (p : ℤ) U η,
        ih U η hη, ?_⟩
      refine HEq.trans (relativeDifferentialFormsPullback_heq f a a' g hcomm
        (show ((p + 1 : ℕ) : ℤ) = 1 + (p : ℤ) by push_cast; ring) U hheq) ?_
      exact heq_of_eq (pullback_mul_exactOne f a a' g hcomm p U b η)

/-- **The de Rham differential commutes with pulling back, on a multiple of an exact wedge.**
Both sides are computed by the `generator` axiom of
`AlgebraicGeometry.SheafOfModules.DeRhamDifferential`: on the left because the pullback of an
exact wedge is an exact wedge, on the right because the differential of `b · ω` is
`d b ∧ ω` and pulling back is multiplicative. -/
theorem deRhamComplex_d_relativeDifferentialFormsPullback_smul (p : ℕ) (U : X.Opens)
    (b : Γ(X, U)) (ω : Γ(relativeDifferentialForms a (p : ℤ), U))
    (hω : IsExactWedge (deRhamAlgebras a) (op U) p ω) :
    ((deRhamComplex a').d p (p + 1)).val.app (op (f ⁻¹ᵁ U))
        (relativeDifferentialFormsPullback f a a' g hcomm (p : ℤ) U (b • ω))
      = relativeDifferentialFormsPullback f a a' g hcomm ((p : ℤ) + 1) U
          (((deRhamComplex a).d p (p + 1)).val.app (op U) (b • ω)) := by
  have hpb := isExactWedge_relativeDifferentialFormsPullback f a a' g hcomm p U ω hω
  have hL : HEq
      (((deRhamComplex a').d p (p + 1)).val.app (op (f ⁻¹ᵁ U))
        (relativeDifferentialFormsPullback f a a' g hcomm (p : ℤ) U (b • ω)))
      (((relativeDifferentialFormsAlgebra a').mul 1 (p : ℤ)).app (op (f ⁻¹ᵁ U))
        (exactOne (deRhamAlgebras a') (op (f ⁻¹ᵁ U)) ((f.app U).hom b))
        (relativeDifferentialFormsPullback f a a' g hcomm (p : ℤ) U ω)) :=
    HEq.trans
      (heq_of_eq (congrArg (((deRhamComplex a').d p (p + 1)).val.app (op (f ⁻¹ᵁ U)))
        (relativeDifferentialFormsPullback_smul f a a' g hcomm (p : ℤ) U b ω)))
      (deRhamComplex_d_smul_heq a' p (f ⁻¹ᵁ U) _ _ hpb)
  have hR : HEq
      (relativeDifferentialFormsPullback f a a' g hcomm ((p : ℤ) + 1) U
        (((deRhamComplex a).d p (p + 1)).val.app (op U) (b • ω)))
      (((relativeDifferentialFormsAlgebra a').mul 1 (p : ℤ)).app (op (f ⁻¹ᵁ U))
        (exactOne (deRhamAlgebras a') (op (f ⁻¹ᵁ U)) ((f.app U).hom b))
        (relativeDifferentialFormsPullback f a a' g hcomm (p : ℤ) U ω)) :=
    HEq.trans
      (relativeDifferentialFormsPullback_heq f a a' g hcomm
        (show (p : ℤ) + 1 = 1 + (p : ℤ) from add_comm _ _) U
        (deRhamComplex_d_smul_heq a p U b ω hω))
      (heq_of_eq (pullback_mul_exactOne f a a' g hcomm p U b ω))
  exact eq_of_heq (hL.trans hR.symm)

/-- Restricting the differential of a pulled-back form is the differential of the pulled-back
restriction: the de Rham differential and the pullback of forms both commute with
restriction. -/
theorem deRhamComplex_d_relativeDifferentialFormsPullback_restrict (p : ℕ) {U V : X.Opens}
    (hVU : V ≤ U) (ξ : Γ(relativeDifferentialForms a (p : ℤ), U)) :
    (relativeDifferentialForms a' ((p : ℤ) + 1)).presheaf.map
        (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun _ hz => hVU hz)).op
        (((deRhamComplex a').d p (p + 1)).val.app (op (f ⁻¹ᵁ U))
          (relativeDifferentialFormsPullback f a a' g hcomm (p : ℤ) U ξ))
      = ((deRhamComplex a').d p (p + 1)).val.app (op (f ⁻¹ᵁ V))
          (relativeDifferentialFormsPullback f a a' g hcomm (p : ℤ) V
            ((relativeDifferentialForms a (p : ℤ)).presheaf.map (homOfLE hVU).op ξ)) :=
  Eq.trans
    (PresheafOfModules.naturality_apply ((deRhamComplex a').d p (p + 1)).val
      (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun _ hz => hVU hz)).op _).symm
    (congrArg (((deRhamComplex a').d p (p + 1)).val.app (op (f ⁻¹ᵁ V)))
      (relativeDifferentialFormsPullback_map f a a' g hcomm (p : ℤ) hVU ξ).symm)

/-- Restricting the pullback of a differential is the pullback of the restricted differential. -/
theorem relativeDifferentialFormsPullback_deRhamComplex_d_restrict (p : ℕ) {U V : X.Opens}
    (hVU : V ≤ U) (ξ : Γ(relativeDifferentialForms a (p : ℤ), U)) :
    (relativeDifferentialForms a' ((p : ℤ) + 1)).presheaf.map
        (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun _ hz => hVU hz)).op
        (relativeDifferentialFormsPullback f a a' g hcomm ((p : ℤ) + 1) U
          (((deRhamComplex a).d p (p + 1)).val.app (op U) ξ))
      = relativeDifferentialFormsPullback f a a' g hcomm ((p : ℤ) + 1) V
          (((deRhamComplex a).d p (p + 1)).val.app (op V)
            ((relativeDifferentialForms a (p : ℤ)).presheaf.map (homOfLE hVU).op ξ)) :=
  Eq.trans
    (relativeDifferentialFormsPullback_map f a a' g hcomm ((p : ℤ) + 1) hVU _).symm
    (congrArg (relativeDifferentialFormsPullback f a a' g hcomm ((p : ℤ) + 1) V)
      (PresheafOfModules.naturality_apply ((deRhamComplex a).d p (p + 1)).val
        (homOfLE hVU).op ξ).symm)

/-- **The canonical map on relative differential forms commutes with the relative de Rham
differential.** For a commutative square of schemes with horizontal arrows `f : W ⟶ X` and
`g : S' ⟶ S`, every open `U` of `X` and every `ω ∈ Γ(Ω^p_{X/S}, U)`,

`d (f^* ω) = f^* (d ω)` in `Γ(Ω^{p+1}_{W/S'}, f⁻¹U)`.

Both sides are additive and compatible with restriction, so it suffices to check the identity on
multiples of exact wedges, which generate `Ω^p_{X/S}` locally. -/
theorem deRhamComplex_d_relativeDifferentialFormsPullback (p : ℕ) (U : X.Opens)
    (ω : Γ(relativeDifferentialForms a (p : ℤ), U)) :
    ((deRhamComplex a').d p (p + 1)).val.app (op (f ⁻¹ᵁ U))
        (relativeDifferentialFormsPullback f a a' g hcomm (p : ℤ) U ω)
      = relativeDifferentialFormsPullback f a a' g hcomm ((p : ℤ) + 1) U
          (((deRhamComplex a).d p (p + 1)).val.app (op U) ω) := by
  refine AlgebraicGeometry.SheafOfModules.exteriorPower_induction (deRhamAlgebras a) p
    (fun V ξ => ((deRhamComplex a').d p (p + 1)).val.app (op (f ⁻¹ᵁ V.unop))
          (relativeDifferentialFormsPullback f a a' g hcomm (p : ℤ) V.unop ξ)
        = relativeDifferentialFormsPullback f a a' g hcomm ((p : ℤ) + 1) V.unop
            (((deRhamComplex a).d p (p + 1)).val.app V ξ))
    ?_ ?_ ?_ ?_ ?_ (op U) ω
  · intro V
    refine Eq.trans (congrArg (((deRhamComplex a').d p (p + 1)).val.app (op (f ⁻¹ᵁ V.unop)))
      (relativeDifferentialFormsPullback_zero f a a' g hcomm (p : ℤ) V.unop)) ?_
    refine Eq.trans (map_zero _) ?_
    exact (Eq.trans
      (congrArg (relativeDifferentialFormsPullback f a a' g hcomm ((p : ℤ) + 1) V.unop)
        (map_zero _))
      (relativeDifferentialFormsPullback_zero f a a' g hcomm ((p : ℤ) + 1) V.unop)).symm
  · intro V x y hx hy
    refine Eq.trans (congrArg (((deRhamComplex a').d p (p + 1)).val.app (op (f ⁻¹ᵁ V.unop)))
      (relativeDifferentialFormsPullback_add f a a' g hcomm (p : ℤ) V.unop x y)) ?_
    refine Eq.trans (map_add _ _ _) ?_
    refine Eq.trans (congrArg₂ (· + ·) hx hy) ?_
    exact (Eq.trans
      (congrArg (relativeDifferentialFormsPullback f a a' g hcomm ((p : ℤ) + 1) V.unop)
        (map_add _ _ _))
      (relativeDifferentialFormsPullback_add f a a' g hcomm ((p : ℤ) + 1) V.unop _ _)).symm
  · intro V x hx
    refine Eq.trans (congrArg (((deRhamComplex a').d p (p + 1)).val.app (op (f ⁻¹ᵁ V.unop)))
      (relativeDifferentialFormsPullback_neg f a a' g hcomm (p : ℤ) V.unop x)) ?_
    refine Eq.trans (map_neg _ _) ?_
    refine Eq.trans (congrArg (fun z => -z) hx) ?_
    exact (Eq.trans
      (congrArg (relativeDifferentialFormsPullback f a a' g hcomm ((p : ℤ) + 1) V.unop)
        (map_neg _ _))
      (relativeDifferentialFormsPullback_neg f a a' g hcomm ((p : ℤ) + 1) V.unop _)).symm
  · intro V ξ Sv hSv hall
    refine (relativeDifferentialForms a' ((p : ℤ) + 1)).isSheaf.isSeparated
      (f ⁻¹ᵁ V.unop) (preimageSieve f Sv) (preimageSieve_mem f Sv hSv) _ _ ?_
    rintro V' j ⟨V₀, ι, hι, hle⟩
    have hV₀ : V₀ ≤ V.unop := ι.le
    have e := fun (z : Γ(relativeDifferentialForms a' ((p : ℤ) + 1), f ⁻¹ᵁ V.unop)) =>
      presheaf_map_map (relativeDifferentialForms a' ((p : ℤ) + 1))
        (homOfLE (show f ⁻¹ᵁ V₀ ≤ f ⁻¹ᵁ V.unop from fun _ hz => hV₀ hz)) (homOfLE hle) j z
    refine Eq.trans (e _).symm (Eq.trans (congrArg
      (fun z => (relativeDifferentialForms a' ((p : ℤ) + 1)).presheaf.map (homOfLE hle).op z)
      ?_) (e _))
    exact Eq.trans (deRhamComplex_d_relativeDifferentialFormsPullback_restrict
        f a a' g hcomm p hV₀ ξ)
      (Eq.trans (hall V₀ ι hι)
        (relativeDifferentialFormsPullback_deRhamComplex_d_restrict f a a' g hcomm p hV₀ ξ).symm)
  · intro V b η hη
    exact deRhamComplex_d_relativeDifferentialFormsPullback_smul f a a' g hcomm p V.unop b η hη

/-- **The canonical map on relative differential forms commutes with the relative de Rham
differential**, with the pullback of a form written out as the unit of `f^* ⊣ f_*` followed by
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap`. -/
theorem deRhamComplex_d_relativeDifferentialFormsMap (p : ℕ) (U : X.Opens)
    (ω : Γ(relativeDifferentialForms a (p : ℤ), U)) :
    ((deRhamComplex a').d p (p + 1)).val.app (op (f ⁻¹ᵁ U))
        ((relativeDifferentialFormsMap f a a' g hcomm (p : ℤ)).val.app (op (f ⁻¹ᵁ U))
          (modulesPullbackUnit f (relativeDifferentialForms a (p : ℤ)) U ω))
      = (relativeDifferentialFormsMap f a a' g hcomm ((p : ℤ) + 1)).val.app (op (f ⁻¹ᵁ U))
          (modulesPullbackUnit f (relativeDifferentialForms a ((p : ℤ) + 1)) U
            (((deRhamComplex a).d p (p + 1)).val.app (op U) ω)) :=
  deRhamComplex_d_relativeDifferentialFormsPullback f a a' g hcomm p U ω

end AlgebraicGeometry.Scheme.Hom

end
