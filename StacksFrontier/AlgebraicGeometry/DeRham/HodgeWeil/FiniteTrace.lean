module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FiniteFlatDeRhamTrace
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.FirstChernClassPullback
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.DeRhamComparisonAdjoint
public import StacksFrontier.Algebra.Homology.RightDerivedEdgeIso

/-!
# The trace map on Hodge cohomology of a finite syntomic morphism

Let `f : X ⟶ P` be a finite syntomic morphism of schemes such that `f_*𝒪_X` is finite locally
free of constant rank `e`, let `sP : P ⟶ S` be a morphism and `sX = f ≫ sP`. The proof of Axiom
(A6) for Hodge cohomology (Stacks, Remark 0FWE, which reads the proof of Proposition 0FWD,
"Proof of Axiom (A6) for `X` irreducible", for Hodge cohomology) uses the trace map
`Θ_p : f_*Ω^p_{X/S} ⟶ Ω^p_{P/S}` on differential forms of Proposition 0FLC, whose composite with
the canonical map `Ω^p_{P/S} ⟶ f_*Ω^p_{X/S}` is multiplication by `e`. Since `f` is affine and
`Ω^p_{X/S}` is quasi-coherent, the higher direct images of `Ω^p_{X/S}` vanish ([Stacks, Tag 01XC])
and the Leray edge map `H^q(P, f_*Ω^p_{X/S}) ⟶ H^q(X, Ω^p_{X/S})` is an isomorphism. The map

`Θ : H^q(X, Ω^p_{X/S}) ≅ H^q(P, f_*Ω^p_{X/S}) ⟶ H^q(P, Ω^p_{P/S})`

induced by `Θ_p` then satisfies `Θ(f^* x) = e • x`. Hence `f^*` is injective on
`H^q(P, Ω^p_{P/S})` when `e` is invertible on `S`, for instance when `S = Spec k` with `k` a field
of characteristic zero and `e ≥ 1`.

## Main definitions

* `Stacks.HodgeWeil.hodgeAbelianTrace`: the trace map `R^qΓ(X, Ω^p_{X/S}) ⟶ R^qΓ(P, Ω^p_{P/S})`
  on the cohomology of the underlying abelian sheaves.
* `Stacks.HodgeWeil.hodgeComponentTrace`: the trace map `H^q(X, Ω^p_{X/S}) ⟶ H^q(P, Ω^p_{P/S})`
  on the Hodge cohomology groups on which the pullback `Stacks.HodgeWeil.hodgePullback` is
  defined.

## Main results

* `Stacks.HodgeWeil.isIso_abelianEdgeMap_app_of_isAffineHom`: the Leray edge map
  `H^q(P, f_*M) ⟶ H^q(X, M)` is an isomorphism for `f` affine and `M` quasi-coherent.
* `Stacks.HodgeWeil.formsAbelianPushforward_comp_relativeFormsTrace`: the canonical map
  `Ω^p_{P/S} ⟶ f_*Ω^p_{X/S}` followed by the trace is multiplication by `e`.
* `Stacks.HodgeWeil.hodgeComponentTrace_hodgePullback`: **`Θ(f^* x) = e • x`.**
* `Stacks.HodgeWeil.exists_hodgeComponentTrace`: the same for any structure morphism `sX` with
  `f ≫ sP = sX ≫ 𝟙 S`.
* `Stacks.HodgeWeil.injective_hodgePullback_of_isUnit`: `f^*` is injective when `e` is a unit of
  `Γ(S, 𝒪_S)`.
* `Stacks.HodgeWeil.injective_hodgePullback_of_charZero`: `f^*` is injective over a field of
  characteristic zero when `e ≥ 1`.

## Implementation notes

The trace is built on the cohomology `R^qΓ` of the underlying sheaves of abelian groups, where the
Leray edge map is an edge morphism of a composite of right derived functors and its invertibility
in the presence of vanishing higher direct images is available, and transported to the groups
`AlgebraicGeometry.SheafOfModules.hodgeCohomologyComponent` of `f⁻¹𝒪_S`-modules by the comparison
`AlgebraicGeometry.SheafOfModules.hodgeComponentAbelianIso` of the two realizations, which
carries the abelian pullback to `Stacks.HodgeWeil.hodgePullback`
(`Stacks.HodgeWeil.hodgeComponentAbelianIso_hodgePullback`). The trace map is additive; it is
not semilinear for a ring map between the rings acting on the two sides, and is not used as such.

## References

* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
* [Stacks Project, Tag 0FWD](https://stacks.math.columbia.edu/tag/0FWD)
* [Stacks Project, Tag 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Cohomology.Leray (sectionsFunctor)
open Stacks.Cohomology.LerayLowDegree (abelianPushforward abelianEdgeMap abelianCohomology)
open AlgebraicGeometry.SheafOfModules (hodgeCohomologyComponent hodgeComponentAbelianIso)

universe u

namespace Stacks.HodgeWeil

attribute [local instance] HasDerivedCategory.standard

/-! ### The Leray edge map along an affine morphism -/

/-- **The Leray edge map `H^q(P, f_*M) ⟶ H^q(X, M)` is an isomorphism for an affine morphism `f`
and a quasi-coherent module `M`**, on the cohomology of the underlying sheaves of abelian groups:
the higher direct images of `M` vanish ([Stacks, Tag 01XC]). -/
theorem isIso_abelianEdgeMap_app_of_isAffineHom {X P : Scheme.{u}} (f : X ⟶ P) [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent] (i : ℕ) :
    IsIso ((abelianEdgeMap.{u, u} f.base i).app
      ((_root_.SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj M)) :=
  Stacks.Cohomology.RightDerivedEdgeIso.isIso_edge_app _ _ _ i fun q hq _ =>
    Stacks.WeilDeRham.isZero_rightDerived_abelianPushforward_toSheaf_of_isAffineHom f M q hq

/-! ### The trace map -/

variable {X P S : Scheme.{u}} (f : X ⟶ P) (sP : P ⟶ S) [IsFinite f] (hf : Syntomic f) (e : ℕ)

/-- **The canonical map followed by the trace is multiplication by the rank** on the underlying
abelian sheaf of `Ω^p_{P/S}`: the canonical map `Ω^p_{P/S} ⟶ f_*Ω^p_{X/S}` of the square
`f ≫ sP = (f ≫ sP) ≫ 𝟙 S` followed by the trace `f_*Ω^p_{X/S} ⟶ Ω^p_{P/S}` of Proposition 0FLC
is `e • 𝟙`, when `f_*𝒪_X` is finite locally free of rank `e`. -/
theorem formsAbelianPushforward_comp_relativeFormsTrace
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pushforward f).obj (_root_.SheafOfModules.unit X.ringCatSheaf)) e]
    (p : ℕ) :
    formsAbelianPushforward f (f ≫ sP) sP (𝟙 S) (Category.comp_id _).symm p ≫
        (_root_.SheafOfModules.toSheaf.{u} P.ringCatSheaf).map (f.relativeFormsTrace sP hf p) =
      e • 𝟙 _ := by
  have h := HomologicalComplex.congr_hom
    (Stacks.WeilDeRham.deRhamAbelianPushforwardMap_comp_deRhamAbelianTraceMap f sP hf e) p
  rw [HomologicalComplex.comp_f, HomologicalComplex.nsmul_f_apply,
    HomologicalComplex.id_f] at h
  refine Eq.trans ?_ h
  rw [formsAbelianPushforward, Stacks.DeRhamBaseChange.formsAdjoint_eq_deRhamFormsPushforwardHom]
  rfl

/-- **The trace map on the cohomology of the underlying abelian sheaves**
`R^qΓ(X, Ω^p_{X/S}) ⟶ R^qΓ(P, Ω^p_{P/S})` of a finite syntomic `f : X ⟶ P` over `sP : P ⟶ S`:
the inverse of the Leray edge map `R^qΓ(P, f_*Ω^p_{X/S}) ⟶ R^qΓ(X, Ω^p_{X/S})`, an isomorphism
since `f` is affine, followed by the map induced by the trace `f_*Ω^p_{X/S} ⟶ Ω^p_{P/S}`. -/
def hodgeAbelianTrace (p i : ℕ) :
    ((sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerived i).obj
        ((SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras (f ≫ sP))
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ sP)))).X p) ⟶
      ((sectionsFunctor P.toRingedSpace.carrier ⊤).rightDerived i).obj
        ((SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras sP)
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sP))).X p) :=
  (@asIso _ _ _ _ ((abelianEdgeMap.{u, u} f.base i).app
      ((_root_.SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj
        (Scheme.Hom.relativeDifferentialForms (f ≫ sP) (p : ℤ))))
    (haveI := Scheme.Hom.isQuasicoherent_relativeDifferentialForms (f ≫ sP) p
     isIso_abelianEdgeMap_app_of_isAffineHom f _ i)).inv ≫
    (abelianCohomology.{u, u} P.toRingedSpace.carrier ⊤ i).map
      ((_root_.SheafOfModules.toSheaf.{u} P.ringCatSheaf).map (f.relativeFormsTrace sP hf p))

/-- **The trace map on the abelian realization undoes the abelian pullback up to the rank**: the
map induced on `R^qΓ(P, -)` by the canonical map `Ω^p_{P/S} ⟶ f_*Ω^p_{X/S}`, followed by the
Leray edge map and `Stacks.HodgeWeil.hodgeAbelianTrace`, is multiplication by `e`. -/
theorem hodgeAbelianTrace_abelianEdgeMap
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pushforward f).obj (_root_.SheafOfModules.unit X.ringCatSheaf)) e]
    (p i : ℕ)
    (y : ((sectionsFunctor P.toRingedSpace.carrier ⊤).rightDerived i).obj
      ((SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras sP)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sP))).X p)) :
    (hodgeAbelianTrace f sP hf p i).hom ((abelianEdgeMap.{u, u} f.base i).app _
        ((abelianCohomology.{u, u} _ ⊤ i).map
          (formsAbelianPushforward f (f ≫ sP) sP (𝟙 S) (Category.comp_id _).symm p) y)) =
      e • y := by
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms (f ≫ sP) p
  have := isIso_abelianEdgeMap_app_of_isAffineHom f
    (Scheme.Hom.relativeDifferentialForms (f ≫ sP) (p : ℤ)) i
  let F := abelianCohomology.{u, u} P.toRingedSpace.carrier ⊤ i
  have h1 := Iso.hom_inv_id_apply (asIso ((abelianEdgeMap.{u, u} f.base i).app
      ((_root_.SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj
        (Scheme.Hom.relativeDifferentialForms (f ≫ sP) (p : ℤ)))))
    (F.map (formsAbelianPushforward f (f ≫ sP) sP (𝟙 S) (Category.comp_id _).symm p) y)
  have h2 : F.map (formsAbelianPushforward f (f ≫ sP) sP (𝟙 S) (Category.comp_id _).symm p) ≫
      F.map ((_root_.SheafOfModules.toSheaf.{u} P.ringCatSheaf).map
        (f.relativeFormsTrace sP hf p)) = e • 𝟙 _ :=
    (F.map_comp _ _).symm.trans ((congrArg F.map
      (formsAbelianPushforward_comp_relativeFormsTrace f sP hf e p)).trans
      (F.map_nsmul.trans (congrArg (e • ·) (F.map_id _))))
  have h3 := ConcreteCategory.congr_hom h2 y
  rw [ConcreteCategory.comp_apply] at h3
  exact (congrArg (F.map ((_root_.SheafOfModules.toSheaf.{u} P.ringCatSheaf).map
    (f.relativeFormsTrace sP hf p))).hom h1).trans h3

/-- **The trace map on Hodge cohomology** `Θ : H^q(X, Ω^p_{X/S}) ⟶ H^q(P, Ω^p_{P/S})` of a finite
syntomic `f : X ⟶ P` over `sP : P ⟶ S`: `Stacks.HodgeWeil.hodgeAbelianTrace` read through the
comparison `AlgebraicGeometry.SheafOfModules.hodgeComponentAbelianIso` of the two realizations of
the Hodge cohomology groups. -/
def hodgeComponentTrace (p i : ℕ) :
    hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras (f ≫ sP)) p (i : ℤ) →+
      hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras sP) p (i : ℤ) :=
  ((hodgeComponentAbelianIso (X := X.toRingedSpace) (Scheme.Hom.deRhamAlgebras (f ≫ sP))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ sP))) p i i rfl).inv ≫
    hodgeAbelianTrace f sP hf p i ≫
    (hodgeComponentAbelianIso (X := P.toRingedSpace) (Scheme.Hom.deRhamAlgebras sP)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sP)) p i i rfl).hom).hom

/-- **`Θ(f^* x) = e • x` on Hodge cohomology** (Stacks, Remark 0FWE and the proof of
Proposition 0FWD). Let `f : X ⟶ P` be finite syntomic with `f_*𝒪_X` finite locally free of
constant rank `e`, and let `sP : P ⟶ S`. Then for every class `x ∈ H^q(P, Ω^p_{P/S})`, the trace
`Θ` of `Stacks.HodgeWeil.hodgeComponentTrace` carries the pullback `f^* x` along the square
`f ≫ sP = (f ≫ sP) ≫ 𝟙 S` to `e • x`. -/
theorem hodgeComponentTrace_hodgePullback
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pushforward f).obj (_root_.SheafOfModules.unit X.ringCatSheaf)) e]
    (p i : ℕ) (x : hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras sP) p (i : ℤ)) :
    hodgeComponentTrace f sP hf p i
        (hodgePullback f (f ≫ sP) sP (𝟙 S) (Category.comp_id _).symm p i x) = e • x := by
  let EP := hodgeComponentAbelianIso (X := P.toRingedSpace) (Scheme.Hom.deRhamAlgebras sP)
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sP)) p i i rfl
  obtain ⟨y, rfl⟩ : ∃ y, EP.hom.hom y = x := ⟨_, ConcreteCategory.congr_hom EP.inv_hom_id x⟩
  rw [← hodgeComponentAbelianIso_hodgePullback f (f ≫ sP) sP (𝟙 S) (Category.comp_id _).symm p
    i y]
  have h1 := ConcreteCategory.congr_hom (hodgeComponentAbelianIso (X := X.toRingedSpace)
      (Scheme.Hom.deRhamAlgebras (f ≫ sP))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ sP))) p i i
      rfl).hom_inv_id
    ((abelianEdgeMap.{u, u} f.base i).app _ ((abelianCohomology.{u, u} _ ⊤ i).map
      (formsAbelianPushforward f (f ≫ sP) sP (𝟙 S) (Category.comp_id _).symm p) y))
  exact (congrArg (fun z => EP.hom.hom ((hodgeAbelianTrace f sP hf p i).hom z)) h1).trans
    ((congrArg EP.hom.hom (hodgeAbelianTrace_abelianEdgeMap f sP hf e p i y)).trans
      (map_nsmul _ e y))

include hf in
/-- **A trace map on Hodge cohomology exists for any structure morphism of `X` over `S`.** Let
`f : X ⟶ P` be finite syntomic with `f_*𝒪_X` finite locally free of constant rank `e`, and let
`sP : P ⟶ S`, `sX : X ⟶ S` with `f ≫ sP = sX ≫ 𝟙 S`. Then there is an additive map
`Θ : H^q(X, Ω^p_{X/S}) ⟶ H^q(P, Ω^p_{P/S})` with `Θ(f^* x) = e • x` for all `x`. -/
theorem exists_hodgeComponentTrace
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pushforward f).obj (_root_.SheafOfModules.unit X.ringCatSheaf)) e]
    (sX : X ⟶ S) (hcomm : f ≫ sP = sX ≫ 𝟙 S) (p i : ℕ) :
    ∃ Θ : hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras sX) p (i : ℤ) →+
        hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras sP) p (i : ℤ),
      ∀ x, Θ (hodgePullback f sX sP (𝟙 S) hcomm p i x) = e • x := by
  obtain rfl : sX = f ≫ sP := (Category.comp_id sX).symm.trans hcomm.symm
  refine ⟨hodgeComponentTrace f sP hf p i, fun x => ?_⟩
  exact hodgeComponentTrace_hodgePullback f sP hf e p i x

/-! ### Injectivity of the pullback -/

include hf in
/-- **The pullback along a finite syntomic morphism of constant rank `e` is injective on Hodge
cohomology when `e` is invertible on the base.** Let `f : X ⟶ P` be finite syntomic with
`f_*𝒪_X` finite locally free of constant rank `e`, let `sP : P ⟶ S` and `sX : X ⟶ S` with
`f ≫ sP = sX ≫ 𝟙 S`, and suppose `e` is a unit of `Γ(S, 𝒪_S)`. Then
`f^* : H^q(P, Ω^p_{P/S}) ⟶ H^q(X, Ω^p_{X/S})` is injective. -/
theorem injective_hodgePullback_of_isUnit
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pushforward f).obj (_root_.SheafOfModules.unit X.ringCatSheaf)) e]
    (sX : X ⟶ S) (hcomm : f ≫ sP = sX ≫ 𝟙 S) (he : IsUnit (e : S.sheaf.obj.obj (op ⊤)))
    (p i : ℕ) : Function.Injective (hodgePullback f sX sP (𝟙 S) hcomm p i) := by
  obtain ⟨Θ, hΘ⟩ := exists_hodgeComponentTrace f sP hf e sX hcomm p i
  have hu : IsUnit (e : (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{u} sP.base).obj S.sheaf)).obj.obj (op ⊤)) := by
    have h := he.map (Scheme.Hom.inverseImageGlobalSections sP).hom
    rw [map_natCast] at h
    exact h
  refine (injective_iff_map_eq_zero _).2 fun x hx => hu.smul_eq_zero.mp ?_
  rw [Nat.cast_smul_eq_nsmul, ← hΘ x, hx, map_zero]

include hf in
/-- **The pullback along a finite syntomic morphism of positive constant degree is injective on
Hodge cohomology over a field of characteristic zero** (the consequence used in the proof of
(A6), Stacks, Remark 0FWE). Let `k` be a field of characteristic zero and `f : X ⟶ P` a
finite syntomic morphism of `k`-schemes with `f_*𝒪_X` finite locally free of constant rank
`e ≥ 1`. Then `f^* : H^q(P, Ω^p_{P/k}) ⟶ H^q(X, Ω^p_{X/k})` is injective. -/
theorem injective_hodgePullback_of_charZero {k : Type u} [Field k] [CharZero k]
    (sP : P ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pushforward f).obj (_root_.SheafOfModules.unit X.ringCatSheaf)) e]
    (sX : X ⟶ Spec (CommRingCat.of k)) (hcomm : f ≫ sP = sX ≫ 𝟙 _) (he : 1 ≤ e) (p i : ℕ) :
    Function.Injective (hodgePullback f sX sP (𝟙 _) hcomm p i) :=
  injective_hodgePullback_of_isUnit f sP hf e sX hcomm
    (Stacks.WeilDeRham.isUnit_natCast_spec_globalSections k (Nat.one_le_iff_ne_zero.mp he)) p i

end Stacks.HodgeWeil

end
