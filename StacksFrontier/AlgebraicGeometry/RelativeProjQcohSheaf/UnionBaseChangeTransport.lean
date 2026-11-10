module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AlgebraTransportFunctorial
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.BaseChangeCompAlgebra
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadrupleChartGlue
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionAlgebraTransport
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionFunctor

/-!
# The base change of Tag 01NT for the union `F`: composition and transport

Let `S` be a scheme and `𝒜` a graded `𝒪_S`-algebra.  For a morphism `g : S' ⟶ S` the base change
of Tag 01NT is the map `F'(T) → F(T)` of `...RelativeProjQcohSheaf.F.baseChangeUp`, from the union
of the display 01NX for `g^*𝒜` to the union for `𝒜`: a point `(f', ℒ, ψ')` goes to
`(g ∘ f', ℒ, ψ)`, with `ψ` read across the canonical identification `(f')^*g^*𝒜 = (g ∘ f')^*𝒜`.

This file proves the two laws that describe how that map interacts with the rest of the
structure:

* it is **compatible with the transport along a homomorphism of graded algebras**: base changing
  after transporting along the inverse image `g^*Φ` of a homomorphism `Φ : 𝒜 ⟶ ℬ` is transporting
  along `Φ` after base changing;
* it is **associative**: base changing along `q : T' ⟶ T` and then along `g : T ⟶ S` is base
  changing along the composite `q ≫ g`, once the source is transported along the composition law
  `q^*(g^*𝒜) ≅ (q ≫ g)^*𝒜` of the inverse image.

Together with the composition law of the transport, these are exactly what is needed to compare
the iterated base changes of a quadruple that arise when the restriction maps of the functor of
quadruples of Stacks 084A are composed.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.algebraTransport_algebraTransport`: the
  transport of the union along a composite is the composite of the transports.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.baseChangeUp_algebraTransport`: base change
  commutes with transport.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.baseChangeUp_baseChangeUp`: base change is
  associative.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.baseChangeUp_injective`: over a fixed
  morphism `f' : T ⟶ S'` the base change is injective.

## References

* [Stacks Project, Tag 01NT](https://stacks.math.columbia.edu/tag/01NT)
* [Stacks Project, Tag 01NX](https://stacks.math.columbia.edu/tag/01NX)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

/-! ### Quadruples -/

namespace Quadruple

variable {S S' T W : Scheme.{u}}
  {A B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}

/-- **Base change commutes with transport.** For `Φ : 𝒜 ⟶ ℬ`, reading a quadruple for `g^*ℬ`
over `f'` as one for `g^*𝒜` along the inverse image `g^*Φ` and then base changing it to `𝒜` over
`g ∘ f'` gives the same quadruple as base changing it to `ℬ` first and then transporting along
`Φ`.  Degreewise this is the naturality of the contraction of an iterated pullback. -/
theorem baseChangeUp_algebraTransport (g : S' ⟶ S) (f' : T ⟶ S')
    (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B) (h : ∀ n : ℤ, IsIso (Φ.app n))
    (P : Quadruple f' (baseAlgebra g B) d) :
    (algebraTransport (baseAlgebraMapHom g Φ) (fun n => haveI := h n; inferInstance)
        P).baseChangeUp g f' A d =
      algebraTransport Φ h (P.baseChangeUp g f' B d) :=
  Quadruple.ext rfl fun i => heq_of_eq (by
    change compComparison f' g (A.piece (i * d)) ≫
        ((pullbackFunctor (ringedSpaceHom f')).map
          ((pullbackFunctor (ringedSpaceHom g)).map (Φ.app (i * d))) ≫ P.twisting.app i) =
      (pullbackFunctor (ringedSpaceHom (f' ≫ g))).map (Φ.app (i * d)) ≫
        (compComparison f' g (B.piece (i * d)) ≫ P.twisting.app i)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ P.twisting.app i)
        (compComparison_naturality f' g (Φ.app (i * d)))).trans (Category.assoc _ _ _)))

/-- **Base change is associative.** For `q : T ⟶ S'`, `g : S' ⟶ S` and `π = q ≫ g`, a quadruple
for `π^*𝒜` over `f'`, transported along the composition law `q^*(g^*𝒜) ≅ π^*𝒜`, base changed along
`q` and then along `g`, is the quadruple base changed along `π` directly.  Degreewise this is the
associativity of the contraction of an iterated pullback together with the fact that the
composition law is its inverse. -/
theorem baseChangeUp_baseChangeUp (q : S' ⟶ T) (g : T ⟶ S) (π : S' ⟶ S) (hπ : q ≫ g = π)
    (f' : W ⟶ S') (P : Quadruple f' (baseAlgebra π A) d) :
    HEq (((algebraTransport (baseAlgebraCompHomOf A q g π hπ) (fun _ => inferInstance)
        P).baseChangeUp q f' (baseAlgebra g A) d).baseChangeUp g (f' ≫ q) A d)
      (P.baseChangeUp π f' A d) := by
  subst hπ
  refine heq_of_eq (Quadruple.ext rfl fun i => heq_of_eq ?_)
  have hcan : (baseAlgebraCompHomOf A q g (q ≫ g) rfl).app (i * d) =
      inv (compComparison q g (A.piece (i * d))) :=
    (Stacks.AlgebraicGeometry.ModuleLimits.canHom_rfl q g (A.piece (i * d))).trans
      (pullbackComp_hom_app_eq_inv_compComparison q g (A.piece (i * d)))
  have hcancel : (pullbackFunctor (ringedSpaceHom f')).map
        (compComparison q g (A.piece (i * d))) ≫
      (pullbackFunctor (ringedSpaceHom f')).map
        ((baseAlgebraCompHomOf A q g (q ≫ g) rfl).app (i * d)) = 𝟙 _ := by
    have hhi : compComparison q g (A.piece (i * d)) ≫
        (baseAlgebraCompHomOf A q g (q ≫ g) rfl).app (i * d) = 𝟙 _ :=
      (congrArg (fun z => compComparison q g (A.piece (i * d)) ≫ z) hcan).trans
        (IsIso.hom_inv_id _)
    exact ((CategoryTheory.Functor.map_comp _ _ _).symm.trans
      (congrArg (pullbackFunctor (ringedSpaceHom f')).map hhi)).trans
        (CategoryTheory.Functor.map_id _ _)
  change compComparison (f' ≫ q) g (A.piece (i * d)) ≫
      (compComparison f' q ((pullbackFunctor (ringedSpaceHom g)).obj (A.piece (i * d))) ≫
        ((pullbackFunctor (ringedSpaceHom f')).map
          ((baseAlgebraCompHomOf A q g (q ≫ g) rfl).app (i * d)) ≫ P.twisting.app i)) =
    compComparison f' (q ≫ g) (A.piece (i * d)) ≫ P.twisting.app i
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ ((pullbackFunctor (ringedSpaceHom f')).map
      ((baseAlgebraCompHomOf A q g (q ≫ g) rfl).app (i * d)) ≫ P.twisting.app i))
    (compComparison_assoc f' q g (A.piece (i * d)))).trans ?_
  refine (Category.assoc _ _ _).trans (congrArg (fun z => compComparison f' (q ≫ g)
    (A.piece (i * d)) ≫ z) ?_)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ P.twisting.app i) hcancel).trans (Category.id_comp _))

end Quadruple

/-! ### The union -/

variable {S S' T W : Scheme.{u}}
  {A B C : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}

/-- Quadruples over `f` that are equal give equal points of `F(T)` with the same degree. -/
private theorem F.mk_quot_congr {f : T ⟶ S} (d : {d : ℤ // 0 < d})
    {R R' : Quadruple f A d.1} (h : R = R') :
    (⟨f, Quot.mk (UnionRel (f := f) (A := A)) ⟨d, R⟩⟩ : F A T) = ⟨f, Quot.mk _ ⟨d, R'⟩⟩ :=
  h ▸ rfl

/-- **The transport of the union is functorial in the homomorphism**: transporting along `Φ`
after transporting along `Ψ` is transporting along the composite. -/
theorem F.algebraTransport_algebraTransport (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (Ψ : SheafOfModules.GradedAlgebra.UnitalHom B C) (hΦ : ∀ n : ℤ, IsIso (Φ.app n))
    (hΨ : ∀ n : ℤ, IsIso (Ψ.app n)) (hΦΨ : ∀ n : ℤ, IsIso ((Φ.comp Ψ).app n))
    (ξ : F C T) :
    F.algebraTransport Φ hΦ (F.algebraTransport Ψ hΨ ξ) = F.algebraTransport (Φ.comp Ψ) hΦΨ ξ := by
  obtain ⟨f, q⟩ := ξ
  induction q using Quot.ind with
  | _ P =>
      exact F.mk_quot_congr P.1 (Quadruple.algebraTransport_comp Φ Ψ hΦ hΨ hΦΨ P.2)

/-- **Base change commutes with transport** on the union: `F.baseChangeUp g A` of the transport
along `baseAlgebraMapHom g Φ` equals the transport along `Φ` of `F.baseChangeUp g B`. -/
theorem F.baseChangeUp_algebraTransport (g : S' ⟶ S)
    (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B) (h : ∀ n : ℤ, IsIso (Φ.app n))
    (ξ : F (baseAlgebra g B) T) :
    F.baseChangeUp g A (F.algebraTransport (baseAlgebraMapHom g Φ)
        (fun n => haveI := h n; inferInstance) ξ) =
      F.algebraTransport Φ h (F.baseChangeUp g B ξ) := by
  obtain ⟨f', q⟩ := ξ
  induction q using Quot.ind with
  | _ P =>
      exact F.mk_quot_congr P.1 (Quadruple.baseChangeUp_algebraTransport g f' Φ h P.2)

/-- **Base change is associative**, on the union: base changing along `q` and then along `g`,
after transporting along the composition law `q^*(g^*𝒜) ≅ π^*𝒜`, is base changing along the
composite `π = q ≫ g`. -/
theorem F.baseChangeUp_baseChangeUp (q : S' ⟶ T) (g : T ⟶ S) (π : S' ⟶ S) (hπ : q ≫ g = π)
    (ξ : F (baseAlgebra π A) W) :
    F.baseChangeUp g A (F.baseChangeUp q (baseAlgebra g A)
        (F.algebraTransport (baseAlgebraCompHomOf A q g π hπ) (fun _ => inferInstance) ξ)) =
      F.baseChangeUp π A ξ := by
  subst hπ
  obtain ⟨f', c⟩ := ξ
  induction c using Quot.ind with
  | _ P =>
      exact F.mk_quot_congr P.1
        (eq_of_heq (Quadruple.baseChangeUp_baseChangeUp q g (q ≫ g) rfl f' P.2))

/-- **Over a fixed morphism the base change is injective**: two classes over `f' : T ⟶ S'` with
the same image are equal, the inverse map `...RelativeProjQcohSheaf.F.baseChangeDownQ` recovering
each of them. -/
theorem F.baseChangeUp_injective (g : S' ⟶ S) {f' : T ⟶ S'}
    {a b : Quot (UnionRel (f := f') (A := baseAlgebra g A))}
    (h : F.baseChangeUp g A ⟨f', a⟩ = F.baseChangeUp g A ⟨f', b⟩) : a = b := by
  have h2 : (F.baseChangeUp g A ⟨f', a⟩).2 = (F.baseChangeUp g A ⟨f', b⟩).2 :=
    eq_of_heq (Sigma.mk.inj h).2
  have ha := F.baseChangeDownQ_baseChangeUp g A ⟨f', a⟩
  have hb := F.baseChangeDownQ_baseChangeUp g A ⟨f', b⟩
  have hab : (⟨f', a⟩ : F (baseAlgebra g A) T) = ⟨f', b⟩ :=
    ha.symm.trans ((congrArg (F.baseChangeDownQ g A f') h2).trans hb)
  exact eq_of_heq (Sigma.mk.inj hab).2

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
