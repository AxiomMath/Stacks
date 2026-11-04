module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassScale

/-!
# The transport of the union `F` of the display 01NX along an isomorphism of graded algebras

Let `X` be a scheme and `Φ : 𝒜 ⟶ ℬ` a unital homomorphism of graded `𝒪_X`-algebras all of whose
components are isomorphisms.  Then the functors of quadruples of `(X, 𝒜)` and of `(X, ℬ)` agree.
At a fixed degree this is `...RelativeProjQcohSheaf.Fd.algebraTransportEquiv`; this file proves
it for the **union** `F = ⋃_{d ≥ 1} F_d` of the display 01NX, which the library did not have.

Unlike the base change of `...RelativeProjQcohSheaf.F.baseChangeUp`, no converse is needed:
the inverse map is the transport along `...RelativeProjQcohSheaf.unitalHomInverse`, so only the
forward descent to the quotient is required in each direction.  That descent needs the transport
to match both relations `...RelativeProjQcohSheaf.UnionRel` generates — strict equivalence inside
a degree, by `...RelativeProjQcohSheaf.Quadruple.strictlyEquivalent_algebraTransport_iff`, and
the equivalence of Tag 01NW across degrees, by
`...RelativeProjQcohSheaf.Quadruple.CompatibleAt.algebraTransport`.  Both were already proved;
the second had not been stated in the `Quadruple.Equivalent` spelling the union's relation uses.

This is the second of the two comparisons that a functor of quadruples over a *varying* base
needs — the other being `...RelativeProjQcohSheaf.F.baseChangePullbackIso` — because a change of
base scheme produces the base-changed algebra `g^*𝒜` only up to isomorphism, not on the nose.

Everything is unconditional: no positivity of the degree, no quasi-compactness of the test
scheme.

## References

* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NW](https://stacks.math.columbia.edu/tag/01NW)
* [Stacks Project, Tag 01NX](https://stacks.math.columbia.edu/tag/01NX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

/-! ### A comparison of Tag 01NW survives the transport -/

namespace Quadruple

variable {X T : Scheme.{u}}
  {A B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X.toRingedSpace)}
  {d d' : ℤ} {f : T ⟶ X}

/-- **The equivalence of [Stacks, Section 01NS] across degrees survives the transport along an
isomorphism of graded algebras**, in the spelling the union's relation uses.  Equivalence *is* a
comparison at the common multiple `d d'` of the two degrees, so this is
`...RelativeProjQcohSheaf.Quadruple.CompatibleAt.algebraTransport` read at `(d', d)`. -/
theorem Equivalent.algebraTransport (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (hiso : ∀ n : ℤ, IsIso (Φ.app n)) {P : Quadruple f B d} {Q : Quadruple f B d'}
    (he : Equivalent P Q) :
    Equivalent (Quadruple.algebraTransport Φ hiso P) (Quadruple.algebraTransport Φ hiso Q) :=
  CompatibleAt.algebraTransport Φ hiso he

end Quadruple

/-! ### The union `F`, transported -/

section FLevel

variable {X : Scheme.{u}}
  {A B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X.toRingedSpace)}
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B) (h : ∀ n : ℤ, IsIso (Φ.app n))

/-- **The map `F(T)` for `ℬ` to `F(T)` for `𝒜`** along a unital homomorphism all of whose
components are isomorphisms: the point of a quadruple of positive degree is sent to the point of
its transport, of the same degree.  Well defined because the transport matches both relations the
union's `...RelativeProjQcohSheaf.UnionRel` generates. -/
def F.algebraTransport {T : Scheme.{u}} (ξ : F B T) : F A T :=
  ⟨ξ.1,
    Quot.lift
      (fun P : PositiveQuadruple ξ.1 B =>
        Quot.mk (UnionRel (f := ξ.1) (A := A)) ⟨P.1, Quadruple.algebraTransport Φ h P.2⟩)
      (fun _ _ hrel => by
        cases hrel with
        | strict hs =>
            exact Quot.sound (UnionRel.strict
              ((Quadruple.strictlyEquivalent_algebraTransport_iff Φ h).mpr hs))
        | equivalent he =>
            exact Quot.sound (UnionRel.equivalent
              (Quadruple.Equivalent.algebraTransport Φ h he)))
      ξ.2⟩

/-- The morphism to the base recorded by a point of the union is unchanged by the transport. -/
@[simp] theorem F.algebraTransport_fst {T : Scheme.{u}} (ξ : F B T) :
    (F.algebraTransport Φ h ξ).1 = ξ.1 := rfl

/-- The transport sends the point of a quadruple to the point of its transport, of the same
degree. -/
@[simp] theorem F.algebraTransport_mk {T : Scheme.{u}} (f : T ⟶ X) {d : ℤ} (hd : 0 < d)
    (P : Quadruple f B d) :
    F.algebraTransport Φ h (F.mk f hd P) =
      F.mk f hd (Quadruple.algebraTransport Φ h P) := rfl

/-- **The unions `F(T)` for `𝒜` and for `ℬ` correspond bijectively** along a unital homomorphism
`Φ : 𝒜 ⟶ ℬ` all of whose components are isomorphisms.  The inverse is the transport along
`...RelativeProjQcohSheaf.unitalHomInverse`. -/
def F.algebraTransportEquiv (T : Scheme.{u}) : F B T ≃ F A T where
  toFun ξ := F.algebraTransport Φ h ξ
  invFun ξ :=
    F.algebraTransport (unitalHomInverse Φ h) (isIso_unitalHomInverse_app Φ h) ξ
  left_inv ξ := by
    obtain ⟨f, q⟩ := ξ
    induction q using Quot.ind with
    | _ P =>
        exact congrArg
          (fun R : Quadruple f B P.1.1 =>
            (⟨f, Quot.mk (UnionRel (f := f) (A := B)) ⟨P.1, R⟩⟩ : F B T))
          (Quadruple.algebraTransport_inverse_algebraTransport Φ h P.2)
  right_inv ξ := by
    obtain ⟨f, q⟩ := ξ
    induction q using Quot.ind with
    | _ P =>
        exact congrArg
          (fun R : Quadruple f A P.1.1 =>
            (⟨f, Quot.mk (UnionRel (f := f) (A := A)) ⟨P.1, R⟩⟩ : F A T))
          (Quadruple.algebraTransport_algebraTransport_inverse Φ h P.2)

/-- The bijection is `...RelativeProjQcohSheaf.F.algebraTransport` on an element. -/
@[simp] theorem F.algebraTransportEquiv_apply (T : Scheme.{u}) (ξ : F B T) :
    F.algebraTransportEquiv Φ h T ξ = F.algebraTransport Φ h ξ := rfl

/-- **The bijection of the unions commutes with the pullback along a morphism of test schemes**,
so it is natural in the test scheme. -/
theorem F.algebraTransport_pullback {T T' : Scheme.{u}} (g : T' ⟶ T) (ξ : F B T) :
    F.algebraTransport Φ h (F.pullback g ξ) = F.pullback g (F.algebraTransport Φ h ξ) := by
  obtain ⟨f, q⟩ := ξ
  induction q using Quot.ind with
  | _ P =>
      exact (congrArg
        (fun R : Quadruple (g ≫ f) A P.1.1 =>
          (⟨g ≫ f, Quot.mk (UnionRel (f := g ≫ f) (A := A)) ⟨P.1, R⟩⟩ : F A T'))
        (Quadruple.algebraTransport_pullback Φ h P.2 g)).symm

/-- **The natural transformation of the functors of the display 01NX induced by a unital
homomorphism** all of whose components are isomorphisms: on a test scheme it is
`...RelativeProjQcohSheaf.F.algebraTransport`, and naturality is
`...RelativeProjQcohSheaf.F.algebraTransport_pullback`. -/
def F.algebraTransportNat : F.functor B ⟶ F.functor A where
  app _T := TypeCat.ofHom (F.algebraTransport Φ h)
  naturality _ _ φ := TypeCat.homEquiv.injective (funext fun ξ =>
    F.algebraTransport_pullback Φ h φ.unop ξ)

/-- The components of the natural transformation. -/
@[simp] theorem F.algebraTransportNat_app (T : Scheme.{u}ᵒᵖ) (ξ : F B T.unop) :
    (F.algebraTransportNat Φ h).app T ξ = F.algebraTransport Φ h ξ := rfl

/-- The natural transformation is an isomorphism, its components being bijections. -/
instance F.isIso_algebraTransportNat : IsIso (F.algebraTransportNat Φ h) := by
  have : ∀ T : Scheme.{u}ᵒᵖ, IsIso ((F.algebraTransportNat Φ h).app T) := fun T =>
    (isIso_iff_bijective _).mpr (F.algebraTransportEquiv Φ h T.unop).bijective
  exact NatIso.isIso_of_isIso_app _

/-- **The functors of the display 01NX of two isomorphic graded algebras are isomorphic.** -/
def F.algebraTransportIso : F.functor B ≅ F.functor A :=
  asIso (F.algebraTransportNat Φ h)

/-- The isomorphism of functors is compatible with the projections to the functor of points of
the base: the transport does not move the structure morphism a point records. -/
theorem F.algebraTransportNat_comp_toBase :
    F.algebraTransportNat Φ h ≫ F.toBase A = F.toBase B :=
  NatTrans.ext (funext fun _T => TypeCat.homEquiv.injective (funext fun _ξ => rfl))

end FLevel

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
