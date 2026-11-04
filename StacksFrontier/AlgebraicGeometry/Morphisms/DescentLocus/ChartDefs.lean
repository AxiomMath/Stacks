module

public import StacksFrontier.AlgebraicGeometry.Morphisms.DescentLocus.Stage
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankBaseOpen
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleComplex

/-!
# Local charts for the descent locus

The definitions shared by the construction of local charts for the descent problem of
[Stacks, Tag 0BDP] and by the assembly of those charts into the descent locus.

## Main definitions

* `AlgebraicGeometry.DescentLocus.fibreH0`: the dimension of the global sections of `E` on the
  fibre of `f` over a point.
* `AlgebraicGeometry.DescentLocus.HasChart`: a local chart of the descent locus at a prime of a
  Noetherian stage.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.DescentLocus

/-- The dimension of the global sections of `E` on the fibre of `f` over `s`. -/
def fibreH0 {X S : Scheme.{u}} (f : X ⟶ S) (E : X.Modules) (s : S) : ℕ :=
  @Module.finrank (S.residueField s)
    Γ((Scheme.Modules.pullback (pullback.fst f (S.fromSpecResidueField s))).obj E, ⊤) _ _
    (Stacks.Cech.sectionsModule (A := S.residueField s)
      (pullback.snd f (S.fromSpecResidueField s))
      ((Scheme.Modules.pullback (pullback.fst f (S.fromSpecResidueField s))).obj E) ⊤)

/-- **A local chart of the descent locus** at the prime `p` of the Noetherian stage `St`: a basic
open `D(g) ∋ p` of `Spec A₀`, a rank `r` and an immersion of finite presentation `Z ⟶ Spec A₀`
such that over `D(g)` the fibre dimension of the sections of `E` is at most `r`, with equality
over `p`; the rank of a free pullback of `E` to a field point over `p` is `r`; and a test morphism
landing over `D(g)` and in the rank-`r` base open satisfies the descent condition exactly when it
factors through `Z`. -/
def HasChart {X S : Scheme.{u}} (f : X ⟶ S) (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] [UniversallyClosed f]
    {V : S.Opens} {hV : IsAffineOpen V} (St : NoetherianStage f E hV)
    (p : PrimeSpectrum St.A₀) : Prop :=
  ∃ (g : St.A₀) (_ : p ∈ PrimeSpectrum.basicOpen g) (r : ℕ) (Z : Over (Spec (.of St.A₀))),
    IsImmersion Z.hom ∧ FinitePresentation Z.hom ∧
    (∀ x : Spec Γ(S, V), Spec.map (CommRingCat.ofHom St.φ) x ∈ PrimeSpectrum.basicOpen g →
      fibreH0 f E (hV.fromSpec x) ≤ r) ∧
    (∀ x : Spec Γ(S, V), Spec.map (CommRingCat.ofHom St.φ) x = p →
      fibreH0 f E (hV.fromSpec x) = r) ∧
    (∀ (K : Type u) [Field K] (k : Spec (.of K) ⟶ Spec Γ(S, V)) (m : ℕ),
      (k ≫ Spec.map (CommRingCat.ofHom St.φ)) (IsLocalRing.closedPoint K) = p →
      Nonempty ((Scheme.Modules.pullback (pullback.fst f (k ≫ hV.fromSpec))).obj E ≅
        SheafOfModules.free (ULift.{u} (Fin m))) → m = r) ∧
    ∀ {T : Scheme.{u}} (h : T ⟶ Spec Γ(S, V)),
      Set.range (h ≫ Spec.map (CommRingCat.ofHom St.φ)) ⊆
        (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum St.A₀)) →
      Set.range (h ≫ hV.fromSpec) ⊆ Scheme.Modules.rankBaseOpen f E r →
      ((∃ l : T ⟶ Z.left, l ≫ Z.hom = h ≫ Spec.map (CommRingCat.ofHom St.φ)) ↔
        DescendsFromBase f E (h ≫ hV.fromSpec))

end AlgebraicGeometry.DescentLocus
