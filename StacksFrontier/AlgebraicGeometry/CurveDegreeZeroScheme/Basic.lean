module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.OverField
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequence
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.TwoOutOfThree
public import StacksFrontier.AlgebraicGeometry.EulerCharTruncation.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Degree

/-!
# The degree of an invertible sheaf is the Euler characteristic of its zero scheme quotient

For `s` a regular global section of an invertible `L` on a proper scheme of dimension at most one
over a field,

`deg(L) = χ(X, i_* i^* L)`,

where `i : Z(s) ⟶ X` is the inclusion of the zero scheme of `s`. Consequently `deg(L)` is
positive as soon as `χ(X, i_* i^* L)` is.

## Main results

The elided prefix throughout is `AlgebraicGeometry`.

* `invertibleCurveDegree_eq_eulerCharacteristic_of_shortExact_unit`: `deg(L) = χ(𝒬)` for any
  short exact sequence `0 ⟶ 𝒪_X ⟶ L ⟶ 𝒬 ⟶ 0`, given the finite dimensionality of
  [Stacks, Tag 02O6] and the vanishing of [Stacks, Tag 01XJ] for the outer two terms.
* `invertibleCurveDegree_pos_of_eulerCharacteristic_pos_of_shortExact_unit`: consequently the
  degree is positive as soon as `χ(𝒬)` is.
* `invertibleCurveDegree_eq_eulerCharacteristic_zeroScheme_of_isRegularSection`: the
  specialization of the first to the zero scheme of a regular section, via [Stacks, Tag 0C6K].
* `invertibleCurveDegree_pos_of_eulerCharacteristic_pos_zeroScheme`: the degree of `L` is
  positive as soon as the Euler characteristic of `i_* i^* L` is.
* `invertibleCurveDegree_eq_eulerCharacteristic_zeroScheme_of_isFinite` and
  `invertibleCurveDegree_pos_of_eulerCharacteristic_pos_zeroScheme_of_isFinite`: the same two
  when the zero scheme is finite over the base field, assuming finite dimensionality of the
  cohomology of the structure sheaf only.

## References

* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The degree of an invertible sheaf is the Euler characteristic of any quotient of it by
`𝒪_X`.** If `0 ⟶ 𝒪_X ⟶ L ⟶ 𝒬 ⟶ 0` is short exact with `L` invertible on a proper
scheme of dimension at most one over a field, then `deg(L) = χ(X, 𝒬)`. The hypotheses `hfinO`,
`hfinQ`, `hvanO` and `hvanQ` are finite dimensionality of the cohomology of the outer two terms
below the bound `N` and its vanishing from `N` on. -/
theorem invertibleCurveDegree_eq_eulerCharacteristic_of_shortExact_unit [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (Q : X.Modules)
    [L.IsCoherent] [(SheafOfModules.unit X.ringCatSheaf).IsCoherent] [Q.IsCoherent] (N : ℕ)
    (hfinO : ∀ n < N, FiniteDimensional k
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n))
    (hfinQ : ∀ n < N, FiniteDimensional k (cohomologyOverField k f Q n))
    (hvanO : ∀ n, N ≤ n →
      IsZero (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n))
    (hvanQ : ∀ n, N ≤ n → IsZero (cohomologyOverField k f Q n))
    (hSE : let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
      ∃ (a : O ⟶ L) (b : L ⟶ Q) (hab : a ≫ b = 0), (ShortComplex.mk a b hab).ShortExact) :
    invertibleCurveDegree k f hdim L = eulerCharacteristic k f Q := by
  obtain ⟨a, b, hab, hex⟩ := hSE
  have hadd := eulerCharacteristic_add_of_shortExact_of_outer k f hex N hfinO hfinQ hvanO hvanQ
  have hd := invertibleCurveDegree_eq_eulerCharacteristic_sub k f hdim L
  linarith [hadd, hd]

/-- **Positivity of the degree from positivity of the Euler characteristic of the quotient.**
If `0 ⟶ 𝒪_X ⟶ L ⟶ 𝒬 ⟶ 0` is short exact with `L` invertible on a proper scheme of dimension at
most one over a field and `0 < χ(X, 𝒬)`, then `0 < deg(L)`. -/
theorem invertibleCurveDegree_pos_of_eulerCharacteristic_pos_of_shortExact_unit [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (Q : X.Modules)
    [L.IsCoherent] [(SheafOfModules.unit X.ringCatSheaf).IsCoherent] [Q.IsCoherent] (N : ℕ)
    (hfinO : ∀ n < N, FiniteDimensional k
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n))
    (hfinQ : ∀ n < N, FiniteDimensional k (cohomologyOverField k f Q n))
    (hvanO : ∀ n, N ≤ n →
      IsZero (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n))
    (hvanQ : ∀ n, N ≤ n → IsZero (cohomologyOverField k f Q n))
    (hSE : let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
      ∃ (a : O ⟶ L) (b : L ⟶ Q) (hab : a ≫ b = 0), (ShortComplex.mk a b hab).ShortExact)
    (hQ : 0 < eulerCharacteristic k f Q) :
    0 < invertibleCurveDegree k f hdim L :=
  (invertibleCurveDegree_eq_eulerCharacteristic_of_shortExact_unit k f hdim L Q N hfinO hfinQ
    hvanO hvanQ hSE).symm ▸ hQ

/-- **The degree of an invertible sheaf is the Euler characteristic of the restriction of the
sheaf to the zero scheme of a regular section**, pushed forward:
`deg(L) = χ(X, i_* i^* L)` for `i : Z(s) ⟶ X`. -/
theorem invertibleCurveDegree_eq_eulerCharacteristic_zeroScheme_of_isRegularSection [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hs : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s)
    [L.IsCoherent] [(SheafOfModules.unit X.ringCatSheaf).IsCoherent]
    [((Scheme.Modules.pushforward (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj
      ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L)).IsCoherent]
    (N : ℕ)
    (hfinO : ∀ n < N, FiniteDimensional k
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n))
    (hfinQ : ∀ n < N, FiniteDimensional k (cohomologyOverField k f
      ((Scheme.Modules.pushforward (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj
        ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L)) n))
    (hvanO : ∀ n, N ≤ n →
      IsZero (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n))
    (hvanQ : ∀ n, N ≤ n → IsZero (cohomologyOverField k f
      ((Scheme.Modules.pushforward (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj
        ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L)) n)) :
    @invertibleCurveDegree k _ X f _ hdim L hL =
      eulerCharacteristic k f
        ((Scheme.Modules.pushforward (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj
          ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L)) := by
  have hL' : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := hL
  obtain ⟨hz, hex⟩ := shortExact_zeroScheme_of_isRegularSection X L s hs
  exact invertibleCurveDegree_eq_eulerCharacteristic_of_shortExact_unit k f hdim L _ N hfinO
    hfinQ hvanO hvanQ ⟨_, _, hz, hex⟩

/-- The degree of an invertible sheaf with a regular global section is positive as soon as the
Euler characteristic of the restriction of the sheaf to the zero scheme of that section is. -/
theorem invertibleCurveDegree_pos_of_eulerCharacteristic_pos_zeroScheme [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hs : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s)
    [L.IsCoherent] [(SheafOfModules.unit X.ringCatSheaf).IsCoherent]
    [((Scheme.Modules.pushforward (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj
      ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L)).IsCoherent]
    (N : ℕ)
    (hfinO : ∀ n < N, FiniteDimensional k
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n))
    (hfinQ : ∀ n < N, FiniteDimensional k (cohomologyOverField k f
      ((Scheme.Modules.pushforward (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj
        ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L)) n))
    (hvanO : ∀ n, N ≤ n →
      IsZero (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n))
    (hvanQ : ∀ n, N ≤ n → IsZero (cohomologyOverField k f
      ((Scheme.Modules.pushforward (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj
        ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L)) n))
    (hQ : 0 < eulerCharacteristic k f
      ((Scheme.Modules.pushforward (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj
        ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L))) :
    0 < @invertibleCurveDegree k _ X f _ hdim L hL :=
  (invertibleCurveDegree_eq_eulerCharacteristic_zeroScheme_of_isRegularSection k f hdim L s hs N
    hfinO hfinQ hvanO hvanQ).symm ▸ hQ

/-- `deg(L) = χ(X, i_* i^* L)` for a regular section whose zero scheme is finite over `k`,
assuming finite dimensionality of the cohomology of the structure sheaf (`hunit`). -/
theorem invertibleCurveDegree_eq_eulerCharacteristic_zeroScheme_of_isFinite [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hs : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s)
    [L.IsCoherent] [(SheafOfModules.unit X.ringCatSheaf).IsCoherent]
    [IsFinite ((zeroScheme X L (s.eval (op ⊤))).subschemeι ≫ f)]
    [((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L).IsCoherent]
    [((Scheme.Modules.pushforward (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj
      ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L)).IsCoherent]
    (hunit : ∀ n, FiniteDimensional k
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n)) :
    @invertibleCurveDegree k _ X f _ hdim L hL =
      eulerCharacteristic k f
        ((Scheme.Modules.pushforward (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj
          ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L)) := by
  obtain ⟨N, hN⟩ := exists_isZero_cohomologyOverField_of_isProper k f
  obtain ⟨qcO, -⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
      (SheafOfModules.unit X.ringCatSheaf)
  obtain ⟨qcQ, -⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
      ((Scheme.Modules.pushforward (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj
        ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L))
  exact invertibleCurveDegree_eq_eulerCharacteristic_zeroScheme_of_isRegularSection k f hdim L s
    hs N (fun n _ => hunit n)
    (fun n _ => finiteDimensional_cohomologyOverField_pushforward_of_isFinite k _ f _ n)
    (fun n hn => hN _ qcO n hn) (fun n hn => hN _ qcQ n hn)

/-- For a regular global section of an invertible sheaf on a proper scheme of dimension at most
one over a field, whose zero scheme is finite over that field, the degree is positive as soon as
the Euler characteristic of the restriction of the sheaf to that zero scheme is, assuming finite
dimensionality of the cohomology of the structure sheaf (`hunit`). -/
theorem invertibleCurveDegree_pos_of_eulerCharacteristic_pos_zeroScheme_of_isFinite [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hs : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s)
    [L.IsCoherent] [(SheafOfModules.unit X.ringCatSheaf).IsCoherent]
    [IsFinite ((zeroScheme X L (s.eval (op ⊤))).subschemeι ≫ f)]
    [((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L).IsCoherent]
    [((Scheme.Modules.pushforward (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj
      ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L)).IsCoherent]
    (hunit : ∀ n, FiniteDimensional k
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n))
    (hQ : 0 < eulerCharacteristic k f
      ((Scheme.Modules.pushforward (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj
        ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L))) :
    0 < @invertibleCurveDegree k _ X f _ hdim L hL :=
  (invertibleCurveDegree_eq_eulerCharacteristic_zeroScheme_of_isFinite k f hdim L s hs
    hunit).symm ▸ hQ

end AlgebraicGeometry

end
