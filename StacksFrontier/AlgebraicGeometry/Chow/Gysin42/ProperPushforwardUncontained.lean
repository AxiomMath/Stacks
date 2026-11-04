module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDominantPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.ClassRule
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforward
import StacksFrontier.AlgebraicGeometry.Chow.GysinPushforwardChernCap
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicDivisorPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Reduction
import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.CartesianSquare

/-!
# Proper pushforward of the Gysin cycle of a component not inside the zero scheme

Let `X` and `X'` be schemes locally of finite type over the base scheme `S` of chapter 42 of the
Stacks Project, let `f : X' ⟶ X` be proper over `S`, let `L` be an invertible module on `X` and
let `s ∈ Γ(X, L)` with zero scheme `i : D = Z(s) ⟶ X`. Writing `D' = Z(f^*s)` and
`g : D' ⟶ D` for the morphism of Remark 0B6Y, let `W' ⊆ X'` be an integral closed subscheme of
delta-dimension `k + 1` whose image `W = f(W')` has delta-dimension `k + 1` as well, and suppose
`W` is not contained in `D`. Then

  `g_* [W' ∩ D']_k = [R(W') : R(W)] · [W ∩ D]_k`  in  `Z_k(D)`,

the multiplicity being the pushforward weight with which the generic point of `W'` enters the
proper pushforward of Stacks 02R4. This is the uncontained, dimension-preserving case of the
component identity on which the proof of Stacks 02TA rests, and it is proved here at the level
of cycles rather than of classes.

## The argument

The two sides are compared on `X`, where pushforward along the closed immersion `i` is injective
(`Stacks.Chow.properPushforward_injective_of_isClosedImmersion`), so that the square
`g ≫ i = i' ≫ f` of Remark 0B6Y turns `i_* g_*` into `f_* i'_*`. There the scheme-theoretic
intersection `W ∩ D` may be formed inside `W` instead of inside `D`, both presentations giving
the same closed subscheme of `X`
(`Stacks.Chow.cycleAssociatedToClosedSubscheme_comap_comm`), and inside `W` it is the zero scheme
of the restriction `s|_W` (Stacks 0B6Y, `Stacks.Divisors.zeroScheme_pullback`). The restriction is
nonzero exactly because `W ⊄ D`.

What remains is an identity of cycles on `W`: the pushforward along `W' ⟶ W` of the cycle of
`Z(s|_{W'})` is `[R(W') : R(W)]` times the cycle of `Z(s|_W)`. Both cycles are divisor cycles by
Stacks 02SK, and the pushforward of a divisor cycle along a proper dominant morphism of integral
schemes of equal delta-dimension is the first displayed equation of Stacks 02ST.

## Main results

* `Stacks.Chow.cycleAssociatedToClosedSubscheme_comap_comm` — the cycle of the intersection of
  two closed subschemes does not depend on which of the two it is formed inside.
* `Stacks.Chow.cycleAssociatedToClosedSubscheme_comap_zeroScheme` — the same for `W ∩ Z(s)`,
  formed inside `Z(s)` or as the zero scheme of `s|_W`.
* `Stacks.Chow.pullbackGlobalSections_subschemeι_ne_zero_iff` — the restriction of `s` to an
  integral closed subscheme is nonzero exactly when that subscheme is not inside `Z(s)`.
* `Stacks.Chow.pullbackZeroScheme_le_integralComponentAt_iff` — an integral component of `X'` lies
  inside `Z(f^*s)` exactly when its image lies inside `Z(s)`.
* `Stacks.Chow.divisorOfMeromorphicSectionCycle_eq_meromorphicDivisorCycle` — the divisor cycle of
  a regular meromorphic section is the divisor cycle of its generic value.
* `Stacks.Chow.cycleAssociatedToZeroScheme_eq_meromorphicDivisorCycle` — Stacks 02SK in that
  second model.
* `Stacks.Chow.properPushforward_cycleAssociatedToZeroScheme` — the cycle of the zero scheme of a
  nonzero section, pushed forward along a proper dominant morphism of integral schemes of equal
  delta-dimension.
* `Stacks.Chow.properPushforward_zeroSchemePullbackMap_cycleAssociatedToClosedSubscheme` — the
  displayed identity.
* `Stacks.Chow.properPushforward_gysinComponentCycle_of_not_le` — the same read on the Gysin
  component cycle of Stacks 02T8, for arbitrary first-Chern component rules: in the uncontained
  case those rules do not enter.

## Implementation notes

### The two divisor-cycle models

`Stacks.Chow.divisorOfMeromorphicSectionCycle`, in which Stacks 02SK is stated, takes a global
section of the sheaf of meromorphic sections; `Stacks.Chow.meromorphicDivisorCycle`, in which the
first displayed equation of Stacks 02ST is stated, takes an element of the generic stalk. The
first is by construction the second at the generic value of the section
(`Stacks.Divisors.genericValue`), and the two coefficient specifications are the same statement,
so `Stacks.Chow.divisorOfMeromorphicSectionCycle_eq_meromorphicDivisorCycle` is a definitional
identity: the trivialization hypotheses the two carry are propositions, hence irrelevant.

The remaining join between the two statements is at the section level: the generic value of the
canonical meromorphic image of a pulled-back global section is the pullback of the generic value,
which is `Stacks.Chow.germ_genericPoint_pullbackGlobalSections`.

### The gradings

Stacks 02SK and Stacks 02ST produce cycles of delta-dimension `n - 1` on a scheme of
delta-dimension `n`, while the Gysin cycle of Stacks 02T8 is a `k`-cycle on a component of
delta-dimension `k + 1`. Rather than transport along `(k + 1) - 1 = k`, the proof of the main
identity replaces `k` by `n - 1` at the outset, which costs one rewrite of the dimension
hypotheses and no cast.

## References

* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST)
* [Stacks Project, Tag 02SK](https://stacks.math.columbia.edu/tag/02SK)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors Stacks.AlgebraicGeometry.SectionsBaseChange

/-! ### The intersection of two closed subschemes, formed on either side -/

/-- **The scheme-theoretic intersection of two closed subschemes of `Y` is the same closed
subscheme of `Y` whichever of the two it is formed inside.** Both inverse images present the
join `T ⊔ D` of the two ideal sheaves, by `Stacks.ChernCap42.exists_iso_comap_sup`, and the
join is symmetric. -/
theorem cycleAssociatedToClosedSubscheme_comap_comm (C : ChowSituation.{u}) {Y : Scheme.{u}}
    (q : Y ⟶ C.S) [LocallyOfFiniteType q] (T D : Y.IdealSheafData) (m : ℤ) :
    cycleAssociatedToClosedSubscheme C q
        ((T.comap D.subschemeι).subschemeι ≫ D.subschemeι) m =
      cycleAssociatedToClosedSubscheme C q
        ((D.comap T.subschemeι).subschemeι ≫ T.subschemeι) m := by
  obtain ⟨e₁, he₁⟩ :=
    Stacks.ChernCap42.exists_iso_comap_sup T D T.subschemeι (Iso.refl _) (by simp)
  obtain ⟨e₂, he₂⟩ :=
    Stacks.ChernCap42.exists_iso_comap_sup D T D.subschemeι (Iso.refl _) (by simp)
  rw [cycleAssociatedToClosedSubscheme_eq_of_iso C q _ (D ⊔ T).subschemeι e₂ he₂ m,
    cycleAssociatedToClosedSubscheme_eq_of_iso C q _ (T ⊔ D).subschemeι e₁ he₁ m, sup_comm]

/-- **The intersection of a closed subscheme with a zero scheme is the zero scheme of the
restricted section.** Formed inside `Z(b)` the intersection is `T ∩ Z(b)`; formed inside `T` it is
the zero scheme of `b|_T`, by Stacks 0B6Y. The two are the same closed subscheme of `Y`. -/
theorem cycleAssociatedToClosedSubscheme_comap_zeroScheme (C : ChowSituation.{u})
    {Y : Scheme.{u}} (q : Y ⟶ C.S) [LocallyOfFiniteType q] (N : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property N]
    (b : Γ(N, ⊤)) (T : Y.IdealSheafData) (m : ℤ) :
    cycleAssociatedToClosedSubscheme C q
        ((T.comap (Divisors.zeroScheme Y N b).subschemeι).subschemeι ≫
          (Divisors.zeroScheme Y N b).subschemeι) m =
      cycleAssociatedToClosedSubscheme C q
        ((Divisors.zeroScheme T.subscheme ((Scheme.Modules.pullback T.subschemeι).obj N)
          (AlgebraicGeometry.pullbackGlobalSections T.subschemeι N b)).subschemeι ≫
            T.subschemeι) m := by
  rw [cycleAssociatedToClosedSubscheme_comap_comm C q T (Divisors.zeroScheme Y N b) m,
    zeroScheme_pullback T.subschemeι N b]

/-! ### When the restriction of a section vanishes -/

/-- **The restriction of a section to an integral closed subscheme is nonzero exactly when that
subscheme is not contained in the zero scheme.** If it is contained, the closed immersion factors
through the zero scheme and the restriction vanishes by Stacks 02OR (2); the converse is
`Stacks.Chow.pullbackGlobalSections_subschemeι_ne_zero`. -/
theorem pullbackGlobalSections_subschemeι_ne_zero_iff {X : Scheme.{u}} (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (T : X.IdealSheafData) (hT : IsIntegral T.subscheme) :
    AlgebraicGeometry.pullbackGlobalSections T.subschemeι L s ≠ 0 ↔
      ¬ Divisors.zeroScheme X L s ≤ T := by
  refine ⟨fun hne hle ↦ hne ?_, fun h ↦ pullbackGlobalSections_subschemeι_ne_zero L s T hT h⟩
  exact (pullbackSection_eq_zero_iff_factorsThrough_zeroScheme X L s T.subschemeι).2
    ⟨Scheme.IdealSheafData.inclusion hle, Scheme.IdealSheafData.inclusion_subschemeι hle⟩

/-- **A closed subscheme of `X'` lies inside the zero scheme of `f^*s` exactly when its
scheme-theoretic image lies inside the zero scheme of `s`.** The zero scheme of `f^*s` is the
inverse image of the zero scheme of `s` (Stacks 0B6Y), and inverse image and image of ideal
sheaves form a Galois connection. -/
theorem pullbackZeroScheme_le_iff_zeroScheme_le_map {X X' : Scheme.{u}} (f : X' ⟶ X)
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (T : X'.IdealSheafData) :
    pullbackZeroScheme f L s ≤ T ↔ Divisors.zeroScheme X L s ≤ T.map f := by
  rw [show pullbackZeroScheme f L s = (Divisors.zeroScheme X L s).comap f from
    zeroScheme_pullback f L s]
  exact Scheme.IdealSheafData.le_map_iff_comap_le.symm

/-- **An integral component of `X'` lies inside the zero scheme of `f^*s` exactly when the
integral component of its image lies inside the zero scheme of `s`**, the image of the integral
component of a point being the integral component of its image. -/
theorem pullbackZeroScheme_le_integralComponentAt_iff {X X' : Scheme.{u}} (f : X' ⟶ X)
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (x' : X') :
    pullbackZeroScheme f L s ≤ integralComponentAt x' ↔
      Divisors.zeroScheme X L s ≤ integralComponentAt (f.base x') := by
  rw [pullbackZeroScheme_le_iff_zeroScheme_le_map f L s, map_integralComponentAt f x']

/-! ### The two divisor-cycle models -/

/-- **The divisor cycle of a regular meromorphic section is the divisor cycle of its generic
value.** The first is defined as the second, the two coefficient specifications being the same
statement; the rank-one hypothesis the second carries is a proposition and so does not enter. -/
theorem divisorOfMeromorphicSectionCycle_eq_meromorphicDivisorCycle (C : ChowSituation.{u})
    {V : Scheme.{u}} (q : V ⟶ C.S) [LocallyOfFiniteType q] [IsIntegral V] (n : ℤ)
    (hn : schemeDeltaDimension C q = (n : EInt)) (N : V.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property N]
    (σ : AlgebraicGeometry.MeromorphicSection V.sheaf N)
    (hσ : AlgebraicGeometry.IsRegularMeromorphicSection V.sheaf N σ)
    (hN : ∀ x : V, IsTrivializedNear N x) :
    letI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian q
    divisorOfMeromorphicSectionCycle C q n hn N σ hσ =
      (meromorphicDivisorCycle C q hn hN (genericValue N σ)).val :=
  rfl

/-- **The germ at the generic point of a pulled-back global section is the pullback of its germ.**
Along a dominant morphism of integral schemes the generic point lies over the generic point, and
the pullback of a stalk element carries germs of sections to germs of their pullbacks. -/
theorem germ_genericPoint_pullbackGlobalSections {V V' : Scheme.{u}} [IsIntegral V]
    [IsIntegral V'] (ρ : V' ⟶ V) [IsDominant ρ] (N : V.Modules) (b : Γ(N, ⊤)) :
    ((Scheme.Modules.pullback ρ).obj N).presheaf.germ ⊤ (genericPoint V') trivial
        (AlgebraicGeometry.pullbackGlobalSections ρ N b) =
      genericStalkPullback ρ N (N.presheaf.germ ⊤ (genericPoint V) trivial b) := by
  rw [AlgebraicGeometry.pullbackGlobalSections_eq_unit ρ N]
  exact (genericStalkPullback_germ ρ N ⊤ trivial b).symm

/-- **Stacks 02SK in the generic-stalk model.** On an integral scheme of delta-dimension `n` the
cycle of the zero scheme of a nonzero global section of an invertible module is the divisor cycle
of the germ of that section at the generic point. -/
theorem cycleAssociatedToZeroScheme_eq_meromorphicDivisorCycle (C : ChowSituation.{u})
    {V : Scheme.{u}} (q : V ⟶ C.S) [LocallyOfFiniteType q] [IsIntegral V] (n : ℤ)
    (hn : schemeDeltaDimension C q = (n : EInt)) (N : V.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property N]
    (b : Γ(N, ⊤)) (hb : b ≠ 0) (hN : ∀ x : V, IsTrivializedNear N x) :
    letI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian q
    cycleAssociatedToClosedSubscheme C q (Divisors.zeroScheme V N b).subschemeι (n - 1) =
      (meromorphicDivisorCycle C q hn hN
        (N.presheaf.germ ⊤ (genericPoint V) trivial b)).val := by
  have _ : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian q
  rw [← Stacks.ChernCap42.divisorOfMeromorphicSectionCycle_eq_cycleAssociatedToZeroScheme
      C q n hn N b hb,
    divisorOfMeromorphicSectionCycle_eq_meromorphicDivisorCycle C q n hn N _ _ hN,
    genericValue_meromorphicSectionOfSection]
  rfl

/-! ### Pushing the cycle of a zero scheme along a proper dominant morphism -/

/-- **The cycle of a zero scheme under a proper dominant pushforward.** Let `ρ : V' ⟶ V` be a
proper dominant morphism of integral schemes locally of finite type over the base, both of
delta-dimension `n`, let `N` be an invertible module on `V` and let `b` be a nonzero global
section of `N`. Then

`ρ_* [Z(ρ^*b)]_{n-1} = [R(V') : R(V)] · [Z(b)]_{n-1}`.

Both cycles are divisor cycles by Stacks 02SK, and the identity is the first displayed equation
of Stacks 02ST. -/
theorem properPushforward_cycleAssociatedToZeroScheme (C : ChowSituation.{u})
    {V V' : Scheme.{u}} (q : V ⟶ C.S) [LocallyOfFiniteType q] (q' : V' ⟶ C.S)
    [LocallyOfFiniteType q'] [IsIntegral V] [IsIntegral V'] {n : ℤ}
    (hn : schemeDeltaDimension C q = (n : EInt))
    (hn' : schemeDeltaDimension C q' = (n : EInt)) (ρ : V' ⟶ V) [IsProper ρ] [IsDominant ρ]
    (hρ : ρ ≫ q = q') (N : V.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property N]
    (b : Γ(N, ⊤)) (hb : b ≠ 0) :
    letI : Algebra V.functionField V'.functionField := (dominantFunctionFieldMap ρ).toAlgebra
    properPushforward C q' q ρ hρ (n - 1)
        (cycleAssociatedToClosedSubscheme C q'
          (Divisors.zeroScheme V' ((Scheme.Modules.pullback ρ).obj N)
            (AlgebraicGeometry.pullbackGlobalSections ρ N b)).subschemeι (n - 1)) =
      (Module.finrank V.functionField V'.functionField : ℤ) •
        cycleAssociatedToClosedSubscheme C q (Divisors.zeroScheme V N b).subschemeι (n - 1) := by
  have _ : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian q
  have _ : IsLocallyNoetherian V' := LocallyOfFiniteType.isLocallyNoetherian q'
  let _ : Algebra V.functionField V'.functionField := (dominantFunctionFieldMap ρ).toAlgebra
  have _ := Stacks.Divisors.isInvertible_presheaf N
  have hN : ∀ x : V, IsTrivializedNear N x := isTrivializedNear_of_isInvertible N
  have hN' : ∀ x : V', IsTrivializedNear ((Scheme.Modules.pullback ρ).obj N) x :=
    fun x ↦ (hN (ρ.base x)).pullback
  have hσ : N.presheaf.germ ⊤ (genericPoint V) trivial b ≠ 0 :=
    Stacks.ChernCap42.germ_ne_zero_of_ne_zero N b hb (genericPoint V)
  have hgerm := germ_genericPoint_pullbackGlobalSections ρ N b
  have hb' : AlgebraicGeometry.pullbackGlobalSections ρ N b ≠ 0 := fun h0 ↦
    genericStalkPullback_ne_zero ρ hN hσ (by rw [← hgerm, h0, map_zero])
  rw [cycleAssociatedToZeroScheme_eq_meromorphicDivisorCycle C q n hn N b hb hN,
    cycleAssociatedToZeroScheme_eq_meromorphicDivisorCycle C q' n hn'
      ((Scheme.Modules.pullback ρ).obj N) _ hb' hN', hgerm]
  exact properPushforward_meromorphicDivisorCycle C q' q hn' hn ρ hρ hN _ hσ

/-! ### The identity on `X` -/

/-- Proper pushforward of cycles commutes with integer multiples. -/
private theorem properPushforward_zsmul_cycle (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (h : A ⟶ B) [IsProper h] (hh : h ≫ sB = sA) (m : ℤ) (j : ℤ) (c : CycleGroup C sA m) :
    properPushforward C sA sB h hh m (j • c) = j • properPushforward C sA sB h hh m c :=
  map_zsmul (properPushforwardHom C sA sB h hh m) j c

section Component

variable (C : ChowSituation.{u}) {X X' : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (p' : X' ⟶ C.S) [LocallyOfFiniteType p'] (f : X' ⟶ X) [IsProper f] (hf : f ≫ p = p')
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- **The uncontained component identity, read on `X`.** Let `W' ⊆ X'` and `W ⊆ X` be integral
closed subschemes of delta-dimension `n`, let `ρ : W' ⟶ W` be a proper dominant morphism
compatible with `f`, and suppose `W` is not contained in the zero scheme of `s`. Then the
pushforward along `f` of the cycle of `W' ∩ Z(f^*s)` in `X'` is `[R(W') : R(W)]` times the cycle
of `W ∩ Z(s)` in `X`.

Both intersections are formed inside the component rather than inside the zero scheme
(`Stacks.Chow.cycleAssociatedToClosedSubscheme_comap_comm`), where they are zero schemes of
restricted sections, and the identity becomes
`Stacks.Chow.properPushforward_cycleAssociatedToZeroScheme` along `ρ`. -/
theorem properPushforward_cycleAssociatedToClosedSubscheme_comap_zeroScheme {n : ℤ}
    (W : X.IdealSheafData) (hW : IsIntegral W.subscheme) (W' : X'.IdealSheafData)
    (hW' : IsIntegral W'.subscheme)
    (hnW : schemeDeltaDimension C (W.subschemeι ≫ p) = (n : EInt))
    (hnW' : schemeDeltaDimension C (W'.subschemeι ≫ p') = (n : EInt))
    (ρ : W'.subscheme ⟶ W.subscheme) [IsProper ρ] [IsDominant ρ]
    (hρ : ρ ≫ W.subschemeι = W'.subschemeι ≫ f)
    (hnotle : ¬ Divisors.zeroScheme X L s ≤ W) :
    letI : Algebra W.subscheme.functionField W'.subscheme.functionField :=
      (dominantFunctionFieldMap ρ).toAlgebra
    properPushforward C p' p f hf (n - 1)
        (cycleAssociatedToClosedSubscheme C p'
          ((W'.comap (pullbackZeroScheme f L s).subschemeι).subschemeι ≫
            (pullbackZeroScheme f L s).subschemeι) (n - 1)) =
      (Module.finrank W.subscheme.functionField W'.subscheme.functionField : ℤ) •
        cycleAssociatedToClosedSubscheme C p
          ((W.comap (Divisors.zeroScheme X L s).subschemeι).subschemeι ≫
            (Divisors.zeroScheme X L s).subschemeι) (n - 1) := by
  have _ : IsIntegral W.subscheme := hW
  have _ : IsIntegral W'.subscheme := hW'
  let _ : Algebra W.subscheme.functionField W'.subscheme.functionField :=
    (dominantFunctionFieldMap ρ).toAlgebra
  have hρq : ρ ≫ (W.subschemeι ≫ p) = W'.subschemeι ≫ p' := by
    rw [← Category.assoc, hρ, Category.assoc, hf]
  have ht : AlgebraicGeometry.pullbackGlobalSections W.subschemeι L s ≠ 0 :=
    pullbackGlobalSections_subschemeι_ne_zero L s W hW hnotle
  -- the intersection with `W'`, formed inside `W'`, is the zero scheme of `s` restricted twice
  have hA' : Divisors.zeroScheme W'.subscheme
        ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback W.subschemeι).obj L))
        (AlgebraicGeometry.pullbackGlobalSections ρ
          ((Scheme.Modules.pullback W.subschemeι).obj L)
          (AlgebraicGeometry.pullbackGlobalSections W.subschemeι L s)) =
      (pullbackZeroScheme f L s).comap W'.subschemeι := by
    rw [zeroScheme_pullback ρ ((Scheme.Modules.pullback W.subschemeι).obj L)
        (AlgebraicGeometry.pullbackGlobalSections W.subschemeι L s),
      zeroScheme_pullback W.subschemeι L s, ← Scheme.IdealSheafData.comap_comp, hρ,
      Scheme.IdealSheafData.comap_comp,
      show (Divisors.zeroScheme X L s).comap f = pullbackZeroScheme f L s from
        (zeroScheme_pullback f L s).symm]
  -- both intersections, formed inside the components
  rw [cycleAssociatedToClosedSubscheme_comap_comm C p' W' (pullbackZeroScheme f L s) (n - 1),
    cycleAssociatedToClosedSubscheme_comap_zeroScheme C p L s W (n - 1), ← hA',
    ← properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
      (W'.subschemeι ≫ p') p' W'.subschemeι rfl
      (Divisors.zeroScheme W'.subscheme
        ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback W.subschemeι).obj L))
        (AlgebraicGeometry.pullbackGlobalSections ρ
          ((Scheme.Modules.pullback W.subschemeι).obj L)
          (AlgebraicGeometry.pullbackGlobalSections W.subschemeι L s))).subschemeι (n - 1),
    ← properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
      (W.subschemeι ≫ p) p W.subschemeι rfl
      (Divisors.zeroScheme W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L)
        (AlgebraicGeometry.pullbackGlobalSections W.subschemeι L s)).subschemeι (n - 1),
    properPushforward_properPushforward C (W'.subschemeι ≫ p') p' p W'.subschemeι f rfl hf (n - 1),
    properPushforward_congr C (W'.subschemeι ≫ p') p (W'.subschemeι ≫ f)
      (ρ ≫ W.subschemeι) hρ.symm (by rw [Category.assoc, hf])
      (by rwa [Category.assoc]) (n - 1),
    ← properPushforward_properPushforward C (W'.subschemeι ≫ p') (W.subschemeι ≫ p) p ρ
      W.subschemeι hρq rfl (n - 1),
    properPushforward_cycleAssociatedToZeroScheme C (W.subschemeι ≫ p) (W'.subschemeι ≫ p')
      hnW hnW' ρ hρq ((Scheme.Modules.pullback W.subschemeι).obj L) _ ht,
    properPushforward_zsmul_cycle]

/-! ### The uncontained component identity of Stacks 02TA -/

/-- **Stacks 02TA on an integral component not contained in the zero scheme, at the level of
cycles.** Let `W' = closure {x'}` be an integral component of `X'` of delta-dimension `k + 1`
whose image `W = closure {f x'}` has delta-dimension `k + 1` too, and suppose `W` is not
contained in the zero scheme `D = Z(s)`. Then

`g_* [W' ∩ D']_k = w(x') · [W ∩ D]_k`  in  `Z_k(D)`,

where `g : D' = Z(f^*s) ⟶ D` is the morphism of Remark 0B6Y and `w(x')` is the pushforward
weight of Stacks 02R4.

The two sides are compared after pushing into `X`, where pushforward along the closed immersion
of `D` is injective and the square `g ≫ i = i' ≫ f` of Remark 0B6Y applies. -/
theorem properPushforward_zeroSchemePullbackMap_cycleAssociatedToClosedSubscheme (k : ℤ)
    (x' : X') (hx' : relativeDimension C.dimensionFunction p' x' = k + 1)
    (hx : relativeDimension C.dimensionFunction p (f.base x') = k + 1)
    (hnotle : ¬ Divisors.zeroScheme X L s ≤ integralComponentAt (f.base x')) :
    properPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
        ((Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackMap f L s)
        (zeroSchemePullbackMap_comp_structureMorphism f L s p p' hf) k
        (cycleAssociatedToClosedSubscheme C ((pullbackZeroScheme f L s).subschemeι ≫ p')
          ((integralComponentAt x').comap
            (pullbackZeroScheme f L s).subschemeι).subschemeι k) =
      pushforwardWeight C p' p f x' •
        cycleAssociatedToClosedSubscheme C ((Divisors.zeroScheme X L s).subschemeι ≫ p)
          ((integralComponentAt (f.base x')).comap
            (Divisors.zeroScheme X L s).subschemeι).subschemeι k := by
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, k = n - 1 := ⟨k + 1, by ring⟩
  have hnn : n - 1 + 1 = n := by ring
  have hWint := isIntegral_integralComponentAt (f.base x')
  have hW'int := isIntegral_integralComponentAt x'
  have hnW : schemeDeltaDimension C ((integralComponentAt (f.base x')).subschemeι ≫ p) =
      (n : EInt) := by
    rw [schemeDeltaDimension_integralComponentAt, hx, hnn]
  have hnW' : schemeDeltaDimension C ((integralComponentAt x').subschemeι ≫ p') =
      (n : EInt) := by
    rw [schemeDeltaDimension_integralComponentAt, hx', hnn]
  let _ : Algebra (integralComponentAt (f.base x')).subscheme.functionField
      (integralComponentAt x').subscheme.functionField :=
    (dominantFunctionFieldMap (integralComponentMap f x')).toAlgebra
  have hwt : pushforwardWeight C p' p f x' =
      (Module.finrank (integralComponentAt (f.base x')).subscheme.functionField
        (integralComponentAt x').subscheme.functionField : ℤ) :=
    pushforwardWeight_eq_finrank_functionField C p' p f x' (by rw [hx', hx])
  rw [hwt]
  refine properPushforward_injective_of_isClosedImmersion C
    ((Divisors.zeroScheme X L s).subschemeι ≫ p) p (Divisors.zeroScheme X L s).subschemeι rfl
    (n - 1) ?_
  rw [properPushforward_properPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
      ((Divisors.zeroScheme X L s).subschemeι ≫ p) p (zeroSchemePullbackMap f L s)
      (Divisors.zeroScheme X L s).subschemeι
      (zeroSchemePullbackMap_comp_structureMorphism f L s p p' hf) rfl (n - 1),
    properPushforward_congr C ((pullbackZeroScheme f L s).subschemeι ≫ p') p
      (zeroSchemePullbackMap f L s ≫ (Divisors.zeroScheme X L s).subschemeι)
      ((pullbackZeroScheme f L s).subschemeι ≫ f) (zeroSchemePullbackMap_comp_subschemeι f L s)
      (by rw [Category.assoc, zeroSchemePullbackMap_comp_structureMorphism f L s p p' hf])
      (by rw [Category.assoc, hf]) (n - 1),
    ← properPushforward_properPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p') p' p
      (pullbackZeroScheme f L s).subschemeι f rfl hf (n - 1),
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
      ((pullbackZeroScheme f L s).subschemeι ≫ p') p' (pullbackZeroScheme f L s).subschemeι rfl
      ((integralComponentAt x').comap (pullbackZeroScheme f L s).subschemeι).subschemeι (n - 1),
    properPushforward_zsmul_cycle,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
      ((Divisors.zeroScheme X L s).subschemeι ≫ p) p (Divisors.zeroScheme X L s).subschemeι rfl
      ((integralComponentAt (f.base x')).comap
        (Divisors.zeroScheme X L s).subschemeι).subschemeι (n - 1)]
  exact properPushforward_cycleAssociatedToClosedSubscheme_comap_zeroScheme C p p' f hf L s
    (integralComponentAt (f.base x')) hWint (integralComponentAt x') hW'int hnW hnW'
    (integralComponentMap f x') (integralComponentMap_subschemeι f x') hnotle

/-- **Stacks 02TA on an integral component not contained in the zero scheme, in the vocabulary of
Stacks 02T8.** On a component `W' = closure {x'}` of delta-dimension `k + 1` whose image has
delta-dimension `k + 1` and is not contained in the zero scheme, the Gysin component cycles on
`X'` and on `X` are the fundamental cycles of the two intersections, so the identity of
`Stacks.Chow.properPushforward_zeroSchemePullbackMap_cycleAssociatedToClosedSubscheme` holds for
them whatever the first-Chern component rules are: in the uncontained case those rules do not
enter the Gysin cycle. -/
theorem properPushforward_gysinComponentCycle_of_not_le (k : ℤ)
    (chern : FirstChernComponentClassRule C p k)
    (chern' : FirstChernComponentClassRule C p' k) (x' : X')
    (hx' : relativeDimension C.dimensionFunction p' x' = k + 1)
    (hx : relativeDimension C.dimensionFunction p (f.base x') = k + 1)
    (hnotle : ¬ Divisors.zeroScheme X L s ≤ integralComponentAt (f.base x')) :
    properPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
        ((Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackMap f L s)
        (zeroSchemePullbackMap_comp_structureMorphism f L s p p' hf) k
        (gysinComponentCycle C p' k ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s) chern' (integralComponentAt x')
          (isIntegral_integralComponentAt x')
          (schemeDeltaDimension_integralComponentAt_of_eq C p' hx')) =
      pushforwardWeight C p' p f x' •
        gysinComponentCycle C p k L s chern (integralComponentAt (f.base x'))
          (isIntegral_integralComponentAt (f.base x'))
          (schemeDeltaDimension_integralComponentAt_of_eq C p hx) := by
  rw [gysinComponentCycle_of_not_le C p' k ((Scheme.Modules.pullback f).obj L)
      (AlgebraicGeometry.pullbackGlobalSections f L s) chern' (integralComponentAt x')
      (isIntegral_integralComponentAt x')
      (schemeDeltaDimension_integralComponentAt_of_eq C p' hx')
      (fun h ↦ hnotle ((pullbackZeroScheme_le_integralComponentAt_iff f L s x').1 h)),
    gysinComponentCycle_of_not_le C p k L s chern (integralComponentAt (f.base x'))
      (isIntegral_integralComponentAt (f.base x'))
      (schemeDeltaDimension_integralComponentAt_of_eq C p hx) hnotle]
  exact properPushforward_zeroSchemePullbackMap_cycleAssociatedToClosedSubscheme C p p' f hf L s
    k x' hx' hx hnotle

end Component

end Stacks.Chow

end
