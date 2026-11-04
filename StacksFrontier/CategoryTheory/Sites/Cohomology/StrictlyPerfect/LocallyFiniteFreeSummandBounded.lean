module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocallyFiniteFreeSummandDerivedHom

/-!
# Derived internal Hom out of a bounded locally finite free complex

Let `(C, O)` be a ringed site. Stacks 08JH identifies the derived internal Hom `RSheafHom(E, F)`
with the ordinary internal Hom complex `SheafHom(E, F)` when `E` is *strictly perfect*: bounded,
with every term a **global** direct summand of a finite free `O`-module. The global hypothesis is
stronger than the geometry supplies — an invertible sheaf of modules is only *locally* a direct
summand of a finite free module, and on `P^1` the sheaf `O(1)` admits no nonzero morphism to a
finite free module at all — and
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_isIso_of_isLocallyFiniteFreeSummand`
removes it for a source concentrated in a **single** degree.

This file removes the boundedness-to-one-degree restriction as well: the comparison

`Q(SheafHom(E, F)) ⟶ RSheafHom(E, F)`

is an isomorphism for every bounded `E` each of whose terms is only locally a direct summand of
a finite free `O`-module, and in particular for a bounded complex of invertible sheaves of
modules. That is the shape the local computation of [Stacks, Tag 0B4B] needs: there the source
is the two-term complex `(ℐ_D ⟶ 𝒪_X)` resolving `i_* 𝒪_D` for an effective Cartier divisor, both
of whose terms are invertible and neither of which is a global summand of a finite free module.

The proof is the stupid-filtration induction of Stacks 08JH verbatim, run with the local
hypothesis in place of the global one. That induction uses its termwise hypothesis through
exactly three facts — it transports along an isomorphism, it holds for a zero module, and it
gives the single-degree case — and all three are available locally:
`IsLocallyFiniteFreeSummand.of_iso` and `IsLocallyFiniteFreeSummand.of_isZero` below, and
`homMap_single_quasiIso_of_isLocallyFiniteFreeSummand` already in the library.

## Main results

All names are in the namespace `AlgebraicGeometry.RingedSite`.

* `IsLocallyFiniteFreeSummand.of_iso` and `IsLocallyFiniteFreeSummand.of_isZero`: the local
  hypothesis transports along an isomorphism and holds for a zero module.
* `homMap_quasiIso_of_bounded_isLocallyFiniteFreeSummand` and
  `homMap_quasiIso_of_isLocallyFiniteFreeSummand`: the internal Hom complex out of such an `E`
  carries a quasi-isomorphism of targets to a quasi-isomorphism, in the windowed and the
  finite-support form.
* `strictlyPerfectHomComparison_isIso_of_bounded_isLocallyFiniteFreeSummand`: **Stacks 08JH for a
  bounded source whose terms are only locally direct summands of finite free modules.**
* `strictlyPerfectHomComparison_isIso_of_bounded_isInvertible`: the same for a bounded complex of
  invertible sheaves of modules.

## Implementation notes

The zero module is locally a finite free summand through the covering family `fun V => V`, every
object covering itself: `CategoryTheory.GrothendieckTopology.CoversTop` of the identity family is
the top sieve at every object. No nontrivial covering is needed, and the index type `X.C` already
lives in the universe `IsLocallyFiniteFreeSummand` asks for.

`IsLocallyFiniteFreeSummand.of_iso` is stated in the direction of
`AlgebraicGeometry.RingedSite.IsFiniteFreeSummand.of_iso`, which concludes about the **source**
of the isomorphism; that is the direction the induction below consumes, where the isomorphism
runs from a term of the kernel complex to the corresponding term of `E`.

The two slice spellings of sheaves of modules over the site over `V` — indexed by
`(X.over V).ringSheaf` and by `X.ringSheaf.over V` — agree, and the local `implicit_reducible`
attributes below are what lets the elaborator see it, exactly as in
`LocallyFiniteFreeSummandSource.lean` in this directory.

## References

* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u d

namespace AlgebraicGeometry.RingedSite

attribute [local implicit_reducible]
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  SheafOfModules.pushforward
  SheafOfModules.overFunctor

variable (X : RingedSite.{u, u, u})

/-! ### Closure properties of the local hypothesis -/

/-- Being locally a direct summand of a finite free module transports along an isomorphism: the
same covering family works, and over each member the restricted isomorphism transports the
global hypothesis by `AlgebraicGeometry.RingedSite.IsFiniteFreeSummand.of_iso`. -/
theorem IsLocallyFiniteFreeSummand.of_iso
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (e : M ≅ N)
    (hN : IsLocallyFiniteFreeSummand X N) : IsLocallyFiniteFreeSummand X M := by
  obtain ⟨ι, V, hV, hloc⟩ := hN
  exact ⟨ι, V, hV, fun i => IsFiniteFreeSummand.of_iso (X.over (V i))
    ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (V i)).mapIso e)
    (hloc i)⟩

/-- A zero module is locally a direct summand of a finite free module, through the covering
family in which every object covers itself: restriction to a slice preserves zero objects, and a
zero module is a direct summand of the free module on the empty index set. -/
theorem IsLocallyFiniteFreeSummand.of_isZero
    {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hM : IsZero M) : IsLocallyFiniteFreeSummand X M := by
  refine ⟨X.C, fun V => V, ?_, fun V => IsFiniteFreeSummand.of_isZero (X.over V) ?_⟩
  · intro W
    exact X.J.superset_covering (fun Y f _ => ⟨W, ⟨f⟩⟩) (X.J.top_mem W)
  · exact Functor.map_isZero
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V) hM

/-! ### The stupid-filtration induction, with the local hypothesis -/

/-- **The bounded case, locally.** If `E` vanishes outside the window `[a, a + r)` and each of
its terms is *locally* a direct summand of a finite free `O`-module, then the internal Hom
complex out of `E` carries a quasi-isomorphism of targets to a quasi-isomorphism.

This is `AlgebraicGeometry.RingedSite.homMap_quasiIso_of_bounded` with the global termwise
hypothesis weakened to the local one. The induction peels off the bottom term: the complex sits
in a termwise split short exact sequence with the kernel of the projection onto that term, the
internal Hom complex turns a termwise split short exact sequence of sources into one of targets,
the single-degree case handles the bottom term by
`homMap_single_quasiIso_of_isLocallyFiniteFreeSummand`, and the kernel is one step narrower. -/
theorem homMap_quasiIso_of_bounded_isLocallyFiniteFreeSummand
    {F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : F ⟶ G) [QuasiIso f] (r : ℕ) (a : ℤ)
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hlo : ∀ i, i < a → IsZero (E.X i)) (hhi : ∀ i, a + r ≤ i → IsZero (E.X i))
    (hterm : ∀ i, IsLocallyFiniteFreeSummand X (E.X i)) :
    QuasiIso (homMap X (𝟙 E) f) := by
  induction r generalizing a E with
  | zero =>
    refine homMap_quasiIso_of_isZero X (complex_isZero_of_terms E fun i => ?_) f
    by_cases hi : i < a
    · exact hlo i hi
    · exact hhi i (by push_cast; omega)
  | succ r ih =>
    have ha : IsZero (E.X (a - 1)) := hlo (a - 1) (by omega)
    set p := bottomProjection E a ha
    set K := kernel p
    have hz : IsZero (K.X a) := isZero_kernel_bottomProjection_X_self E a ha
    have hKX (i : ℤ) (hi : i ≠ a) : K.X i ≅ E.X i :=
      have := isIso_kernel_ι_bottomProjection_f E a ha i hi
      asIso ((kernel.ι p).f i)
    have hKterm (i : ℤ) : IsLocallyFiniteFreeSummand X (K.X i) := by
      by_cases hi : i = a
      · subst i
        exact IsLocallyFiniteFreeSummand.of_isZero X hz
      · exact IsLocallyFiniteFreeSummand.of_iso X (hKX i hi) (hterm i)
    have hKlo (i : ℤ) (hi : i < a + 1) : IsZero (K.X i) := by
      by_cases hia : i = a
      · subst i
        exact hz
      · exact IsZero.of_iso (hlo i (by omega)) (hKX i hia)
    have hKhi (i : ℤ) (hi : a + 1 + r ≤ i) : IsZero (K.X i) :=
      IsZero.of_iso (hhi i (by push_cast; omega)) (hKX i (by omega))
    have hKq : QuasiIso (homMap X (𝟙 K) f) := ih (a + 1) K hKlo hKhi hKterm
    have hAq : QuasiIso (homMap X
        (𝟙 ((HomologicalComplex.single
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) a).obj (E.X a))) f) :=
      homMap_single_quasiIso_of_isLocallyFiniteFreeSummand X f a (hterm a)
    refine homMap_quasiIso_of_degreewiseSplit X
      (ShortComplex.mk (kernel.ι p) p (kernel.condition p)) (fun i => ?_) f
    by_cases hi : i = a
    · subst i
      exact ShortComplex.Splitting.ofIsZeroOfIsIso _ hz (isIso_bottomProjection_f_self E a ha)
    · exact ShortComplex.Splitting.ofIsIsoOfIsZero _
        (isIso_kernel_ι_bottomProjection_f E a ha i hi)
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a (E.X a) i hi)

/-- **The strictly perfect case, locally.** If `E` has only finitely many nonzero terms and each
of them is locally a direct summand of a finite free `O`-module, then the internal Hom complex
out of `E` carries a quasi-isomorphism of targets to a quasi-isomorphism. -/
theorem homMap_quasiIso_of_isLocallyFiniteFreeSummand
    {F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : F ⟶ G) [QuasiIso f]
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hbdd : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hterm : ∀ i, IsLocallyFiniteFreeSummand X (E.X i)) :
    QuasiIso (homMap X (𝟙 E) f) := by
  obtain ⟨a, ha⟩ := hbdd.bddBelow
  obtain ⟨b, hb⟩ := hbdd.bddAbove
  refine homMap_quasiIso_of_bounded_isLocallyFiniteFreeSummand X f (b - a + 1).toNat a E ?_ ?_
    hterm
  · intro i hi
    by_contra hz
    have := ha hz
    omega
  · intro i hi
    by_contra hz
    have := hb hz
    omega

/-! ### The comparison to derived internal Hom -/

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  (D : DerivedInternalHom.{u, d} X)

/-- **Stacks 08JH for a bounded source whose terms are only locally direct summands of finite
free modules.** If `E` has finitely many nonzero terms and each of them is locally a direct
summand of a finite free `O`-module then, for every target `F`, the canonical comparison from
the class of the internal Hom complex `SheafHom(E, F)` to the derived internal Hom
`RSheafHom(E, F)` is an isomorphism.

By `strictlyPerfectHomComparison_isIso_iff` this is the quasi-isomorphy of the map of internal
Hom complexes induced by the K-injective augmentation of `F`, which is
`homMap_quasiIso_of_isLocallyFiniteFreeSummand`. The global hypothesis of
`strictlyPerfectHomComparison_isIso` is not available here, and is not needed. -/
theorem strictlyPerfectHomComparison_isIso_of_bounded_isLocallyFiniteFreeSummand
    (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hbdd : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hterm : ∀ i, IsLocallyFiniteFreeSummand X (E.X i)) :
    IsIso (strictlyPerfectHomComparison X D E F) :=
  (strictlyPerfectHomComparison_isIso_iff X D E F).2
    (homMap_quasiIso_of_isLocallyFiniteFreeSummand X ((kInjectiveAugmentation X).app F) E hbdd
      hterm)

/-- **A bounded complex of invertible sheaves of modules is its own derived dual.** For a bounded
complex `E` of invertible sheaves of `O`-modules and any target `F`, the canonical comparison

`Q(SheafHom(E, F)) ⟶ RSheafHom(E, F)`

is an isomorphism.

An invertible sheaf of modules is rank-one locally free, hence locally a direct summand of a
finite free module (`isLocallyFiniteFreeSummand_of_isInvertible`, the [Stacks, Tag 0B8M]
clause), which is the hypothesis of
`strictlyPerfectHomComparison_isIso_of_bounded_isLocallyFiniteFreeSummand`. It is **not** in
general a global direct summand of a finite free module, so the Stacks 08JH statement
`strictlyPerfectHomComparison_isIso` does not apply. -/
theorem strictlyPerfectHomComparison_isIso_of_bounded_isInvertible
    [HasWeakSheafify X.J AddCommGrpCat.{u}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ V : X.C, HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
    [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hbdd : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hterm : ∀ i, Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property (E.X i)) :
    IsIso (strictlyPerfectHomComparison X D E F) :=
  strictlyPerfectHomComparison_isIso_of_bounded_isLocallyFiniteFreeSummand X D E F hbdd
    fun i => let := hterm i; isLocallyFiniteFreeSummand_of_isInvertible X (E.X i)

end AlgebraicGeometry.RingedSite

end
