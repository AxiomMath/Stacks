module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedGroup
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.TotalChernClass
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankDecomposition

/-!
# The top Chern class of a finite locally free module

Let `(S, δ)` be the base situation of chapter 42, let `X` be locally of finite type over `S` and
let `E` be a finite locally free `𝒪_X`-module. The rank of `E` is locally constant, so `X` is the
disjoint union `X = ∐_r X_r` of the loci on which the rank is `r`, and the *top* Chern class of
`E` is the class whose component on `X_r` is the `r`-th Chern class `c_r(E|_{X_r})`:

  `c_top(E) = Σ_r c_r(E|_{X_r})`.

Its degree is not constant on `X`, so it is in general not a bivariant class of any single degree.
It is instead an element of the completed bivariant group `A^*(X)^∧`, the product over the
connected components of `X` of the graded bivariant groups of the components. The rank is constant
on a connected component, so the top Chern class is homogeneous there, of degree that rank; this
is what gives it a component of the completed group. When only finitely many of the loci `X_r` are
nonempty, only finitely many degrees occur in total and the class already lies in the ordinary
graded group `A^*(X) = ⊕_p A^p(X)`, where it is the finite sum displayed above.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.rankOnConnectedComponent` — the rank of `E` on a connected
  component of `X`.
* `Stacks.Chow.connectedComponentBivariantEquiv` — the identification of `A^p(X)` with the
  product of the `A^p(X_i)` over the connected components of `X`.
* `Stacks.Chow.topChernClass` — the top Chern class, in the completed bivariant group.
* `Stacks.Chow.topChernClassDegree` — its degree-`p` part, as a bivariant class on `X`.
* `Stacks.Chow.topChernClassFinite` — the top Chern class as an ordinary nonhomogeneous bivariant
  class, when only finitely many rank loci are nonempty.

## Main results

* `AlgebraicGeometry.Scheme.Modules.connectedComponentOpens_le_rankStratum` and
  `AlgebraicGeometry.Scheme.Modules.rankStratum_eq_iSup_connectedComponentOpens` — a connected
  component lies in the locus of the rank `E` has on it, and each rank locus is the union of the
  components of that rank.
* `Stacks.Chow.topChernClass_rankStratum` and `Stacks.Chow.topChernClass_of_ne_rank` — on the
  locus where the rank is `r` the top Chern class is `c_r` in degree `r`, and it vanishes in every
  other degree.
* `Stacks.Chow.finite_degrees_topChernClass` — if only finitely many rank loci are nonempty, only
  finitely many degrees occur.
* `Stacks.Chow.topChernClassFinite_component` — the finite sum has the top Chern class as its
  image in the completed group.
* `Stacks.Chow.topChernClassFinite_rankStratum` and `Stacks.Chow.topChernClassFinite_of_ne_rank` —
  the componentwise formula for the finite sum.

## Implementation notes

The Chern classes themselves are carried as a parameter `c` rather than taken from
`Stacks.Chow.chernClassBivariant`, the class of Stacks 0B7H: that construction carries the Chern
class cap products of Stacks 02U5 and 02U7 as data and the three naturality axioms of Stacks 0B76
for them as hypotheses, and none of that is used below, where all that is needed of `c i` is that
it is a bivariant class of the rank's degree on the component `X_i`. The same convention is used
by `Stacks.Chow.totalLocalizedChernClass`.

The components of the completed bivariant group of Stacks 0FE0 are indexed by the connected
components of `X`, so the family `c` is indexed by them too: `c i` is the Chern class
`c_r(E|_{X_i})` of the restriction of `E` to the component `X_i`, where `r` is the rank of `E`
there. A rank locus `X_r` is the union of the connected components of rank `r`, by
`AlgebraicGeometry.Scheme.Modules.rankStratum_eq_iSup_connectedComponentOpens`, and Stacks 0FDZ
identifies `A^*(X_r)` with the product of the `A^*(X_i)` over those components; so the statements
below, which read the top Chern class on the connected components contained in a rank locus, say
exactly that its component on `X_r` is `c_r(E|_{X_r})`.

Local Noetherianity of `X` is assumed as an instance rather than derived in each declaration. It
follows from local finite type over the base by
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`, so it is no extra hypothesis, and
being a `Prop` class it agrees with the instance `Stacks.Chow.completedBivariantGroup` supplies
internally.

Stacks 02S1 and Stacks 02S2 along the legs of a cartesian square are theorems, not hypotheses, of
the identification of Stacks 0FDZ: see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly`. What it still carries are the
three Gysin compatibilities of a `Stacks.Chow.GysinSystem`, exactly as the library's form of that tag
does; they are `Prop`s, so substituting the genuine statements recovers the tag verbatim. Only the
declarations that use the identification carry them: the top Chern class itself and its degreewise
description need none.

## References

* [Stacks Project, Tag 0FA4](https://stacks.math.columbia.edu/tag/0FA4)
* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The connected components of a locally connected scheme are a decomposition of it into open
and closed subschemes: they are pairwise disjoint and they cover. -/
theorem isClopenDecomposition_connectedComponentOpens (X : Scheme.{u})
    [LocallyConnectedSpace X] :
    Stacks.Chow.IsClopenDecomposition X.connectedComponentOpens :=
  ⟨fun _ _ h ↦ X.disjoint_connectedComponentOpens h, X.iSup_connectedComponentOpens⟩

namespace Modules

variable {X : Scheme.{u}} (E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- The rank of a finite locally free module on a connected component of a scheme. The rank is
locally constant, hence constant on a connected component, so it descends to the set of
components. -/
def rankOnConnectedComponent : ConnectedComponents X → ℕ :=
  Quotient.lift ⇑(finiteLocallyFreeRank E) fun _ _ h ↦
    (finiteLocallyFreeRank E).apply_eq_of_isPreconnected isPreconnected_connectedComponent
      (connectedComponent_eq_iff_mem.1 h) mem_connectedComponent

/-- The rank of a finite locally free module on the connected component of a point `x` is its
rank at `x`. -/
@[simp]
theorem rankOnConnectedComponent_mk (x : X) :
    rankOnConnectedComponent E (ConnectedComponents.mk x) = finiteLocallyFreeRank E x :=
  rfl

variable [LocallyConnectedSpace X]

/-- A connected component of a scheme lies in the locus where a finite locally free module has
the rank it has on that component. -/
theorem connectedComponentOpens_le_rankStratum (i : ConnectedComponents X) :
    X.connectedComponentOpens i ≤ rankStratum E (rankOnConnectedComponent E i) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe i
  intro y hy
  exact (finiteLocallyFreeRank E).apply_eq_of_isPreconnected isPreconnected_connectedComponent
    (ConnectedComponents.coe_eq_coe'.1 hy) mem_connectedComponent

/-- A connected component contained in the locus where the rank is `r` is a component on which
the rank is `r`. -/
theorem rankOnConnectedComponent_eq_of_le_rankStratum {i : ConnectedComponents X} {r : ℕ}
    (h : X.connectedComponentOpens i ≤ rankStratum E r) :
    rankOnConnectedComponent E i = r := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe i
  exact (mem_rankStratum E).1 (h (rfl : ConnectedComponents.mk x = _))

/-- The locus where a finite locally free module has rank `r` is nonempty as soon as some
connected component has rank `r` there. -/
theorem nonempty_rankStratum_rankOnConnectedComponent (i : ConnectedComponents X) :
    (rankStratum E (rankOnConnectedComponent E i) : Set X).Nonempty := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe i
  exact ⟨x, connectedComponentOpens_le_rankStratum E _ (rfl : ConnectedComponents.mk x = _)⟩

/-- Each rank locus of a finite locally free module is the union of the connected components on
which the rank takes that value. -/
theorem rankStratum_eq_iSup_connectedComponentOpens (r : ℕ) :
    rankStratum E r =
      ⨆ i ∈ {i : ConnectedComponents X | rankOnConnectedComponent E i = r},
        X.connectedComponentOpens i := by
  refine le_antisymm (fun x hx ↦ ?_) (iSup₂_le fun i hi ↦ ?_)
  · refine Opens.mem_iSup.2 ⟨ConnectedComponents.mk x, ?_⟩
    have hr : rankOnConnectedComponent E (ConnectedComponents.mk x) = r := (mem_rankStratum E).1 hx
    exact Opens.mem_iSup.2 ⟨hr, (rfl : ConnectedComponents.mk x = _)⟩
  · exact hi ▸ connectedComponentOpens_le_rankStratum E i

end Modules

end AlgebraicGeometry.Scheme

namespace Stacks.Chow

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] [IsLocallyNoetherian X] (E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **Stacks 0FDZ** at the decomposition of `X` into its connected components: a bivariant class
of degree `p` for the identity of `X` is the same thing as a family of bivariant classes of degree
`p`, one on each connected component of `X`. -/
def connectedComponentBivariantEquiv (p : ℤ)
    (hgysO : G.IsNaturalUnderOpenImmersion)
    (hgysR : G.IsNaturalUnderOpensRestriction) (hgysC : G.IsNaturalUnderPullbackComp) :
    BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p ≃+
      ∀ i : ConnectedComponents X,
        BivariantClass C G ((X.connectedComponentOpens i).ι ≫ sX)
          ((X.connectedComponentOpens
            ((Scheme.Hom.continuous (𝟙 X)).connectedComponentsMap i)).ι ≫ sX)
          (Scheme.Hom.resConnectedComponent (𝟙 X) i)
          (Scheme.Hom.resConnectedComponent_comp_ι_comp (𝟙 X) (Category.id_comp sX) i) p :=
  bivariantPieceEquiv C G sX sX (𝟙 X) (Category.id_comp sX) X.connectedComponentOpens
    X.connectedComponentOpens ((Scheme.Hom.continuous (𝟙 X)).connectedComponentsMap)
    (Scheme.Hom.connectedComponentOpens_le_preimage (𝟙 X))
    X.isClopenDecomposition_connectedComponentOpens p hgysO hgysR hgysC

variable (c : ∀ i : ConnectedComponents X,
  BivariantClass C G ((X.connectedComponentOpens i).ι ≫ sX)
    ((X.connectedComponentOpens ((Scheme.Hom.continuous (𝟙 X)).connectedComponentsMap i)).ι ≫ sX)
    (Scheme.Hom.resConnectedComponent (𝟙 X) i)
    (Scheme.Hom.resConnectedComponent_comp_ι_comp (𝟙 X) (Category.id_comp sX) i)
    (Scheme.Modules.rankOnConnectedComponent E i : ℤ))

/-- **Stacks 0FA4.** The top Chern class `c_top(E) = Σ_r c_r(E|_{X_r})` of a finite locally free
module `E` on `X`, as an element of the completed bivariant group `A^*(X)^∧`: on a connected
component `X_i` of `X` the rank of `E` is a constant `r`, and there the class is the `r`-th Chern
class `c i` of `E|_{X_i}`, placed in degree `r`. -/
@[stacks 0FA4 "completed top Chern class"]
def topChernClass : completedBivariantGroup C G sX sX (𝟙 X) (Category.id_comp sX) :=
  fun i ↦ DirectSum.of _ (Scheme.Modules.rankOnConnectedComponent E i : ℤ) (c i)

/-- **Stacks 0FA4.** On the locus where `E` has rank `r` the top Chern class is the `r`-th Chern
class, in degree `r`: a connected component `X_i` lies in the locus of the rank `r` of `E` on it,
and the degree-`r` part of `c_top(E)` there is `c_r(E|_{X_i})`. -/
@[stacks 0FA4 "rank-locus Chern component"]
theorem topChernClass_rankStratum (i : ConnectedComponents X) :
    X.connectedComponentOpens i ≤
        Scheme.Modules.rankStratum E (Scheme.Modules.rankOnConnectedComponent E i) ∧
      topChernClass C G sX E c i (Scheme.Modules.rankOnConnectedComponent E i : ℤ) = c i :=
  ⟨Scheme.Modules.connectedComponentOpens_le_rankStratum E i,
    DirectSum.of_eq_same (Scheme.Modules.rankOnConnectedComponent E i : ℤ) (c i)⟩

/-- **Stacks 0FA4.** The top Chern class has no component in a degree other than the rank: on a
connected component on which `E` has rank `r`, the degree-`p` part of `c_top(E)` vanishes for
every `p ≠ r`. -/
@[stacks 0FA4 "off-rank vanishing"]
theorem topChernClass_of_ne_rank (i : ConnectedComponents X) (p : ℤ)
    (h : p ≠ (Scheme.Modules.rankOnConnectedComponent E i : ℤ)) :
    topChernClass C G sX E c i p = 0 :=
  DirectSum.of_eq_of_ne (Scheme.Modules.rankOnConnectedComponent E i : ℤ) p (c i) h

/-- **Stacks 0FA4.** If only finitely many of the loci `X_r` are nonempty, then only finitely many
degrees occur in the top Chern class, so it lies in the ordinary graded group `A^*(X)` inside its
completion. -/
@[stacks 0FA4 "finite-rank-locus case"]
theorem finite_degrees_topChernClass
    (hfin : {r : ℕ | (Scheme.Modules.rankStratum E r : Set X).Nonempty}.Finite) :
    {p : ℤ | ∃ i : ConnectedComponents X, topChernClass C G sX E c i p ≠ 0}.Finite := by
  refine (hfin.image (fun r : ℕ ↦ (r : ℤ))).subset ?_
  rintro p ⟨i, hp⟩
  refine ⟨Scheme.Modules.rankOnConnectedComponent E i,
    Scheme.Modules.nonempty_rankStratum_rankOnConnectedComponent E i, ?_⟩
  by_contra hne
  exact hp (topChernClass_of_ne_rank C G sX E c i p (Ne.symm hne))

section Finite

variable (hgysO : G.IsNaturalUnderOpenImmersion) (hgysR : G.IsNaturalUnderOpensRestriction)
  (hgysC : G.IsNaturalUnderPullbackComp)

/-- The degree-`p` part of the top Chern class, as a bivariant class of degree `p` on `X`: the
class whose restriction to each connected component of `X` is the degree-`p` part of the top Chern
class there. -/
def topChernClassDegree (p : ℤ) : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p :=
  (connectedComponentBivariantEquiv C G sX p hgysO hgysR hgysC).symm
    fun i ↦ topChernClass C G sX E c i p

/-- On each connected component of `X`, the degree-`p` part of the top Chern class restricts to
the degree-`p` part of the top Chern class on that component. -/
theorem connectedComponentBivariantEquiv_topChernClassDegree (p : ℤ)
    (i : ConnectedComponents X) :
    connectedComponentBivariantEquiv C G sX p hgysO hgysR hgysC
        (topChernClassDegree C G sX E c hgysO hgysR hgysC p) i =
      topChernClass C G sX E c i p :=
  congrFun (AddEquiv.apply_symm_apply _ _) i

/-- **Stacks 0FA4.** The top Chern class `c_top(E) = Σ_r c_r(E|_{X_r})` as an ordinary
nonhomogeneous bivariant class on `X`, when only finitely many of the loci `X_r` are nonempty: the
sum, over the ranks `r` that occur, of the degree-`r` part of the top Chern class. -/
@[stacks 0FA4 "ordinary finite top Chern class"]
def topChernClassFinite
    (hfin : {r : ℕ | (Scheme.Modules.rankStratum E r : Set X).Nonempty}.Finite) :
    nonhomogeneousBivariantGroup C G sX sX (𝟙 X) (Category.id_comp sX) :=
  ∑ r ∈ hfin.toFinset, DirectSum.of _ (r : ℤ)
    (topChernClassDegree C G sX E c hgysO hgysR hgysC (r : ℤ))

/-- The finite top Chern class is the sum, over the ranks that occur, of the degree-`r` part of
the top Chern class placed in degree `r`. -/
theorem topChernClassFinite_eq
    (hfin : {r : ℕ | (Scheme.Modules.rankStratum E r : Set X).Nonempty}.Finite) :
    topChernClassFinite C G sX E c hgysO hgysR hgysC hfin =
      ∑ r ∈ hfin.toFinset, DirectSum.of _ (r : ℤ)
        (topChernClassDegree C G sX E c hgysO hgysR hgysC (r : ℤ)) :=
  rfl

/-- In a degree `r` for which the locus where `E` has rank `r` is nonempty, the finite top Chern
class is the degree-`r` part of the top Chern class. -/
theorem topChernClassFinite_natCast
    (hfin : {r : ℕ | (Scheme.Modules.rankStratum E r : Set X).Nonempty}.Finite) (r : ℕ)
    (hr : (Scheme.Modules.rankStratum E r : Set X).Nonempty) :
    topChernClassFinite C G sX E c hgysO hgysR hgysC hfin (r : ℤ) =
      topChernClassDegree C G sX E c hgysO hgysR hgysC (r : ℤ) := by
  rw [topChernClassFinite_eq, DirectSum.sum_apply, Finset.sum_eq_single r]
  · exact DirectSum.of_eq_same (r : ℤ) _
  · intro b _ hb
    exact DirectSum.of_eq_of_ne (b : ℤ) (r : ℤ) _ fun he ↦ hb (Nat.cast_injective he).symm
  · intro h
    exact absurd (hfin.mem_toFinset.2 hr) h

/-- The finite top Chern class vanishes in every degree `p` that is not the rank of `E` at any
point of `X`. -/
theorem topChernClassFinite_eq_zero
    (hfin : {r : ℕ | (Scheme.Modules.rankStratum E r : Set X).Nonempty}.Finite) (p : ℤ)
    (hp : ∀ r : ℕ, (Scheme.Modules.rankStratum E r : Set X).Nonempty → (r : ℤ) ≠ p) :
    topChernClassFinite C G sX E c hgysO hgysR hgysC hfin p = 0 := by
  rw [topChernClassFinite_eq, DirectSum.sum_apply, Finset.sum_eq_zero]
  intro b hb
  exact DirectSum.of_eq_of_ne (b : ℤ) p _ (Ne.symm (hp b (hfin.mem_toFinset.1 hb)))

/-- **Stacks 0FA4.** The finite sum `Σ_r c_r(E|_{X_r})` has the completed top Chern class as its
image under the identification of Stacks 0FDZ: in every degree and on every connected component,
its restriction is the corresponding part of `c_top(E)`. -/
@[stacks 0FA4 "finite-class canonical image"]
theorem topChernClassFinite_component
    (hfin : {r : ℕ | (Scheme.Modules.rankStratum E r : Set X).Nonempty}.Finite) (p : ℤ)
    (i : ConnectedComponents X) :
    connectedComponentBivariantEquiv C G sX p hgysO hgysR hgysC
        (topChernClassFinite C G sX E c hgysO hgysR hgysC hfin p) i =
      topChernClass C G sX E c i p := by
  by_cases hp : ∃ r : ℕ, (Scheme.Modules.rankStratum E r : Set X).Nonempty ∧ (r : ℤ) = p
  · obtain ⟨r, hr, rfl⟩ := hp
    rw [topChernClassFinite_natCast C G sX E c hgysO hgysR hgysC hfin r hr]
    exact connectedComponentBivariantEquiv_topChernClassDegree C G sX E c hgysO
      hgysR hgysC (r : ℤ) i
  · have hp' : ∀ r : ℕ, (Scheme.Modules.rankStratum E r : Set X).Nonempty → (r : ℤ) ≠ p :=
      fun r hr hrp ↦ hp ⟨r, hr, hrp⟩
    rw [topChernClassFinite_eq_zero C G sX E c hgysO hgysR hgysC hfin p hp',
      map_zero, Pi.zero_apply,
      topChernClass_of_ne_rank C G sX E c i p
        (Ne.symm (hp' _ (Scheme.Modules.nonempty_rankStratum_rankOnConnectedComponent E i)))]

/-- **Stacks 0FA4.** On the locus where `E` has rank `r`, the component of the finite sum
`Σ_r c_r(E|_{X_r})` in degree `r` is the `r`-th Chern class: a connected component `X_i` lies in
the locus of the rank `r` of `E` on it, and the degree-`r` component of the sum there is
`c_r(E|_{X_i})`. -/
@[stacks 0FA4 "finite-sum rank component"]
theorem topChernClassFinite_rankStratum
    (hfin : {r : ℕ | (Scheme.Modules.rankStratum E r : Set X).Nonempty}.Finite)
    (i : ConnectedComponents X) :
    X.connectedComponentOpens i ≤
        Scheme.Modules.rankStratum E (Scheme.Modules.rankOnConnectedComponent E i) ∧
      connectedComponentBivariantEquiv C G sX
          (Scheme.Modules.rankOnConnectedComponent E i : ℤ) hgysO hgysR hgysC
          (topChernClassFinite C G sX E c hgysO hgysR hgysC hfin
            (Scheme.Modules.rankOnConnectedComponent E i : ℤ)) i = c i :=
  ⟨Scheme.Modules.connectedComponentOpens_le_rankStratum E i,
    (topChernClassFinite_component C G sX E c hgysO hgysR hgysC hfin
      (Scheme.Modules.rankOnConnectedComponent E i : ℤ) i).trans
        (topChernClass_rankStratum C G sX E c i).2⟩

/-- **Stacks 0FA4.** The finite sum `Σ_r c_r(E|_{X_r})` has no component in a degree other than
the rank: on a connected component on which `E` has rank `r`, its degree-`p` component vanishes
for every `p ≠ r`. -/
@[stacks 0FA4 "finite-sum off-rank component"]
theorem topChernClassFinite_of_ne_rank
    (hfin : {r : ℕ | (Scheme.Modules.rankStratum E r : Set X).Nonempty}.Finite)
    (i : ConnectedComponents X) (p : ℤ)
    (h : p ≠ (Scheme.Modules.rankOnConnectedComponent E i : ℤ)) :
    connectedComponentBivariantEquiv C G sX p hgysO hgysR hgysC
        (topChernClassFinite C G sX E c hgysO hgysR hgysC hfin p) i = 0 :=
  (topChernClassFinite_component C G sX E c hgysO hgysR hgysC hfin p i).trans
    (topChernClass_of_ne_rank C G sX E c i p h)

end Finite

end Stacks.Chow

end
