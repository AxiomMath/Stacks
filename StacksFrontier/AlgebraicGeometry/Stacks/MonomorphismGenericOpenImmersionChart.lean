module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleLocalDimension
public import StacksFrontier.AlgebraicGeometry.Descent.SurjectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Etale.FpqcDescentApplication.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Etale.UniversallyInjectiveUnramified.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.EtaleLocalStructure.ClosedImmersionOpens
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres
public import StacksFrontier.Topology.Dimension.NowhereDense

/-!
# The chart-level kernel of Stacks 0DS2

Stacks 0DS2 says that a locally finite type monomorphism `𝒯 ⟶ 𝒳` of algebraic stacks, with `𝒳`
reduced of dimension at most the dimension `d` of the irreducible `𝒯`, is an open immersion onto
an open subset of an irreducible component of `𝒳` after restricting `𝒯` to a non-empty open
substack. Its proof passes to a smooth surjective chart `U ⟶ 𝒳` by a scheme — reduced because
`𝒳` is — and to the base change `U' = 𝒯 ×_𝒳 U`, which is a scheme because `U' ⟶ U` is a locally
finite type monomorphism. The whole geometric content of the argument is then a statement about
the morphism of schemes `U' ⟶ U`, and that statement is what this module proves.

## Main results

* `AlgebraicGeometry.exists_opens_isOpenImmersion_comp_of_mono_of_topologicalKrullDimAt_le`:
  let `g : X ⟶ Y` be a monomorphism of schemes which is locally of finite type, with `Y` reduced
  and locally Noetherian, and let `x` be a point of `X` at which the local dimension does not
  drop, `dim_{g x}(Y) ≤ dim_x(X)`, the value being finite. Then some non-empty open subscheme
  `W` of `X` has `W ⟶ Y` étale, hence an open immersion.

In the application `g` is `U' ⟶ U`, the hypothesis on local dimensions at `x` is the inequality
`dim_{u'}(U') ≥ dim_u(U)` of **Stacks 0DS3** — which the stack-level argument gets from Stacks
0DRN, 0DRP and 0DRX — and the conclusion is the chart-level conclusion of Stacks 0DS2: the
composite `W ⟶ U ⟶ 𝒳` of the open immersion with the smooth chart is smooth.

## The argument

Being a monomorphism locally of finite type, `g` is unramified (**Stacks 05VH**, through
`AlgebraicGeometry.universallyInjective_unramified_tfae`) and separated. The étale-local
structure of an unramified morphism at a point, **Stacks 04HH**
(`AlgebraicGeometry.exists_etaleNeighborhood_isClosedImmersion_opens_of_unramifiedAt`, the
theorem on which **Stacks 04HI** rests), therefore produces an étale neighbourhood `p : V ⟶ Y`
of `g x` and a commutative square

```
A ---e---> X
|          |
c          g
v          v
V ---p---> Y
```

in which `e` is étale, `c` is a closed immersion, and `A` has a point `z` over the distinguished
point of `V` with `e z = x`. The square is the input of the private
`exists_opens_isOpenImmersion_comp_of_closedImmersion_square`, which carries out the rest; `A` is
produced as an open subscheme of the base change `X ×_Y V`, inside which the required point
exists because the points of a fibre product of schemes surject onto the fibre product of the
point sets.

Since étale morphisms preserve the local dimension (**Stacks 04N4**,
`AlgebraicGeometry.topologicalKrullDimAt_eq_of_etale`), the hypothesis on `x` transports to
`dim_{c z}(V) ≤ dim_z(A)`. Writing `Z = range c`, a closed subset of `V`, this forces `Z` to
contain a non-empty open subset of `V`: pick a Noetherian open neighbourhood `N` of `c z` whose
Krull dimension realizes the local dimension of `V` at `c z`, which is possible because `V` is
locally Noetherian and the local dimension is attained
(`topologicalKrullDimAt_isLeast`); then `Z ∩ N` has the dimension of `N`, so `Z ∩ N` is not
nowhere dense in `N` (`IsNowhereDense.topologicalKrullDim_lt`, which is where the finiteness of
the dimension is used), and being closed it has non-empty interior.

Let `O` be such a non-empty open subset of `V` inside `Z`, chosen inside the preimage of an
affine open of `Y`, so that `O` is reduced: a scheme smooth over a reduced affine scheme is
reduced (**Stacks 033B**, through
`AlgebraicGeometry.isReduced_of_smooth_of_isAffine`). The restriction `c ∣_ O` is a surjective
closed immersion onto the reduced `O`, hence an isomorphism. Finally `W` is the image of
`c ⁻¹ᵁ O` under `e`, an open subset of `X` since `e` is étale; the induced `c ⁻¹ᵁ O ⟶ W` is
étale and surjective, and composing it with `W ⟶ Y` gives `(c ∣_ O) ≫ O.ι ≫ p`, which is étale.
So `W ⟶ Y` is étale by descent along a surjective étale morphism of sources (**Stacks 02KM**,
`Stacks.Etale.etale_of_comp_surjective_etale`), and being also a monomorphism it is an open
immersion (**Stacks 025G**, through
`AlgebraicGeometry.isOpenImmersion_of_etale_universallyInjective`).

## Implementation notes

The finiteness of `dim_{g x}(Y)` is an honest hypothesis of the scheme-level statement, not a
weakening: the inequality alone does not force a proper closed subset of a Noetherian space to
have smaller dimension, as `IsNowhereDense.topologicalKrullDim_lt` records. In Stacks 0DS2 it
comes for free, the dimension of `𝒯` there being the natural number `d`.

No `@[stacks]` attribute is placed. Stacks 0DS3 is the *equation* `dim_{u'}(U') ≥ dim_u(U)`
inside the proof of Stacks 0DS2, which is this module's hypothesis rather than its conclusion,
and Stacks 0DS2 itself is a statement about algebraic stacks; the registration of 0DS2 belongs
to `StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismGenericOpenImmersion`.

## References

* [Stacks Project, Tag 025G](https://stacks.math.columbia.edu/tag/025G)
* [Stacks Project, Tag 02KM](https://stacks.math.columbia.edu/tag/02KM)
* [Stacks Project, Tag 033B](https://stacks.math.columbia.edu/tag/033B)
* [Stacks Project, Tag 04HH](https://stacks.math.columbia.edu/tag/04HH)
* [Stacks Project, Tag 04HI](https://stacks.math.columbia.edu/tag/04HI)
* [Stacks Project, Tag 04N4](https://stacks.math.columbia.edu/tag/04N4)
* [Stacks Project, Tag 05VH](https://stacks.math.columbia.edu/tag/05VH)
* [Stacks Project, Tag 0DS2](https://stacks.math.columbia.edu/tag/0DS2)
* [Stacks Project, Tag 0DS3](https://stacks.math.columbia.edu/tag/0DS3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-- **A closed subset of a Noetherian space whose dimension is that of the whole space contains a
non-empty open subset.** Were it not so the subset would have empty interior, hence be nowhere
dense, and `IsNowhereDense.topologicalKrullDim_lt` would make its dimension strictly smaller. -/
private theorem exists_isOpen_nonempty_subset_of_topologicalKrullDim_le
    {T : Type*} [TopologicalSpace T] [NoetherianSpace T] [Nonempty T] {Z : Set T}
    (hZ : IsClosed Z) (hfin : topologicalKrullDim T ≠ ⊤)
    (hdim : topologicalKrullDim T ≤ topologicalKrullDim Z) :
    ∃ O : Set T, IsOpen O ∧ O.Nonempty ∧ O ⊆ Z := by
  by_contra hcon
  have hint : interior Z = ∅ := by
    by_contra h
    exact hcon ⟨interior Z, isOpen_interior, Set.nonempty_iff_ne_empty.mpr h, interior_subset⟩
  have hnd : IsNowhereDense Z := by rw [IsNowhereDense, hZ.closure_eq]; exact hint
  exact absurd (hnd.topologicalKrullDim_lt hZ ‹Nonempty T› hfin) (not_lt.mpr hdim)

namespace AlgebraicGeometry

/-- The geometric heart of Stacks 0DS2, with the étale-local structure of the unramified
morphism `g` already extracted as a commutative square: `e` and `p` étale, `c` a closed
immersion, and a point `z` of `A` at which the local dimension of `V` does not exceed that of
`A`. Then a non-empty open subscheme of `X` is an open immersion over `Y`. -/
private theorem exists_opens_isOpenImmersion_comp_of_closedImmersion_square
    {X Y V A : Scheme.{u}} (g : X ⟶ Y) [Mono g] [IsReduced Y] [IsLocallyNoetherian Y]
    (p : V ⟶ Y) [Etale p] (c : A ⟶ V) [IsClosedImmersion c] (e : A ⟶ X) [Etale e]
    (hsq : e ≫ g = c ≫ p) (z : A)
    (hdim : topologicalKrullDimAt V (c z) ≤ topologicalKrullDimAt A z)
    (hfin : topologicalKrullDimAt V (c z) ≠ ⊤) :
    ∃ W : X.Opens, (W : Set X).Nonempty ∧ Etale (W.ι ≫ g) ∧
      IsOpenImmersion (W.ι ≫ g) := by
  classical
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian p
  -- An affine open of `Y` around the image of `z`, over which `V` is reduced.
  obtain ⟨Y₀, hY₀aff, hY₀mem, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := p (c z)) (U := ⊤) (Opens.mem_top _)
  have hmem₀ : c z ∈ p ⁻¹ᵁ Y₀ := hY₀mem
  have : IsAffine Y₀.toScheme := hY₀aff
  have : IsReduced Y₀.toScheme := isReduced_of_isOpenImmersion Y₀.ι
  have : IsReduced (p ⁻¹ᵁ Y₀).toScheme := isReduced_of_smooth_of_isAffine (p ∣_ Y₀)
  -- An affine, hence Noetherian, open neighbourhood of `c z` inside it.
  obtain ⟨N₀, hN₀aff, hN₀mem, hN₀sub⟩ :=
    exists_isAffineOpen_mem_and_subset (x := c z) (U := p ⁻¹ᵁ Y₀) hmem₀
  have : IsNoetherianRing Γ(V, N₀) := IsLocallyNoetherian.component_noetherian ⟨N₀, hN₀aff⟩
  have hN₀noeth : NoetherianSpace ↥(N₀ : Set V) := noetherianSpace_of_isAffineOpen N₀ hN₀aff
  -- A Noetherian open neighbourhood of `c z` inside it whose Krull dimension is the local
  -- dimension of `V` at `c z`; the local dimension is attained, by `topologicalKrullDimAt`.
  obtain ⟨N, hNopen, hNmem, hNsub, hNnoeth, hNdim⟩ : ∃ N : Set V, IsOpen N ∧ c z ∈ N ∧
      N ⊆ (N₀ : Set V) ∧ NoetherianSpace ↥N ∧
      topologicalKrullDim ↥N = topologicalKrullDimAt V (c z) := by
    obtain ⟨⟨D, hDmem, hDopen, hDdim⟩, hDleast⟩ := topologicalKrullDimAt_isLeast V (c z)
    refine ⟨(N₀ : Set V) ∩ D, N₀.2.inter hDopen, ⟨hN₀mem, hDmem⟩, Set.inter_subset_left,
      NoetherianSpace.of_subset (W := (N₀ : Set V)) Set.inter_subset_left, le_antisymm ?_ ?_⟩
    · rw [hDdim]; exact topologicalKrullDim_le_of_subset Set.inter_subset_right
    · exact hDleast ⟨(N₀ : Set V) ∩ D, ⟨hN₀mem, hDmem⟩, N₀.2.inter hDopen, rfl⟩
  have : NoetherianSpace ↥N := hNnoeth
  have : Nonempty ↥N := ⟨⟨c z, hNmem⟩⟩
  -- The range of the closed immersion `c`, a closed subset of `V` of full local dimension.
  have hZclosed : IsClosed (Set.range c) := c.isClosedEmbedding.isClosed_range
  have hSdim : topologicalKrullDim ↥N ≤
      topologicalKrullDim ↥((Subtype.val : ↥N → V) ⁻¹' Set.range c) := by
    have hpre : ((Subtype.val : ↥N → V) ⁻¹' Set.range c) =
        ((Subtype.val : ↥N → V) ⁻¹' (Set.range c ∩ N)) := by
      ext t
      exact ⟨fun h => ⟨h, t.2⟩, fun h => h.1⟩
    have hind : Topology.IsInducing
        (fun t : ↥(⇑c ⁻¹' N) => (⟨c t.1, ⟨t.1, rfl⟩, t.2⟩ : ↥(Set.range c ∩ N))) :=
      Topology.IsInducing.subtypeVal.of_comp_iff.mp
        (c.isClosedEmbedding.isEmbedding.isInducing.comp Topology.IsInducing.subtypeVal)
    calc topologicalKrullDim ↥N
        = topologicalKrullDimAt V (c z) := hNdim
      _ ≤ topologicalKrullDimAt A z := hdim
      _ ≤ topologicalKrullDim ↥(⇑c ⁻¹' N) :=
          (topologicalKrullDimAt_isLeast A z).2
            ⟨_, hNmem, hNopen.preimage c.continuous, rfl⟩
      _ ≤ topologicalKrullDim ↥(Set.range c ∩ N) := hind.topologicalKrullDim_le
      _ = _ := by
          rw [hpre]
          exact (topologicalKrullDim_preimage_val N _ Set.inter_subset_right).symm
  -- Hence the range of `c` contains a non-empty open subset `O` of `V`.
  obtain ⟨O, hOsubZ, hOsubN, hOne⟩ : ∃ O : V.Opens, (O : Set V) ⊆ Set.range c ∧
      (O : Set V) ⊆ (N₀ : Set V) ∧ (O : Set V).Nonempty := by
    obtain ⟨O', hO'open, hO'ne, hO'sub⟩ :=
      exists_isOpen_nonempty_subset_of_topologicalKrullDim_le
        (T := ↥N) (hZclosed.preimage continuous_subtype_val)
        (by rw [hNdim]; exact hfin) hSdim
    refine ⟨⟨Subtype.val '' O', hNopen.isOpenEmbedding_subtypeVal.isOpenMap _ hO'open⟩,
      ?_, ?_, hO'ne.image _⟩
    · rintro _ ⟨t, ht, rfl⟩; exact hO'sub ht
    · rintro _ ⟨t, -, rfl⟩; exact hNsub t.2
  -- `O` is reduced, being an open subscheme of a scheme smooth over a reduced affine scheme.
  have hOle : O ≤ p ⁻¹ᵁ Y₀ := fun _ h => hN₀sub (hOsubN h)
  have : IsReduced O.toScheme := isReduced_of_isOpenImmersion (V.homOfLE hOle)
  -- The restriction of `c` over `O` is a surjective closed immersion, hence an isomorphism.
  have : IsClosedImmersion (c ∣_ O) :=
    IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) inferInstance O
  -- Every point of `O` lifts to a point of `c ⁻¹ᵁ O`, since `O` lies in the range of `c`.
  have hlift : ∀ o ∈ (O : Set V), ∃ w : (c ⁻¹ᵁ O).toScheme, c w.1 = o := fun o ho => by
    obtain ⟨w, hw⟩ := hOsubZ ho
    exact ⟨⟨w, show c w ∈ O by rw [hw]; exact ho⟩, hw⟩
  have : Surjective (c ∣_ O) := by
    refine ⟨fun t => ?_⟩
    obtain ⟨w, hw⟩ := hlift t.1 t.2
    exact ⟨w, Subtype.ext (by rw [morphismRestrict_base_coe]; exact hw)⟩
  have : IsIso (c ∣_ O) := isIso_of_isClosedImmersion_of_surjective _
  -- `W` is the image of `c ⁻¹ᵁ O` under the étale morphism `e`.
  obtain ⟨W, hWrange⟩ : ∃ W : X.Opens, (W : Set X) = Set.range ((c ⁻¹ᵁ O).ι ≫ e) :=
    ⟨⟨_, ((c ⁻¹ᵁ O).ι ≫ e).isOpenMap.isOpen_range⟩, rfl⟩
  -- `c ⁻¹ᵁ O ⟶ W` is étale and surjective, and `c ⁻¹ᵁ O ⟶ W ⟶ Y` is étale.
  have hqsub : Set.range ((c ⁻¹ᵁ O).ι ≫ e) ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι, hWrange]
  have hqfac : IsOpenImmersion.lift W.ι ((c ⁻¹ᵁ O).ι ≫ e) hqsub ≫ W.ι =
      (c ⁻¹ᵁ O).ι ≫ e := IsOpenImmersion.lift_fac _ _ _
  have : Surjective (IsOpenImmersion.lift W.ι ((c ⁻¹ᵁ O).ι ≫ e) hqsub) := by
    refine ⟨fun t => ?_⟩
    obtain ⟨w, hw⟩ : t.1 ∈ Set.range ((c ⁻¹ᵁ O).ι ≫ e) := hWrange ▸ t.2
    refine ⟨w, W.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hqfac]
    exact hw.trans (W.ι_apply t).symm
  have : Etale (IsOpenImmersion.lift W.ι ((c ⁻¹ᵁ O).ι ≫ e) hqsub) := by
    have : Etale (IsOpenImmersion.lift W.ι ((c ⁻¹ᵁ O).ι ≫ e) hqsub ≫ W.ι) := by
      rw [hqfac]; infer_instance
    exact Etale.of_comp _ W.ι
  have hcomp : IsOpenImmersion.lift W.ι ((c ⁻¹ᵁ O).ι ≫ e) hqsub ≫ (W.ι ≫ g) =
      (c ∣_ O) ≫ (O.ι ≫ p) := by
    rw [← Category.assoc, hqfac, Category.assoc, hsq, ← Category.assoc,
      ← morphismRestrict_ι, Category.assoc]
  have : Etale (IsOpenImmersion.lift W.ι ((c ⁻¹ᵁ O).ι ≫ e) hqsub ≫ (W.ι ≫ g)) := by
    rw [hcomp]; infer_instance
  have hWet : Etale (W.ι ≫ g) :=
    Stacks.Etale.etale_of_comp_surjective_etale
      (IsOpenImmersion.lift W.ι ((c ⁻¹ᵁ O).ι ≫ e) hqsub) (W.ι ≫ g)
  have : Mono (W.ι ≫ g) := mono_comp _ _
  refine ⟨W, ?_, hWet, inferInstance⟩
  obtain ⟨o, ho⟩ := hOne
  obtain ⟨w, -⟩ := hlift o ho
  exact hWrange ▸ ⟨_, Set.mem_range_self w⟩

/-- **The chart-level conclusion of Stacks 0DS2.** Let `g : X ⟶ Y` be a monomorphism of schemes
which is locally of finite type, with `Y` reduced and locally Noetherian, and let `x` be a point
of `X` at which the local dimension does not drop: `dim_{g x}(Y) ≤ dim_x(X)`, this common bound
being finite. Then some non-empty open subscheme `W` of `X` has `W ⟶ Y` étale, hence an open
immersion.

In Stacks 0DS2, `g` is the base change `U' = 𝒯 ×_𝒳 U ⟶ U` of the monomorphism `𝒯 ⟶ 𝒳` along a
smooth surjective chart `U ⟶ 𝒳` by a scheme, which is reduced because `𝒳` is and locally
Noetherian because `𝒳` is; the hypothesis on the local dimensions at `x` is the inequality
`dim_{u'}(U') ≥ dim_u(U)` of Stacks 0DS3; and the conclusion is what the source needs, since the
composite of `W ⟶ U` with the smooth chart `U ⟶ 𝒳` is then smooth. -/
theorem exists_opens_isOpenImmersion_comp_of_mono_of_topologicalKrullDimAt_le
    {X Y : Scheme.{u}} (g : X ⟶ Y) [Mono g] [LocallyOfFiniteType g]
    [IsReduced Y] [IsLocallyNoetherian Y] (x : X)
    (hdim : topologicalKrullDimAt Y (g x) ≤ topologicalKrullDimAt X x)
    (hfin : topologicalKrullDimAt Y (g x) ≠ ⊤) :
    ∃ W : X.Opens, (W : Set X).Nonempty ∧ Etale (W.ι ≫ g) ∧
      IsOpenImmersion (W.ι ≫ g) := by
  classical
  -- Stacks 05VH: a monomorphism locally of finite type is unramified.
  have hunr : Unramified g := by
    have hmono : LocallyOfFiniteType g ∧ Mono g := ⟨inferInstance, inferInstance⟩
    have h : Unramified g ∧ Mono g :=
      ((universallyInjective_unramified_tfae g).out 3 1).mp hmono
    exact h.1
  -- Stacks 04HH at the single point `x` of the fibre of `g` over `g x`.
  obtain ⟨E, m, Vop, hVop, -, hcov⟩ :=
    exists_etaleNeighborhood_isClosedImmersion_opens_of_unramifiedAt g 1 (fun _ => x) (g x)
      (fun _ => rfl) (fun i j _ => Subsingleton.elim i j) (fun _ => hunr.unramifiedAt x)
  -- The points of a fibre product surject onto the fibre product of the point sets.
  obtain ⟨zz, hzfst, hzsnd⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := g) (g := E.toBase) x E.point E.map_point.symm
  obtain ⟨jj, hjz⟩ := hcov 0 zz hzsnd hzfst
  have hci : IsClosedImmersion ((Vop ⟨0, jj⟩).ι ≫ pullback.snd g E.toBase) :=
    (hVop ⟨0, jj⟩).1
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : (Vop ⟨0, jj⟩).toScheme, (Vop ⟨0, jj⟩).ι z₀ = zz :=
    ⟨⟨zz, hjz⟩, by simp⟩
  have hcz : ((Vop ⟨0, jj⟩).ι ≫ pullback.snd g E.toBase) z₀ = E.point := by
    rw [Scheme.Hom.comp_apply, hz₀]; exact hzsnd
  have hez : ((Vop ⟨0, jj⟩).ι ≫ pullback.fst g E.toBase) z₀ = x := by
    rw [Scheme.Hom.comp_apply, hz₀]; exact hzfst
  have hsq : ((Vop ⟨0, jj⟩).ι ≫ pullback.fst g E.toBase) ≫ g =
      ((Vop ⟨0, jj⟩).ι ≫ pullback.snd g E.toBase) ≫ E.toBase := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  -- Stacks 04N4 transports the dimension inequality to the square.
  have hdim' : topologicalKrullDimAt E.scheme
      (((Vop ⟨0, jj⟩).ι ≫ pullback.snd g E.toBase) z₀) ≤
      topologicalKrullDimAt (Vop ⟨0, jj⟩).toScheme z₀ := by
    rw [hcz, topologicalKrullDimAt_eq_of_etale E.toBase E.point, E.map_point,
      topologicalKrullDimAt_eq_of_etale ((Vop ⟨0, jj⟩).ι ≫ pullback.fst g E.toBase) z₀, hez]
    exact hdim
  have hfin' : topologicalKrullDimAt E.scheme
      (((Vop ⟨0, jj⟩).ι ≫ pullback.snd g E.toBase) z₀) ≠ ⊤ := by
    rw [hcz, topologicalKrullDimAt_eq_of_etale E.toBase E.point, E.map_point]
    exact hfin
  exact exists_opens_isOpenImmersion_comp_of_closedImmersion_square g E.toBase
    ((Vop ⟨0, jj⟩).ι ≫ pullback.snd g E.toBase)
    ((Vop ⟨0, jj⟩).ι ≫ pullback.fst g E.toBase) hsq z₀ hdim' hfin'

end AlgebraicGeometry

end
