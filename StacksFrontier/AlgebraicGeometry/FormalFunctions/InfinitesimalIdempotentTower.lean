module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.InfinitesimalNeighbourhood

/-!
# Idempotents on the infinitesimal neighbourhoods of a fibre

Let `f : X ⟶ Y` be a morphism of schemes, let `y` be a point of `Y` and let `X_n` be the `n`-th
infinitesimal neighbourhood of the fibre `X_y` of [Stacks, Tag 02OD], as constructed in
`StacksFrontier/AlgebraicGeometry/FormalFunctions/InfinitesimalNeighbourhood.lean`. For `n ≥ 1` all
the `X_n` have the *same underlying topological space* as the fibre, because each of them has
the fibre of `f` over `y` as the range of its projection to `X`. Consequently an idempotent
global function on `X_1 = X_y` lifts, compatibly, to an idempotent global function on every
`X_n`.

That tower of idempotents is the first half of the proof of [Stacks, Tag 0G7X]: it produces a
compatible system in `limₙ H⁰(X_n, 𝒪_{X_n})`, which the theorem on formal functions in its
stalk form [Stacks, Tag 02OD] identifies with the completed stalk of `f_* 𝒪_X` at `y`. **Nothing
about that identification is used or proved here**; everything in this file is unconditional.

## Main definitions

* `Stacks.FormalFunctions.infinitesimalIdempotent`: the tower of idempotents. Its value at `n` is
  an idempotent of `Γ(X_{n+1}, 𝒪)` restricting to the given idempotent of `Γ(X_y, 𝒪)`.

## Main results

* `Stacks.FormalFunctions.exists_isIdempotentElem_appTop_eq_of_isHomeomorph`: **idempotents lift
  along a morphism which is a homeomorphism on spaces.** If `i : Z ⟶ W` is a morphism of schemes
  whose underlying map is a homeomorphism, then every idempotent of `Γ(Z, 𝒪_Z)` is the image of
  an idempotent of `Γ(W, 𝒪_W)`. (It need not be the image of a *unique* one, and `i` need not be
  an isomorphism: only the clopen decomposition cut out by the idempotent is transported.)
* `Stacks.FormalFunctions.range_infinitesimalBase`: the range of `c_n` is `{y}` for `n ≥ 1`.
* `Stacks.FormalFunctions.isHomeomorph_infinitesimalTransition`: the transition morphism
  `X_n ⟶ X_m` is a homeomorphism on underlying spaces for `1 ≤ n ≤ m`.
* `Stacks.FormalFunctions.infinitesimalIdempotent_isIdempotentElem`,
  `Stacks.FormalFunctions.infinitesimalIdempotent_restrict` and
  `Stacks.FormalFunctions.infinitesimalIdempotent_zero`: the tower consists of idempotents, is
  compatible with the transition morphisms, and starts at the given idempotent of the fibre.

## Implementation notes

An idempotent `e` of `Γ(Z, 𝒪_Z)` is the same thing as a decomposition of `Z` into the two
disjoint opens `Z_{e ≠ 0}` and `Z_{1 - e ≠ 0}`, and the reconstruction of `e` from that
decomposition is `exists_isIdempotentElem_res_eq_one_res_eq_zero` — gluing the sections `1` and
`0`. Transporting the decomposition along a homeomorphism and gluing again is the proof of
`exists_isIdempotentElem_appTop_eq_of_isHomeomorph`; it is the only place where the sheaf
condition is used.

The tower is indexed so that `infinitesimalIdempotent f y e he n` lives on `X_{n + 1}`: the
zeroth infinitesimal neighbourhood `X_0` is empty (`𝔪_y ^ 0 = 𝒪_{Y,y}`, so the base ring is the
zero ring), and the source's indexing starts at `X_1 = X_y`.

## References

* [Stacks Project, Tag 02OD](https://stacks.math.columbia.edu/tag/02OD)
* [Stacks Project, Tag 0G7X](https://stacks.math.columbia.edu/tag/0G7X)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace Topology

universe u

namespace Stacks.FormalFunctions

/-! ### Idempotent global functions and clopen decompositions -/

/-- **A decomposition of a scheme into two disjoint opens produces an idempotent global
function.** The function is glued from `1` on the first open and `0` on the second; the two agree
on the intersection because the intersection is empty. -/
public theorem exists_isIdempotentElem_res_eq_one_res_eq_zero (X : Scheme.{u})
    (U V : X.Opens) (hcover : ⊤ ≤ U ⊔ V) (hdisj : U ⊓ V = ⊥) :
    ∃ a : Γ(X, ⊤), IsIdempotentElem a ∧
      (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom a = 1 ∧
      (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom a = 0 := by
  let W : Bool → X.Opens := fun b => if b then V else U
  have hW : ⊤ ≤ iSup W := by
    rw [SetLike.le_def]
    intro x hx
    rcases hcover hx with hxU | hxV
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨false, by simpa [W] using hxU⟩
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨true, by simpa [W] using hxV⟩
  let sf : (b : Bool) → Γ(X, W b) := fun b => if b then 0 else 1
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf W sf := by
    intro i j
    cases i <;> cases j
    · exact (map_one _).trans (map_one _).symm
    · have hsub : Subsingleton (Γ(X, W false ⊓ W true)) := by
        simpa [W] using (show Subsingleton (Γ(X, U ⊓ V)) by rw [hdisj]; infer_instance)
      exact Subsingleton.elim _ _
    · have hsub : Subsingleton (Γ(X, W true ⊓ W false)) := by
        simpa [W] using
          (show Subsingleton (Γ(X, V ⊓ U)) by rw [inf_comm, hdisj]; infer_instance)
      exact Subsingleton.elim _ _
    · exact (map_zero _).trans (map_zero _).symm
  obtain ⟨a, ha, -⟩ := X.sheaf.existsUnique_gluing'
    (U := W) (V := ⊤) (iUV := fun _ => homOfLE le_top) hW sf hcompat
  refine ⟨a, ?_, ha false, ha true⟩
  show a * a = a
  refine X.sheaf.eq_of_locally_eq' W ⊤ (fun _ => homOfLE le_top) hW _ _ fun b => ?_
  rw [map_mul, ha b]
  cases b
  · exact one_mul _
  · exact zero_mul _

/-- An idempotent restricts to `1` on the open where it is invertible. -/
public theorem res_basicOpen_eq_one_of_isIdempotentElem (X : Scheme.{u}) (e : Γ(X, ⊤))
    (he : IsIdempotentElem e) :
    (X.presheaf.map (homOfLE (X.basicOpen_le e)).op).hom e = 1 := by
  exact (IsIdempotentElem.iff_eq_one_of_isUnit
    (X.toRingedSpace.isUnit_res_basicOpen e)).mp (he.map _)

/-- An idempotent restricts to `0` on the open where its complement is invertible. -/
public theorem res_basicOpen_one_sub_eq_zero_of_isIdempotentElem (X : Scheme.{u}) (e : Γ(X, ⊤))
    (he : IsIdempotentElem e) :
    (X.presheaf.map (homOfLE (X.basicOpen_le (1 - e))).op).hom e = 0 := by
  have h := res_basicOpen_eq_one_of_isIdempotentElem X (1 - e) he.one_sub
  rw [map_sub, map_one] at h
  have h' : (1 : Γ(X, X.basicOpen (1 - e))) -
      (X.presheaf.map (homOfLE (X.basicOpen_le (1 - e))).op).hom e = 1 := h
  linear_combination (norm := ring_nf) -h'

/-- The two opens cut out by an idempotent cover the scheme. -/
public theorem top_le_basicOpen_sup_basicOpen_one_sub (X : Scheme.{u}) (e : Γ(X, ⊤)) :
    ⊤ ≤ X.basicOpen e ⊔ X.basicOpen (1 - e) := by
  calc (⊤ : X.Opens) = X.basicOpen (1 : Γ(X, ⊤)) := by rw [X.basicOpen_one]
    _ = X.basicOpen (e + (1 - e)) := by congr 1; ring
    _ ≤ X.basicOpen e ⊔ X.basicOpen (1 - e) := X.basicOpen_add_le e (1 - e)

/-- The two opens cut out by an idempotent are disjoint. -/
public theorem basicOpen_inf_basicOpen_one_sub_of_isIdempotentElem (X : Scheme.{u})
    (e : Γ(X, ⊤)) (he : IsIdempotentElem e) :
    X.basicOpen e ⊓ X.basicOpen (1 - e) = ⊥ := by
  have hmul : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  rw [← X.basicOpen_mul, hmul, X.basicOpen_zero]

/-- **Idempotents lift along a morphism which is a homeomorphism on underlying spaces.** Let
`i : Z ⟶ W` be a morphism of schemes whose map of topological spaces is a homeomorphism. Then
every idempotent `e` of `Γ(Z, 𝒪_Z)` is the image of an idempotent of `Γ(W, 𝒪_W)`.

The clopen decomposition of `Z` that `e` cuts out is transported to `W` through the
homeomorphism, and the idempotent it cuts out there restricts to `1` and to `0` on the two
pieces, hence agrees with `e` after pulling back. The morphism `i` is *not* assumed to be an
isomorphism, and the lift is not unique in general. -/
public theorem exists_isIdempotentElem_appTop_eq_of_isHomeomorph {Z W : Scheme.{u}} (i : Z ⟶ W)
    (hi : IsHomeomorph i.base) (e : Γ(Z, ⊤)) (he : IsIdempotentElem e) :
    ∃ a : Γ(W, ⊤), IsIdempotentElem a ∧ i.appTop.hom a = e := by
  let h := hi.homeomorph i.base
  let UZ := Z.basicOpen e
  let VZ := Z.basicOpen (1 - e)
  let UW : W.Opens := ⟨h '' (UZ : Set Z), h.isOpenMap _ UZ.2⟩
  let VW : W.Opens := ⟨h '' (VZ : Set Z), h.isOpenMap _ VZ.2⟩
  have hcoverZ : ⊤ ≤ UZ ⊔ VZ := top_le_basicOpen_sup_basicOpen_one_sub Z e
  have hdisjZ : UZ ⊓ VZ = ⊥ := basicOpen_inf_basicOpen_one_sub_of_isIdempotentElem Z e he
  have hpre : ∀ T : Z.Opens, i ⁻¹ᵁ (⟨h '' (T : Set Z), h.isOpenMap _ T.2⟩ : W.Opens) = T := by
    intro T
    ext z
    show i z ∈ h '' (T : Set Z) ↔ z ∈ T
    refine ⟨fun hz => ?_, fun hz => ⟨z, hz, by simp [h]⟩⟩
    obtain ⟨w, hw, hwi⟩ := hz
    have hwz : w = z := h.injective (by simpa [h] using hwi)
    simpa [hwz] using hw
  have hpreU : i ⁻¹ᵁ UW = UZ := hpre UZ
  have hpreV : i ⁻¹ᵁ VW = VZ := hpre VZ
  have hcoverW : ⊤ ≤ UW ⊔ VW := by
    intro x _
    obtain ⟨z, rfl⟩ := h.surjective x
    rcases hcoverZ (show z ∈ (⊤ : Z.Opens) from trivial) with hz | hz
    · exact Or.inl ⟨z, hz, rfl⟩
    · exact Or.inr ⟨z, hz, rfl⟩
  have hdisjW : UW ⊓ VW = ⊥ := by
    refine SetLike.ext fun x => ⟨?_, by simp⟩
    rintro ⟨hxU, hxV⟩
    obtain ⟨z, hzU, rfl⟩ := hxU
    obtain ⟨w, hwV, hwz⟩ := hxV
    have : w = z := h.injective hwz
    subst this
    have hmem : w ∈ UZ ⊓ VZ := ⟨hzU, hwV⟩
    simp [hdisjZ] at hmem
  obtain ⟨a, ha, haU, haV⟩ :=
    exists_isIdempotentElem_res_eq_one_res_eq_zero W UW VW hcoverW hdisjW
  have key : ∀ (T : Z.Opens) (S : W.Opens) (hTS : T ≤ i ⁻¹ᵁ S) (b : Γ(W, ⊤)),
      (Z.presheaf.map (homOfLE (le_top : T ≤ ⊤)).op).hom (i.appTop.hom b) =
        (i.appLE S T hTS).hom
          ((W.presheaf.map (homOfLE (le_top : S ≤ ⊤)).op).hom b) := by
    intro T S hTS b
    have hT : T ≤ i ⁻¹ᵁ (⊤ : W.Opens) := le_top
    have hstep : (i.appLE ⊤ T hT).hom b =
        (i.appLE S T hTS).hom
          ((W.presheaf.map (homOfLE (le_top : S ≤ ⊤)).op).hom b) := by
      rw [← Scheme.Hom.map_appLE (f := i) (e := hTS)
        (homOfLE (le_top : S ≤ ⊤)).op]
      rfl
    exact hstep
  have happU : (Z.presheaf.map (homOfLE (le_top : UZ ≤ ⊤)).op).hom (i.appTop.hom a) = 1 := by
    rw [key UZ UW hpreU.ge a, haU, map_one]
  have happV : (Z.presheaf.map (homOfLE (le_top : VZ ≤ ⊤)).op).hom (i.appTop.hom a) = 0 := by
    rw [key VZ VW hpreV.ge a, haV, map_zero]
  refine ⟨a, ha, ?_⟩
  refine Z.sheaf.eq_of_locally_eq₂ (homOfLE (le_top : UZ ≤ ⊤)) (homOfLE (le_top : VZ ≤ ⊤))
    hcoverZ _ _ ?_ ?_
  · exact happU.trans (res_basicOpen_eq_one_of_isIdempotentElem Z e he).symm
  · exact happV.trans (res_basicOpen_one_sub_eq_zero_of_isIdempotentElem Z e he).symm

/-! ### The infinitesimal neighbourhoods have the space of the fibre -/

/-- **The `n`-th infinitesimal base `Spec (𝒪_{Y,y}/𝔪_y ^ n) ⟶ Y` has range `{y}`, for
`n ≥ 1`.** The spectrum of `𝒪_{Y,y}/𝔪_y ^ n` has the closed point of `Spec 𝒪_{Y,y}` as its only
image point, because `𝔪_y ^ n` has the same zero locus as `𝔪_y`, and the canonical morphism
`Spec 𝒪_{Y,y} ⟶ Y` takes the closed point to `y`. -/
public theorem specMap_toStalkQuotient_eq_closedPoint {Y : Scheme.{u}} (y : Y) {n : ℕ}
    (hn : 0 < n) (p : Spec (stalkQuotient y n)) :
    (Spec.map (toStalkQuotient y n)).base p =
      IsLocalRing.closedPoint (Y.presheaf.stalk y) := by
  have hmax : (stalkMaximalIdeal y).IsMaximal := IsLocalRing.maximalIdeal.isMaximal _
  have hqRing : Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk (stalkMaximalIdeal y ^ n))) =
      {IsLocalRing.closedPoint (Y.presheaf.stalk y)} := by
    rw [range_comap_of_surjective (R := Y.presheaf.stalk y)
        (S := Y.presheaf.stalk y ⧸ stalkMaximalIdeal y ^ n)
        (Ideal.Quotient.mk (stalkMaximalIdeal y ^ n)) Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, PrimeSpectrum.zeroLocus_pow _ (Nat.ne_of_gt hn),
      PrimeSpectrum.zeroLocus_eq_singleton]
    rfl
  have hp : PrimeSpectrum.comap (Ideal.Quotient.mk (stalkMaximalIdeal y ^ n)) p ∈
      Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (stalkMaximalIdeal y ^ n))) := ⟨p, rfl⟩
  rw [hqRing] at hp
  exact hp

/-- **The `n`-th infinitesimal base `Spec (𝒪_{Y,y}/𝔪_y ^ n) ⟶ Y` has range `{y}`, for
`n ≥ 1`.** The spectrum of `𝒪_{Y,y}/𝔪_y ^ n` has the closed point of `Spec 𝒪_{Y,y}` as its only
image point, because `𝔪_y ^ n` has the same zero locus as `𝔪_y`, and the canonical morphism
`Spec 𝒪_{Y,y} ⟶ Y` takes the closed point to `y`. -/
public theorem range_infinitesimalBase {Y : Scheme.{u}} (y : Y) {n : ℕ} (hn : 0 < n) :
    Set.range (infinitesimalBase y n).base = {y} := by
  have hne : stalkMaximalIdeal y ^ n ≠ ⊤ := by
    intro h
    have h1 : (⊤ : Ideal (Y.presheaf.stalk y)) ≤ stalkMaximalIdeal y := by
      rw [← h]
      exact Ideal.pow_le_self (Nat.ne_of_gt hn)
    exact (IsLocalRing.maximalIdeal.isMaximal (Y.presheaf.stalk y)).ne_top
      (le_antisymm le_top h1)
  have : Nontrivial (Y.presheaf.stalk y ⧸ stalkMaximalIdeal y ^ n) :=
    Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (Y.presheaf.stalk y ⧸ stalkMaximalIdeal y ^ n) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (stalkMaximalIdeal y ^ n))
      Ideal.Quotient.mk_surjective
  have hbase : ∀ p : Spec (stalkQuotient y n), (infinitesimalBase y n).base p = y := by
    intro p
    show (Y.fromSpecStalk y).base ((Spec.map (toStalkQuotient y n)).base p) = y
    rw [specMap_toStalkQuotient_eq_closedPoint y hn p]
    exact Y.fromSpecStalk_closedPoint
  refine Set.eq_singleton_iff_unique_mem.mpr
    ⟨⟨IsLocalRing.closedPoint (stalkQuotient y n), hbase _⟩, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact hbase p

/-- **The `n`-th infinitesimal neighbourhood has the fibre as the range of its projection to
`X`, for `n ≥ 1`.** -/
public theorem range_infinitesimalι {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) {n : ℕ} (hn : 0 < n) :
    Set.range (infinitesimalι f y n).base = Set.range (f.fiberι y).base := by
  rw [Scheme.Pullback.range_fst, range_infinitesimalBase y hn, Scheme.Hom.range_fiberι]

/-- **The transition morphism `X_n ⟶ X_m` is a homeomorphism on underlying spaces, for
`1 ≤ n ≤ m`.** Both projections to `X` are embeddings with the same range — the fibre — so the
transition is an embedding whose image is everything. -/
public theorem isHomeomorph_infinitesimalTransition {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    {n m : ℕ} (h : n ≤ m) (hn : 0 < n) (hm : 0 < m) :
    IsHomeomorph (infinitesimalTransition f y h).base := by
  have hcomp : ∀ x, (infinitesimalι f y m).base ((infinitesimalTransition f y h).base x) =
      (infinitesimalι f y n).base x := fun x =>
    congrArg (fun k : Scheme.Hom _ _ => k.base x) (infinitesimalTransition_ι f y h)
  have hcompFn : (infinitesimalι f y m).base ∘ (infinitesimalTransition f y h).base =
      (infinitesimalι f y n).base := funext hcomp
  have hembN : IsEmbedding (infinitesimalι f y n).base := (infinitesimalι f y n).isEmbedding
  have hembM : IsEmbedding (infinitesimalι f y m).base := (infinitesimalι f y m).isEmbedding
  refine isHomeomorph_iff_isEmbedding_surjective.mpr ⟨?_, fun z => ?_⟩
  · exact IsEmbedding.of_comp (infinitesimalTransition f y h).continuous
      (infinitesimalι f y m).continuous (hcompFn ▸ hembN)
  · have hrange : Set.range (infinitesimalι f y n).base =
        Set.range (infinitesimalι f y m).base :=
      (range_infinitesimalι f y hn).trans (range_infinitesimalι f y hm).symm
    obtain ⟨x, hx⟩ : (infinitesimalι f y m).base z ∈ Set.range (infinitesimalι f y n).base := by
      rw [hrange]; exact ⟨z, rfl⟩
    exact ⟨x, hembM.injective ((hcomp x).trans hx)⟩

/-! ### The tower of idempotents -/

/-- One step of the tower: an idempotent on `X_{n+1}` is lifted to an idempotent on `X_{n+2}`
restricting to it. -/
public def infinitesimalIdempotentStep {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (n : ℕ)
    (a : Γ(infinitesimalNeighbourhood f y (n + 1), ⊤)) (ha : IsIdempotentElem a) :
    Γ(infinitesimalNeighbourhood f y (n + 2), ⊤) :=
  (exists_isIdempotentElem_appTop_eq_of_isHomeomorph
    (infinitesimalTransition f y (Nat.le_succ (n + 1)))
    (isHomeomorph_infinitesimalTransition f y (Nat.le_succ (n + 1)) n.succ_pos
      (n + 1).succ_pos) a ha).choose

/-- The lifted element `infinitesimalIdempotentStep` is idempotent and restricts to the given
idempotent along the transition morphism `X_{n+1} ⟶ X_{n+2}`. -/
private theorem infinitesimalIdempotentStep_spec {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (n : ℕ)
    (a : Γ(infinitesimalNeighbourhood f y (n + 1), ⊤)) (ha : IsIdempotentElem a) :
    IsIdempotentElem (infinitesimalIdempotentStep f y n a ha) ∧
      (infinitesimalTransition f y (Nat.le_succ (n + 1))).appTop.hom
        (infinitesimalIdempotentStep f y n a ha) = a :=
  (exists_isIdempotentElem_appTop_eq_of_isHomeomorph
    (infinitesimalTransition f y (Nat.le_succ (n + 1)))
    (isHomeomorph_infinitesimalTransition f y (Nat.le_succ (n + 1)) n.succ_pos
      (n + 1).succ_pos) a ha).choose_spec

/-- The lifted element `infinitesimalIdempotentStep` is idempotent. -/
public theorem infinitesimalIdempotentStep_isIdempotentElem {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) (n : ℕ) (a : Γ(infinitesimalNeighbourhood f y (n + 1), ⊤))
    (ha : IsIdempotentElem a) : IsIdempotentElem (infinitesimalIdempotentStep f y n a ha) :=
  (infinitesimalIdempotentStep_spec f y n a ha).1

/-- The lifted element `infinitesimalIdempotentStep` restricts to the given idempotent along the
transition morphism `X_{n+1} ⟶ X_{n+2}`. -/
public theorem infinitesimalIdempotentStep_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (n : ℕ)
    (a : Γ(infinitesimalNeighbourhood f y (n + 1), ⊤)) (ha : IsIdempotentElem a) :
    (infinitesimalTransition f y (Nat.le_succ (n + 1))).appTop.hom
      (infinitesimalIdempotentStep f y n a ha) = a :=
  (infinitesimalIdempotentStep_spec f y n a ha).2

/-- **The tower of idempotents over an idempotent of the fibre.** The value at `n` is an
idempotent global function on the `(n+1)`-st infinitesimal neighbourhood `X_{n+1}` of the fibre,
and these are compatible with the transition morphisms. The value at `0` is the given idempotent
of `Γ(X_y, 𝒪)` read on `X_1 ≅ X_y`. -/
public def infinitesimalIdempotent {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (e : Γ(f.fiber y, ⊤))
    (he : IsIdempotentElem e) :
    (n : ℕ) → {a : Γ(infinitesimalNeighbourhood f y (n + 1), ⊤) // IsIdempotentElem a}
  | 0 => ⟨(fiberIsoInfinitesimalNeighbourhoodOne f y).inv.appTop.hom e, by
      change _ * _ = _
      rw [← map_mul]
      exact congrArg (fiberIsoInfinitesimalNeighbourhoodOne f y).inv.appTop.hom he⟩
  | n + 1 =>
      ⟨infinitesimalIdempotentStep f y n (infinitesimalIdempotent f y e he n).1
        (infinitesimalIdempotent f y e he n).2,
       infinitesimalIdempotentStep_isIdempotentElem f y n
         (infinitesimalIdempotent f y e he n).1 (infinitesimalIdempotent f y e he n).2⟩

/-- Every term of the tower is idempotent. -/
public theorem infinitesimalIdempotent_isIdempotentElem {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (e : Γ(f.fiber y, ⊤)) (he : IsIdempotentElem e) (n : ℕ) :
    IsIdempotentElem (infinitesimalIdempotent f y e he n).1 :=
  (infinitesimalIdempotent f y e he n).2

/-- **The tower is compatible with the transition morphisms.** -/
public theorem infinitesimalIdempotent_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (e : Γ(f.fiber y, ⊤)) (he : IsIdempotentElem e) (n : ℕ) :
    (infinitesimalTransition f y (Nat.le_succ (n + 1))).appTop.hom
        (infinitesimalIdempotent f y e he (n + 1)).1 =
      (infinitesimalIdempotent f y e he n).1 :=
  infinitesimalIdempotentStep_appTop f y n (infinitesimalIdempotent f y e he n).1
    (infinitesimalIdempotent f y e he n).2

/-- **The tower starts at the given idempotent of the fibre.** -/
public theorem infinitesimalIdempotent_zero {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (e : Γ(f.fiber y, ⊤)) (he : IsIdempotentElem e) :
    (fiberIsoInfinitesimalNeighbourhoodOne f y).hom.appTop.hom
        (infinitesimalIdempotent f y e he 0).1 = e := by
  have hh : (fiberIsoInfinitesimalNeighbourhoodOne f y).inv.appTop ≫
      (fiberIsoInfinitesimalNeighbourhoodOne f y).hom.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  show ((fiberIsoInfinitesimalNeighbourhoodOne f y).inv.appTop ≫
    (fiberIsoInfinitesimalNeighbourhoodOne f y).hom.appTop).hom e = e
  rw [hh]
  rfl

end Stacks.FormalFunctions

end

end
