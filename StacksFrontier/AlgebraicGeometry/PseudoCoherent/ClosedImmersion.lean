module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Restriction

/-!
# Comparing two closed immersions of an affine scheme into affine spaces over the base

Let `f : X ⟶ S` be a morphism of affine schemes locally of finite type. Stacks 09VC says that
`m`-pseudo-coherence of the derived pushforward of an object of `D(𝒪_X)` along a closed immersion
`X ⟶ 𝔸ⁿ_S` over `S` does not depend on the closed immersion chosen. The proof of that lemma has
two halves. The first is purely geometric: any two such closed immersions `i : X ⟶ 𝔸ⁿ_S` and
`j : X ⟶ 𝔸ᵐ_S` are dominated by a single one, in the strong sense that there are closed
immersions `k : 𝔸ⁿ_S ⟶ 𝔸ⁿ⁺ᵐ_S` and `l : 𝔸ᵐ_S ⟶ 𝔸ⁿ⁺ᵐ_S` over `S` with `i ≫ k = j ≫ l`. That
half is proved here. The second half is the transport of `m`-pseudo-coherence along `k` and along
`l`, which is Stacks 09VA; see the implementation notes.

## Main results

* `AlgebraicGeometry.AffineSpace.isClosedImmersion_homOfVector`: a morphism into an affine space
  over an affine base given by a family of global sections is a closed immersion as soon as the
  corresponding polynomial evaluation map is surjective.
* `AlgebraicGeometry.AffineSpace.exists_isClosedImmersion_containing`: a closed immersion of an
  affine scheme into an affine space over an affine base, factoring a given morphism, whose
  coordinates contain a prescribed family of global sections.
* `AlgebraicGeometry.AffineSpace.exists_isClosedImmersion_sum`: **the comparison diagram of the
  Stacks 09VC proof.** Two closed immersions of an affine scheme into affine spaces over an affine
  base, both factoring the same morphism, are dominated over the base by closed immersions into
  the affine space on the sum of the two index types, compatibly.
* `AlgebraicGeometry.AffineSpace.exists_isClosedImmersion_sum_of_equiv` and
  `AlgebraicGeometry.AffineSpace.exists_isClosedImmersion_fin_add`: the same with the index type
  of the dominating affine space transported along an equivalence, the latter in the
  `ULift (Fin (n + m))` form in which Stacks 09VC is stated.
* `AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_of_forall`: the
  implication (2) ⇒ (1) of Stacks 09VC, which needs no pseudo-coherence theory at all — only
  that at least one closed immersion into an affine space over the base exists.

## Implementation notes

The coordinates of the dominating immersions are the ones the source writes down: `k` sends the
`ι`-coordinates to themselves and the `κ`-coordinate `b` to a chosen preimage under `i` of the
`b`-th coordinate of `j`, and symmetrically for `l`. Such preimages exist because a closed
immersion of affine schemes is surjective on global sections
(`AlgebraicGeometry.Scheme.Hom.app_surjective`). That `i ≫ k = j ≫ l` is then a computation on
coordinates, using that a morphism into an affine space over `S` is determined by its structure
morphism to `S` together with the images of the coordinates
(`AlgebraicGeometry.AffineSpace.hom_ext`).

That `k` is a closed immersion is checked on global sections. Rather than identifying
`Γ(𝔸(ι; S), ⊤)` with a polynomial ring, it is enough to precompose with the evaluation
homomorphism `MvPolynomial ι Γ(S, ⊤) ⟶ Γ(𝔸(ι; S), ⊤)` sending a polynomial to the corresponding
combination of coordinates over the image of `Γ(S, ⊤)`; that homomorphism is *bijective*, because
it is the global-sections map of `AlgebraicGeometry.AffineSpace.isoOfIsAffine` up to the
isomorphism `Γ(Spec R, ⊤) ≅ R`, and surjectivity of a composite gives surjectivity of its second
factor. The surjectivity statement needed for the dominating immersions is slightly more general:
the evaluating family need only *contain* the coordinates, which is
`AlgebraicGeometry.AffineSpace.surjective_eval₂Hom_of_coord_eq`, proved by renaming variables
along the inclusion of the index type.

What is still missing for Stacks 09VC itself is Stacks 09VA: for a closed immersion of ringed
spaces `i` with `i_*𝒪` pseudo-coherent, an object of the derived category is `m`-pseudo-coherent
if and only if its derived pushforward is. Given that lemma for `k` and for `l`, Stacks 09VC
follows from `exists_isClosedImmersion_fin_add` by transporting along `k` and back along `l`,
using that `i ≫ k = j ≫ l`. Stacks 09VA in turn rests on the theory of pseudo-coherent complexes
on a ringed space — two-out-of-three in a distinguished triangle (Stacks 08CD), finite-typeness of
the top cohomology sheaf (Stacks 08DN) and the comparison with module-level pseudo-coherence on an
affine scheme (Stacks 08E7, which uses Stacks 065H, already in the library) — of which this library
currently has only the definitions, in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/SheafLevel.lean`.

`AlgebraicGeometry.AffineSpace.over_hom_eq` bridges the two spellings `(AffineSpace.over ι S).hom`
and `𝔸(ι; S) ↘ S` of the structure morphism of an affine space. They are definitionally equal but
not syntactically so — the notation inserts `CategoryTheory.over` — so Mathlib's rewrite rules,
which are stated in the second spelling, do not fire on the first. The statements here use the
first spelling, which is the one Stacks 09VC, 09VD and 09VE are stated in.

## References

* [The Stacks Project, Lemma 36.61.2 (09VC)](https://stacks.math.columbia.edu/tag/09VC)
* [The Stacks Project, Lemma 36.60.9 (09VA)](https://stacks.math.columbia.edu/tag/09VA)
* [The Stacks Project, Definition 20.46.4 (08CB)](https://stacks.math.columbia.edu/tag/08CB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MvPolynomial TopologicalSpace

namespace AlgebraicGeometry

universe u

namespace AffineSpace

/-- The structure morphism of an affine space, written as the projection of the `CanonicallyOver`
instance, is the structure morphism written with the `↘` notation. The two are definitionally but
not syntactically equal, so this is the bridge that lets Mathlib's rewrite rules apply to the
former spelling. -/
public theorem over_hom_eq {ι : Type u} (S : Scheme.{u}) :
    (AffineSpace.over ι S).hom = AffineSpace ι S ↘ S :=
  rfl

/-- Evaluating a polynomial over `Γ(S, ⊤)` at the coordinates of `𝔸(ι; S)` is surjective onto
`Γ(𝔸(ι; S), ⊤)` when `S` is affine: it is the map on global sections of the isomorphism
`𝔸(ι; S) ≅ Spec Γ(S, ⊤)[ι]`, up to `Γ(Spec R, ⊤) ≅ R`. -/
public theorem surjective_eval₂Hom_coord {ι : Type u} (S : Scheme.{u}) [IsAffine S] :
    Function.Surjective
      (eval₂Hom ((AffineSpace.over ι S).hom.appTop).hom (AffineSpace.coord S)) := by
  have hbij : Function.Bijective ((AffineSpace.isoOfIsAffine ι S).hom.app ⊤) :=
    ConcreteCategory.bijective_of_isIso _
  rw [show ((AffineSpace.isoOfIsAffine ι S).hom.app ⊤) =
      (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom
        (eval₂Hom ((AffineSpace.over ι S).hom.appTop).hom (AffineSpace.coord S)) from
      AffineSpace.isoOfIsAffine_hom_appTop ..] at hbij
  exact (show Function.Surjective
      ((eval₂Hom ((AffineSpace.over ι S).hom.appTop).hom (AffineSpace.coord S)) ∘
        (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι Γ(S, ⊤)))).hom) from
    fun y => hbij.2 y).of_comp

/-- Evaluation of polynomials at a family `w` is surjective as soon as evaluation at a family `u`
is, when `w` reproduces `u` along some map `e`: a polynomial in `u` is the renaming along `e` of a
polynomial in the variables of `w`. -/
private theorem surjective_eval₂Hom_of_comp_eq {R A n ι : Type*} [CommSemiring R] [CommSemiring A]
    (g : R →+* A) (w : n → A) (u : ι → A) (e : ι → n) (he : ∀ a, w (e a) = u a)
    (h : Function.Surjective (eval₂Hom g u)) : Function.Surjective (eval₂Hom g w) := by
  intro y
  obtain ⟨p, hp⟩ := h y
  refine ⟨rename e p, ?_⟩
  rw [← hp]
  simp only [coe_eval₂Hom, eval₂_rename]
  exact congrArg (fun v => eval₂ g v p) (funext he)

/-- Evaluating a polynomial over `Γ(S, ⊤)` in variables indexed by `n` at a family `w` of global
sections of `𝔸(ι; S)` is surjective as soon as `w` reproduces the coordinates of `𝔸(ι; S)` along
some map `e : ι → n`: a polynomial in the coordinates is the renaming along `e` of a polynomial
in the variables it indexes. -/
public theorem surjective_eval₂Hom_of_coord_eq {ι n : Type u} (S : Scheme.{u}) [IsAffine S]
    (w : n → Γ(AffineSpace ι S, ⊤)) (e : ι → n)
    (he : ∀ a, w (e a) = AffineSpace.coord S a) :
    Function.Surjective (eval₂Hom ((AffineSpace.over ι S).hom.appTop).hom w) :=
  surjective_eval₂Hom_of_comp_eq _ w _ e he (surjective_eval₂Hom_coord (ι := ι) S)

/-- Precomposing the global sections map of a morphism `h : T ⟶ 𝔸(ι; S)` over `S` with the
evaluation map of `𝔸(ι; S)` is evaluation at the pulled back coordinates. -/
private theorem appTop_comp_eval₂Hom_coord {T S : Scheme.{u}} {ι : Type u}
    (h : T ⟶ AffineSpace ι S) (g : T ⟶ S) (hg : h ≫ (AffineSpace.over ι S).hom = g) :
    (h.appTop).hom.comp
      (eval₂Hom ((AffineSpace.over ι S).hom.appTop).hom (AffineSpace.coord S)) =
      eval₂Hom (g.appTop).hom fun a => h.appTop (AffineSpace.coord S a) := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
  · simp only [RingHom.comp_apply, eval₂Hom_C]
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hg]
  · simp only [RingHom.comp_apply, eval₂Hom_X']

/-- A morphism `T ⟶ 𝔸(ι; S)` over `S` given by a family `v` of global sections of an affine `T`
is a closed immersion whenever evaluation of polynomials at `v` is surjective onto `Γ(T, ⊤)`.

Being a closed immersion is checked on global sections; precomposing with the evaluation map of
`𝔸(ι; S)` turns the map on global sections into evaluation at `v`, and surjectivity of a
composite gives surjectivity of its second factor. -/
public theorem isClosedImmersion_homOfVector {T S : Scheme.{u}} [IsAffine T] [IsAffine S]
    {ι : Type u} (g : T ⟶ S) (v : ι → Γ(T, ⊤))
    (hv : Function.Surjective (eval₂Hom (g.appTop).hom v)) :
    IsClosedImmersion (AffineSpace.homOfVector g v) := by
  have key := appTop_comp_eval₂Hom_coord (AffineSpace.homOfVector g v) g
    (AffineSpace.homOfVector_over g v)
  simp only [AffineSpace.homOfVector_appTop_coord] at key
  exact IsClosedImmersion.of_surjective_of_isAffine _
    (Function.Surjective.of_comp (g := ⇑(eval₂Hom ((AffineSpace.over ι S).hom.appTop).hom
      (AffineSpace.coord S))) (by rw [← RingHom.coe_comp, key]; exact hv))

/-- **A presentation adapted to a prescribed family of functions.** A morphism of affine schemes
locally of finite type admits a closed immersion into an affine space over the target, factoring
it, whose coordinate family *contains* any prescribed family `w` of global sections of the source:
the index type is `ULift (Fin k) ⊕ ι` and the coordinates indexed by `ι` pull back to `w`.

This is the shape of presentation the proofs of Stacks 09VD and 09VE use — they need the
coordinates to include the functions cutting out the opens of the cover, and a family inverting
them. -/
public theorem exists_isClosedImmersion_containing {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) [LocallyOfFiniteType f] {ι : Type u} (w : ι → Γ(X, ⊤)) :
    ∃ (k : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin k) ⊕ ι) S),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin k) ⊕ ι) S).hom = f ∧
          ∀ a, i.appTop (AffineSpace.coord S (Sum.inr a)) = w a := by
  obtain ⟨k, i₀, hi₀, hover₀⟩ := exists_isClosedImmersion_affineSpace f
  have hi₀s : Function.Surjective i₀.appTop := i₀.app_surjective ⊤ (isAffineOpen_top _)
  have hbase : Function.Surjective
      (eval₂Hom (f.appTop).hom fun a => i₀.appTop (AffineSpace.coord S a)) := by
    rw [← appTop_comp_eval₂Hom_coord i₀ f hover₀]
    exact hi₀s.comp (surjective_eval₂Hom_coord S)
  exact ⟨k, AffineSpace.homOfVector f
      (Sum.elim (fun a => i₀.appTop (AffineSpace.coord S a)) w),
    isClosedImmersion_homOfVector _ _
      (surjective_eval₂Hom_of_comp_eq _ _ _ Sum.inl (fun _ => rfl) hbase),
    AffineSpace.homOfVector_over _ _, fun a => AffineSpace.homOfVector_appTop_coord _ _ _⟩

/-- Reindexing an affine space along an equivalence of index types is an isomorphism, the inverse
being reindexing along the inverse equivalence. -/
public instance isIso_reindex {ι κ : Type u} (S : Scheme.{u}) (e : ι ≃ κ) :
    IsIso (AffineSpace.reindex (e : ι → κ) S) := by
  refine ⟨AffineSpace.reindex (e.symm : κ → ι) S, AffineSpace.hom_ext (by simp) fun a => ?_,
    AffineSpace.hom_ext (by simp) fun a => ?_⟩
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord,
      AffineSpace.reindex_appTop_coord, Scheme.Hom.id_appTop, CommRingCat.id_apply,
      Equiv.apply_symm_apply]
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord,
      AffineSpace.reindex_appTop_coord, Scheme.Hom.id_appTop, CommRingCat.id_apply,
      Equiv.symm_apply_apply]

/-- **The comparison diagram in the proof of Stacks 09VC.** Let `X` and `S` be affine, and let
`i : X ⟶ 𝔸(ι; S)` and `j : X ⟶ 𝔸(κ; S)` be closed immersions over `S` factoring the same
morphism `f : X ⟶ S`. Then there are closed immersions `k : 𝔸(ι; S) ⟶ 𝔸(ι ⊕ κ; S)` and
`l : 𝔸(κ; S) ⟶ 𝔸(ι ⊕ κ; S)` over `S` with `i ≫ k = j ≫ l`.

This reduces the comparison of `i` and `j` to transporting `m`-pseudo-coherence along the single
closed immersion `k`, and back along the single closed immersion `l`. -/
public theorem exists_isClosedImmersion_sum {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    {ι κ : Type u} {f : X ⟶ S}
    (i : X ⟶ AffineSpace ι S) [IsClosedImmersion i]
    (hi : i ≫ (AffineSpace.over ι S).hom = f)
    (j : X ⟶ AffineSpace κ S) [IsClosedImmersion j]
    (hj : j ≫ (AffineSpace.over κ S).hom = f) :
    ∃ (k : AffineSpace ι S ⟶ AffineSpace (ι ⊕ κ) S)
      (l : AffineSpace κ S ⟶ AffineSpace (ι ⊕ κ) S),
      IsClosedImmersion k ∧ IsClosedImmersion l ∧
        k ≫ (AffineSpace.over (ι ⊕ κ) S).hom = (AffineSpace.over ι S).hom ∧
        l ≫ (AffineSpace.over (ι ⊕ κ) S).hom = (AffineSpace.over κ S).hom ∧
        i ≫ k = j ≫ l := by
  classical
  have hisurj : Function.Surjective i.appTop := i.app_surjective ⊤ (isAffineOpen_top _)
  have hjsurj : Function.Surjective j.appTop := j.app_surjective ⊤ (isAffineOpen_top _)
  choose F hF using fun b : κ => hisurj (j.appTop (AffineSpace.coord S b))
  choose G hG using fun a : ι => hjsurj (i.appTop (AffineSpace.coord S a))
  refine ⟨AffineSpace.homOfVector (AffineSpace.over ι S).hom (Sum.elim (AffineSpace.coord S) F),
    AffineSpace.homOfVector (AffineSpace.over κ S).hom (Sum.elim G (AffineSpace.coord S)),
    isClosedImmersion_homOfVector _ _
      (surjective_eval₂Hom_of_coord_eq S _ Sum.inl fun _ => rfl),
    isClosedImmersion_homOfVector _ _
      (surjective_eval₂Hom_of_coord_eq S _ Sum.inr fun _ => rfl),
    AffineSpace.homOfVector_over _ _, AffineSpace.homOfVector_over _ _, ?_⟩
  refine AffineSpace.hom_ext ?_ fun s => ?_
  · simp only [Category.assoc]
    rw [over_hom_eq, AffineSpace.homOfVector_over, AffineSpace.homOfVector_over]
    exact hi.trans hj.symm
  · rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      CommRingCat.comp_apply, AffineSpace.homOfVector_appTop_coord,
      AffineSpace.homOfVector_appTop_coord]
    cases s with
    | inl a => exact (hG a).symm
    | inr b => exact hF b

/-- The comparison diagram of Stacks 09VC with the index type of the dominating affine space
transported along an equivalence `ν ≃ ι ⊕ κ`, reindexing being an isomorphism of affine spaces. -/
public theorem exists_isClosedImmersion_sum_of_equiv {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    {ι κ ν : Type u} (e : ν ≃ ι ⊕ κ) {f : X ⟶ S}
    (i : X ⟶ AffineSpace ι S) [IsClosedImmersion i]
    (hi : i ≫ (AffineSpace.over ι S).hom = f)
    (j : X ⟶ AffineSpace κ S) [IsClosedImmersion j]
    (hj : j ≫ (AffineSpace.over κ S).hom = f) :
    ∃ (k : AffineSpace ι S ⟶ AffineSpace ν S) (l : AffineSpace κ S ⟶ AffineSpace ν S),
      IsClosedImmersion k ∧ IsClosedImmersion l ∧
        k ≫ (AffineSpace.over ν S).hom = (AffineSpace.over ι S).hom ∧
        l ≫ (AffineSpace.over ν S).hom = (AffineSpace.over κ S).hom ∧
        i ≫ k = j ≫ l := by
  obtain ⟨k, l, hk, hl, hko, hlo, hkl⟩ := exists_isClosedImmersion_sum i hi j hj
  have hk' : IsClosedImmersion k := hk
  have hl' : IsClosedImmersion l := hl
  refine ⟨k ≫ AffineSpace.reindex (e : ν → ι ⊕ κ) S,
    l ≫ AffineSpace.reindex (e : ν → ι ⊕ κ) S, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · rw [Category.assoc, over_hom_eq, AffineSpace.reindex_over, ← over_hom_eq, hko]
  · rw [Category.assoc, over_hom_eq, AffineSpace.reindex_over, ← over_hom_eq, hlo]
  · rw [← Category.assoc, ← Category.assoc, hkl]

/-- The comparison diagram of Stacks 09VC in the indexing the source uses: two closed immersions
of an affine scheme into `𝔸ⁿ_S` and `𝔸ᵐ_S` over an affine `S`, factoring the same morphism, are
dominated over `S` by closed immersions into `𝔸ⁿ⁺ᵐ_S`, compatibly. -/
public theorem exists_isClosedImmersion_fin_add {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    {n m : ℕ} {f : X ⟶ S}
    (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) S) [IsClosedImmersion i]
    (hi : i ≫ (AffineSpace.over (ULift.{u} (Fin n)) S).hom = f)
    (j : X ⟶ AffineSpace (ULift.{u} (Fin m)) S) [IsClosedImmersion j]
    (hj : j ≫ (AffineSpace.over (ULift.{u} (Fin m)) S).hom = f) :
    ∃ (k : AffineSpace (ULift.{u} (Fin n)) S ⟶ AffineSpace (ULift.{u} (Fin (n + m))) S)
      (l : AffineSpace (ULift.{u} (Fin m)) S ⟶ AffineSpace (ULift.{u} (Fin (n + m))) S),
      IsClosedImmersion k ∧ IsClosedImmersion l ∧
        k ≫ (AffineSpace.over (ULift.{u} (Fin (n + m))) S).hom =
          (AffineSpace.over (ULift.{u} (Fin n)) S).hom ∧
        l ≫ (AffineSpace.over (ULift.{u} (Fin (n + m))) S).hom =
          (AffineSpace.over (ULift.{u} (Fin m)) S).hom ∧
        i ≫ k = j ≫ l :=
  exists_isClosedImmersion_sum_of_equiv
    (Equiv.ulift.trans
      (finSumFinEquiv.symm.trans (Equiv.sumCongr Equiv.ulift.symm Equiv.ulift.symm)))
    i hi j hj

end AffineSpace

namespace Scheme.Modules

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 09VC, the implication (2) ⇒ (1).** If the derived pushforward of `E` is
`m`-pseudo-coherent for *every* closed immersion of `X` into an affine space over `S` factoring
`f`, then it is so for *some* such closed immersion — because at least one exists, by the remark
preceding Stacks 09UI.

The converse implication is the content of Stacks 09VC and is not proved here; see the
implementation notes of this file. -/
public theorem exists_isPseudoCoherentFromAfterPushforward_of_forall {X S : Scheme.{u}}
    [IsAffine X] [IsAffine S] (f : X ⟶ S) [LocallyOfFiniteType f]
    (E : DerivedCategory X.Modules) (m : ℤ)
    (h : ∀ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) S), IsClosedImmersion i →
      i ≫ (AffineSpace.over (ULift.{u} (Fin n)) S).hom = f →
        IsPseudoCoherentFromAfterPushforward i E m) :
    ∃ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) S),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin n)) S).hom = f ∧
          IsPseudoCoherentFromAfterPushforward i E m :=
  let ⟨n, i, hi, hover⟩ := exists_isClosedImmersion_affineSpace f
  ⟨n, i, hi, hover, h n i hi hover⟩

end Scheme.Modules

end AlgebraicGeometry

end
