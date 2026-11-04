module

public import StacksFrontier.AlgebraicGeometry.AmpleCluster.ProjImmersion
public import StacksFrontier.AlgebraicGeometry.AmpleCluster.QuasiAffineAndImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorBaseRestriction

/-!
# The affine-open hypothesis of Stacks 0B9A

Proposition 0B9A of the Stacks project asks of a morphism `X ⟶ S` that any `d` points of a
fibre lie in an affine open of `X`. This file proves the facts about that hypothesis which the
proof of the proposition and its applications use.

* It passes to the restriction `X ×_S V ⟶ V` over an open `V ⊆ S`: the reduction to an affine
  base consumes it in this form.
* Its strengthening to `d + 1` points makes every degree-`d` family in an open of `X` closed in
  `X ×_S T`, which is the footnote to the source's proof.
* It holds for a projective morphism to an affine scheme, in particular for a projective scheme
  over a field (Stacks 0B9B, case (4), over an affine base): any finitely many points of such a
  scheme lie in an affine open.

## Main results

* `Stacks.Hilbert.exists_isAffineOpen_le_of_finite` — finitely many points of an open `W`
  contained in an affine open lie in an affine open contained in `W`.
* `Stacks.Hilbert.baseRestrict_affineFibres` — the hypothesis of 0B9A for `X ⟶ S` implies it for
  `X ×_S V ⟶ V`.
* `Stacks.Hilbert.exists_isAffineOpen_of_isProjectiveMorphism` — finitely many points of a
  scheme projective over an affine scheme lie in an affine open.
* `Stacks.Hilbert.isClosed_range_of_affineFibres_succ` — the footnote to the proof of 0B9A: if any
  `d + 1` points of a fibre lie in an affine open, a scheme finite locally free of rank `d` over
  `T` mapping to `X ×_S T` has closed image; hence `Stacks.Hilbert.ClosedInAmbient` holds.

## Implementation notes

Points of a fibre are a `Fin d`-indexed family with a common image in the base, the form in
which `Stacks.Hilbert.exists_isAffineOpen_supportedIn_of_specField` consumes the hypothesis.

The projective case uses graded prime avoidance on the integral model `Proj ℤ[T₀, …, Tₙ]`:
the images of the points lie in one affine `D₊(g)`
(`Stacks.AmpleCluster.exists_isAffineOpen_basicOpen_of_finite`), and its preimage in `X` is
affine, because `X ⟶ ℙⁿ_S ⟶ Proj ℤ[T₀, …, Tₙ]` is an affine morphism when `S` is affine.

## References

* [Stacks Project, Tag 0B9A](https://stacks.math.columbia.edu/tag/0B9A)
* [Stacks Project, Tag 0B9B](https://stacks.math.columbia.edu/tag/0B9B)
* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Hilbert

/-- Finitely many points of an open `W` of a scheme, contained in an affine open `U`, lie in an
affine open contained in `W`: an open subscheme of an affine scheme is quasi-affine. -/
theorem exists_isAffineOpen_le_of_finite {X : Scheme.{u}} {U W : X.Opens} (hU : IsAffineOpen U)
    (hWU : W ≤ U) {E : Set X} (hE : E.Finite) (hEW : E ⊆ W) :
    ∃ U' : X.Opens, IsAffineOpen U' ∧ E ⊆ U' ∧ U' ≤ W := by
  have : IsAffine U.toScheme := hU
  obtain ⟨U'', hU'', hEU''⟩ :=
    Stacks.AmpleCluster.exists_affineOpen_containing_finite_of_immersion_affine
      (X.homOfLE hWU) (E := Subtype.val ⁻¹' E) (hE.preimage Subtype.val_injective.injOn)
  refine ⟨W.ι ''ᵁ U'', hU''.image_of_isOpenImmersion _, fun x hx => ?_,
    Scheme.Opens.ι_image_le _ _⟩
  exact (Scheme.Opens.mem_ι_image_iff (x := ⟨x, hEW hx⟩)).mpr (hEU'' hx)

variable {S : Scheme.{u}}

/-- **The hypothesis of Stacks 0B9A passes to an open of the base.** If any `d` points of a fibre
of `X ⟶ S` lie in an affine open of `X`, then any `d` points of a fibre of `X ×_S V ⟶ V` lie in
an affine open of `X ×_S V`. -/
theorem baseRestrict_affineFibres (X : Over S) (d : ℕ)
    (hX : ∀ (s : S) (x : Fin d → X.left), (∀ i, X.hom (x i) = s) →
      ∃ U : X.left.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U)
    (V : S.Opens) (s : V.toScheme) (x : Fin d → (baseRestrict X V).left)
    (hx : ∀ i, (baseRestrict X V).hom (x i) = s) :
    ∃ U : (baseRestrict X V).left.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U := by
  let p : (baseRestrict X V).left ⟶ X.left := pullback.fst X.hom V.ι
  have hp : ∀ i, X.hom (p (x i)) = V.ι s := fun i => by
    rw [← hx i, ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    rfl
  obtain ⟨U, hU, hxU⟩ := hX _ (fun i => p (x i)) hp
  obtain ⟨U', hU', hEU', hU'W⟩ := exists_isAffineOpen_le_of_finite hU
    (inf_le_left : U ⊓ p.opensRange ≤ U) (Set.finite_range fun i => p (x i))
    (Set.range_subset_iff.mpr fun i => ⟨hxU i, ⟨x i, rfl⟩⟩)
  exact ⟨p ⁻¹ᵁ U', hU'.preimage_of_isOpenImmersion p (hU'W.trans inf_le_right),
    fun i => hEU' ⟨i, rfl⟩⟩

/-- **Finitely many points of a scheme projective over an affine scheme lie in an affine open.**
Let `f : X ⟶ S` be a projective morphism with `S` affine. The images of the points in the
integral model `Proj ℤ[T₀, …, Tₙ]` of projective space lie in one affine `D₊(g)` by graded prime
avoidance, and the preimage of `D₊(g)` in `X` is affine. -/
theorem exists_isAffineOpen_of_isProjectiveMorphism {X : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    (hf : IsProjectiveMorphism f) {E : Set X} (hE : E.Finite) :
    ∃ U : X.Opens, IsAffineOpen U ∧ E ⊆ U := by
  obtain ⟨n, i, hi, -⟩ := hf
  let : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
    MvPolynomial.gradedAlgebra
  let q : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
    i ≫ projectiveSpaceOver.toIntegralAtUniverse n S
  have : IsAffineHom q := by
    have := hi
    have : IsAffineHom (pullback.snd (terminal.from S)
        (terminal.from (projectiveSpaceAtUniverse.{u} n))) :=
      isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _)
        (inferInstance : IsAffineHom (terminal.from S))
    exact inferInstanceAs (IsAffineHom (i ≫ pullback.snd _ _))
  obtain ⟨g, hg, hEg⟩ := Stacks.AmpleCluster.exists_isAffineOpen_basicOpen_of_finite
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (hE.image q)
  exact ⟨q ⁻¹ᵁ Proj.basicOpen _ g, hg.preimage q, fun x hx => hEg ⟨x, hx, rfl⟩⟩

/-- **The hypothesis of Stacks 0B9A for a projective morphism to an affine scheme**, in
particular for a projective scheme over a field: any `d` points of `X` lie in an affine open. -/
theorem affineFibres_of_isProjectiveMorphism [IsAffine S] (X : Over S)
    (hX : IsProjectiveMorphism X.hom) (d : ℕ) (s : S) (x : Fin d → X.left)
    (_hx : ∀ i, X.hom (x i) = s) : ∃ U : X.left.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U := by
  obtain ⟨U, hU, hxU⟩ := exists_isAffineOpen_of_isProjectiveMorphism X.hom hX (Set.finite_range x)
  exact ⟨U, hU, fun i => hxU ⟨i, rfl⟩⟩

/-! ### The footnote to the proof of 0B9A: families in an open are closed -/

/-- The points of a scheme finite locally free of rank `d` over `T` lying over one point of `T`
are at most `d` in number. -/
theorem cardinalMk_fibre_le {Z T : Scheme.{u}} (q : Z ⟶ T) (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank q d] (t : T) :
    Cardinal.mk {z : Z // q z = t} ≤ d := by
  have key := cardinalMk_pullback_le_of_degree_le q d
    (fun k' _ g => ⟨d, le_rfl, Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
      (IsPullback.of_hasPullback g q).flip⟩) (T.residueField t) (T.fromSpecResidueField t)
  obtain ⟨y⟩ : Nonempty (Spec (T.residueField t) : Type u) :=
    inferInstanceAs (Nonempty (PrimeSpectrum (T.residueField t)))
  have hw : ∀ z : {z : Z // q z = t}, ∃ w : (pullback (T.fromSpecResidueField t) q : Scheme.{u}),
      pullback.snd (T.fromSpecResidueField t) q w = z.1 := fun z => by
    obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback y z.1
      ((Scheme.fromSpecResidueField_apply t y).trans z.2.symm)
    exact ⟨w, hw⟩
  choose w hw using hw
  refine (Cardinal.mk_le_of_injective (f := w) fun z z' h => Subtype.ext ?_).trans key
  rw [← hw z, ← hw z', h]

/-- If any `d + 1` points of a fibre of `X ⟶ S` lie in an affine open, then so do a point `y`
and a family of points over the same point indexed by a type embedding into `Fin d`. -/
private theorem exists_isAffineOpen_mem_of_affineFibres_succ (X : Over S) (d : ℕ)
    (hX : ∀ (s : S) (x : Fin (d + 1) → X.left), (∀ i, X.hom (x i) = s) →
      ∃ U : X.left.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U)
    {ι : Type*} (e : ι ↪ Fin d) (s : S) (y : X.left) (hy : X.hom y = s) (f : ι → X.left)
    (hf : ∀ i, X.hom (f i) = s) : ∃ W : X.left.Opens, IsAffineOpen W ∧ y ∈ W ∧ ∀ i, f i ∈ W := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · obtain ⟨W, hW, hmem⟩ := hX s (fun _ => y) (fun _ => hy)
    exact ⟨W, hW, hmem 0, fun i => (hι.false i).elim⟩
  · obtain ⟨W, hW, hmem⟩ := hX s (Fin.cons y fun j => f (Function.invFun e j))
      (Fin.cases hy fun j => hf (Function.invFun e j))
    refine ⟨W, hW, hmem 0, fun i => ?_⟩
    have h := hmem (e i).succ
    rwa [Fin.cons_succ, Function.leftInverse_invFun e.injective i] at h

/-- Let `c : Z ⟶ Y` restrict to a universally closed `Z₀ ⟶ N` over an open `N ⊆ Y`, where `Z₀`
is the whole preimage of `N`. Then a point of `N` in the closure of the image of `c` lies in it. -/
private theorem mem_range_of_mem_closure_of_universallyClosed_resLE {Z Y : Scheme.{u}} (c : Z ⟶ Y)
    (N : Y.Opens) (Z₀ : Z.Opens) (hZN : Z₀ ≤ c ⁻¹ᵁ N) (hNZ : c ⁻¹ᵁ N ≤ Z₀)
    [UniversallyClosed (c.resLE N Z₀ hZN)] {x : Y} (hxN : x ∈ N) (hx : x ∈ closure (Set.range c)) :
    x ∈ Set.range c := by
  set c₀ := c.resLE N Z₀ hZN
  have hc₀ : ∀ z, N.ι (c₀ z) = c z.1 := fun z => by
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι]
    rfl
  have hrange : N.ι ⁻¹' Set.range c = Set.range c₀ := by
    ext y
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨⟨z, hNZ (show c z ∈ N by rw [hz]; exact y.2)⟩,
        N.ι.isOpenEmbedding.injective ((hc₀ _).trans hz)⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z.1, (hc₀ z).symm⟩
  have hxN' : (⟨x, hxN⟩ : N) ∈ closure (N.ι ⁻¹' Set.range c) := by
    rw [← N.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage N.ι.continuous]
    exact hx
  rw [hrange, c₀.isClosedMap.isClosed_range.closure_eq] at hxN'
  obtain ⟨z, hz⟩ := hxN'
  exact ⟨z.1, (hc₀ z).symm.trans (congrArg N.ι hz)⟩

variable {S : Scheme.{u}} in
/-- **The footnote to the proof of Stacks 0B9A.** Suppose any `d + 1` points of a fibre of
`X ⟶ S` lie in an affine open of `X`. Then any morphism `c : Z ⟶ X ×_S T` such that `Z ⟶ T` is
finite locally free of rank `d` has closed image.

Let `x` be in the closure of the image and `t ∈ T` its image. The fibre `Z_t` has at most `d`
points, so there is an affine open `W ⊆ X` containing their images and the image of `x`. Over
the open `T₀ ⊆ T` of points whose fibre maps into `W`, which contains `t` because `Z ⟶ T` is
closed, the morphism `c` lands in the open `N` of `X ×_S T` over `W` and `T₀`, which is separated
over `T₀` because `W` is affine; so `Z_{T₀} ⟶ N` is universally closed, its image is closed in
`N`, and `x ∈ N` lies in it. -/
theorem isClosed_range_of_affineFibres_succ (X : Over S) (d : ℕ)
    (hX : ∀ (s : S) (x : Fin (d + 1) → X.left), (∀ i, X.hom (x i) = s) →
      ∃ U : X.left.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U)
    {T : Over S} {Z : Scheme.{u}} (c : Z ⟶ ((Over.pullback T.hom).obj X).left)
    [hq : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (c ≫ ((Over.pullback T.hom).obj X).hom) d] :
    IsClosed (Set.range c) := by
  set p := ((Over.pullback T.hom).obj X).hom
  set π := familyProjection X T
  set q := c ≫ p
  have : IsFinite q :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation q).mp
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree q d)).1
  have hπ : ∀ y, X.hom (π y) = T.hom (p y) := fun y => by
    rw [← Scheme.Hom.comp_apply, familyProjection_comp, Scheme.Hom.comp_apply]
  refine closure_subset_iff_isClosed.mp fun x hx => ?_
  -- an affine open of `X` containing the image of `x` and of the fibre of `Z` through it
  obtain ⟨e⟩ := (Cardinal.lift_mk_le'.{u, 0} (α := {z : Z // q z = p x})
    (β := Fin d)).mp (by simpa using cardinalMk_fibre_le q d (p x))
  obtain ⟨W, hW, hxW, hFW⟩ := exists_isAffineOpen_mem_of_affineFibres_succ X d hX e
    (T.hom (p x)) (π x) (hπ x) (fun z : {z : Z // q z = p x} => π (c z.1))
    fun z => (hπ _).trans (congrArg T.hom z.2)
  -- the open of `T` over which the fibres of `Z` map into `W`
  have hB : IsClosed (q '' {z | π (c z) ∉ W}) := by
    refine q.isClosedMap _ ?_
    have : IsOpen {z | π (c z) ∈ W} := W.2.preimage (c ≫ π).continuous
    simpa [Set.compl_setOf] using this.isClosed_compl
  let T₀ : T.left.Opens := ⟨_, hB.isOpen_compl⟩
  let N : ((Over.pullback T.hom).obj X).left.Opens := π ⁻¹ᵁ W ⊓ p ⁻¹ᵁ T₀
  have hZN : q ⁻¹ᵁ T₀ ≤ c ⁻¹ᵁ N := fun z hz =>
    ⟨by_contra fun h => hz ⟨z, h, rfl⟩, hz⟩
  have hxN : x ∈ N := ⟨hxW, fun ⟨z, hz, hzx⟩ => hz (hFW ⟨z, hzx⟩)⟩
  -- `N` is separated over `T₀`, because `W` is affine
  let jW := familyAmbientMap (restrictOverι X W) T
  have hNW : Set.range N.ι ⊆ Set.range jW := by
    rintro _ ⟨y, rfl⟩
    exact exists_familyAmbientMap_restrictOverι_eq _ y.2.1
  have : IsSeparated (W.ι ≫ X.hom) := by
    have : IsAffine W.toScheme := hW
    have : IsSeparated ((W.ι ≫ X.hom) ≫ terminal.from S) := IsSeparated.of_isAffineHom _
    exact IsSeparated.of_comp _ (terminal.from S)
  have : IsSeparated (N.ι ≫ p) := by
    rw [← IsOpenImmersion.lift_fac jW N.ι hNW, Category.assoc, familyAmbientMap_hom]
    exact inferInstanceAs (IsSeparated (_ ≫ pullback.snd (W.ι ≫ X.hom) T.hom))
  let p₀ := p.resLE T₀ N inf_le_right
  have : IsSeparated p₀ := by
    have : IsSeparated (p₀ ≫ T₀.ι) := by rw [Scheme.Hom.resLE_comp_ι]; infer_instance
    exact IsSeparated.of_comp _ T₀.ι
  -- so `Z_{T₀} ⟶ N` is universally closed
  have : UniversallyClosed (c.resLE N (q ⁻¹ᵁ T₀) hZN ≫ p₀) := by
    have := IsZariskiLocalAtTarget.restrict (P := @UniversallyClosed)
      (inferInstance : UniversallyClosed q) T₀
    rw [← Scheme.Hom.resLE_eq_morphismRestrict] at this
    rwa [Scheme.Hom.resLE_comp_resLE]
  have : UniversallyClosed (c.resLE N (q ⁻¹ᵁ T₀) hZN) := .of_comp_of_isSeparated _ p₀
  exact mem_range_of_mem_closure_of_universallyClosed_resLE c N _ hZN (fun _ hz => hz.2) hxN hx

variable {S : Scheme.{u}} in
/-- Under the hypothesis of the footnote to the proof of Stacks 0B9A — any `d + 1` points of a
fibre lie in an affine open — every degree-`d` family in an open `U ⊆ X` is closed in
`X ×_S T`. -/
theorem closedInAmbient_of_affineFibres_succ (X : Over S) (d : ℕ)
    (hX : ∀ (s : S) (x : Fin (d + 1) → X.left), (∀ i, X.hom (x i) = s) →
      ∃ U : X.left.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U)
    (U : X.left.Opens) : ClosedInAmbient X d U where
  isClosedImmersion {T} Z := by
    have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((Z.ideal.subschemeι ≫
        familyAmbientMap (restrictOverι X U) T) ≫ ((Over.pullback T.hom).obj X).hom) d := by
      rw [Category.assoc, familyAmbientMap_hom]
      exact Z.isFiniteLocallyFreeOfRank
    exact .of_isPreimmersion _ (isClosed_range_of_affineFibres_succ X d hX _)

variable {S : Scheme.{u}} in
/-- The hypothesis of the footnote to the proof of Stacks 0B9A for `d + 1` points implies the
hypothesis of the proposition for `d` points. -/
theorem affineFibres_of_affineFibres_succ (X : Over S) (d : ℕ)
    (hX : ∀ (s : S) (x : Fin (d + 1) → X.left), (∀ i, X.hom (x i) = s) →
      ∃ U : X.left.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U)
    (s : S) (x : Fin d → X.left) (hx : ∀ i, X.hom (x i) = s) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U := by
  rcases d with _ | d
  · exact ⟨⊥, isAffineOpen_bot _, Fin.elim0⟩
  · exact (exists_isAffineOpen_mem_of_affineFibres_succ X _ hX (.refl _) s (x 0) (hx 0) x hx).imp
      fun _ h => ⟨h.1, h.2.2⟩

end Stacks.Hilbert

end
