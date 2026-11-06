module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.DenseRationalPoints
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.PowerMatrixTwoTransitive
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.GeneralLinearTwoPowerContraction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The orbit of a pair of rational points differing in every coordinate is Zariski dense

Let `K` be an algebraically closed field, let `m : ℕ` and let `x, y` be two `K`-rational points
of `(ℙ¹_K)^m` with `xᵢ ≠ yᵢ` for **every** `i`. Then the orbit of the pair `(x, y)` under the
diagonal action of `G = (GL_{2,K})^m` is Zariski dense in the whole square
`(ℙ¹_K)^m × (ℙ¹_K)^m`: the orbit reaches every pair of rational points with no coincidence, and
those pairs are dense.

That is the content of `AlgebraicGeometry.dense_setOf_exists_powerMatrixAut`, and it is **not**
the exercise cited in the proof of [Stacks, Tag 0AEM]. The exercise there is density in

`(ℙ¹_K)^m ×_{(ℙ¹_K)^I} (ℙ¹_K)^m` with `I = {i | xᵢ = yᵢ}`,

and the case 0AEM's contraction step actually meets has `I ≠ ∅` — for `C = {pt} × ℙ¹` the two
rational points of `C` share their first coordinate. No statement about a closed subset of the
*square* can express that: the hypothesis of
`AlgebraicGeometry.dense_setOf_exists_powerMatrixAut` becomes contradictory as soon as `xᵢ = yᵢ`
for one `i`, so the theorem is vacuous exactly in the case the step needs. See its own docstring
for the proof of that, and `AlgebraicGeometry.Space.isPullback_subsetKernelPair` for the shape
the exercise has to be restated in: the fibre product is again a power of the projective line,
indexed by `{i ∈ I | i ∉ J} ⊕ I`, so it inherits irreducibility and the density statement below
can be run on it directly.

Two inputs meet here, each proved separately:

* which points the orbit reaches, from
  `AlgebraicGeometry.exists_comp_powerMatrixAut_hom_eq_and_eq`: every pair of rational points with
  the same coincidence pattern as `(x, y)`;
* that those points are dense, from `AlgebraicGeometry.dense_setOf_rationalPoint_notMem`: the
  rational points of an irreducible scheme locally of finite type over an algebraically closed
  field which avoid a proper closed subset are dense.

## Main results

* `AlgebraicGeometry.property_overProd`: a property of morphisms of schemes stable under base
  change and composition holds of the structure morphism of a binary product in a slice category.
* `AlgebraicGeometry.irreducibleSpace_projectiveSpacePowerOver`: **`(ℙ¹_K)^m` is irreducible** over
  a separably closed field.
* `AlgebraicGeometry.isProper_projectiveSpacePowerOver_prod`: the product of two copies of
  `(ℙ¹_K)^m` is proper over `Spec K`.
* `AlgebraicGeometry.dense_setOf_exists_powerMatrixAut`: **the orbit of `(x, y)` is Zariski
  dense in the square**, for `x` and `y` differing in every coordinate; vacuous otherwise.

## Implementation notes

The rational points of the product `(ℙ¹_K)^m × (ℙ¹_K)^m` are read as morphisms out of
`Over.mk (𝟙 (Spec K))` in the slice category over `Spec K`, where the product is a product; a
rational point of the product is then the pair of its two components by
`CategoryTheory.Limits.prod.hom_ext`, with no statement about the points of the underlying scheme
of a fibre product.

## References

* [Stacks Project, Tag 020J](https://stacks.math.columbia.edu/tag/020J)
* [Stacks Project, Tag 0B2U](https://stacks.math.columbia.edu/tag/0B2U)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### A property of the structure morphism of a product in a slice category -/

/-- **A property of morphisms of schemes stable under base change and composition holds of the
structure morphism of a binary product in a slice category** as soon as it holds of the structure
morphisms of the two factors: one projection is the base change of the other factor's structure
morphism. -/
@[ega "I 3.5.1" "(ii) ⇒ (i), special case",
  ega "I 5.5.12" "(iv)",
  ega "II 5.4.2" "(iv), special case"]
theorem property_overProd (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] {S : Scheme.{u}} (X Y : Over S) [HasBinaryProduct X Y]
    (hX : P X.hom) (hY : P Y.hom) :
    P (X ⨯ Y).hom := by
  have hpb := Over.isPullback_of_binaryFan_isLimit _ (prodIsProd X Y)
  have hfst : P (prod.fst : X ⨯ Y ⟶ X).left := MorphismProperty.of_isPullback hpb.flip hY
  rw [show (X ⨯ Y).hom = (prod.fst : X ⨯ Y ⟶ X).left ≫ X.hom from (Over.w _).symm]
  exact P.comp_mem _ _ hfst hX

/-! ### Irreducibility and properness of a power of the projective line and of its square -/

section PowerIrreducible

variable (K : Type u) [Field K]

/-- **A finite power of the projective line over a separably closed field is irreducible.** The
empty power is `Spec K`, and a power with one more factor is a binary product of a power with
`ℙ¹_K`; over a separably closed field a product of irreducibles is irreducible. -/
theorem irreducibleSpace_projectiveSpacePowerOver [IsSepClosed K] (m : ℕ) :
    IrreducibleSpace ↥(projectiveSpacePowerOver K 1 m).left := by
  have hiso : ∀ {A B : Over (Spec (CommRingCat.of K))}, (A ≅ B) →
      IrreducibleSpace ↥A.left → IrreducibleSpace ↥B.left := fun e h =>
    ObjectProperty.prop_of_iso (P := fun W : Scheme.{u} => IrreducibleSpace ↥W)
      ((Over.forget (Spec (CommRingCat.of K))).mapIso e) h
  induction m with
  | zero =>
    have ht : IsTerminal (projectiveSpacePowerOver K 1 0) :=
      IsTerminal.ofUniqueHom (fun _ => Pi.lift fun i => Fin.elim0 i)
        (fun _ _ => Pi.hom_ext _ _ fun i => Fin.elim0 i)
    exact hiso (IsTerminal.uniqueUpToIso Over.mkIdTerminal ht)
      (inferInstance : IrreducibleSpace ↥(Spec (CommRingCat.of K)))
  | succ p ih =>
    have hline : IrreducibleSpace
        ↥((projectiveSpaceOverRing 1 (CommRingCat.of K)).asOver
          (Spec (CommRingCat.of K))).left :=
      (inferInstance : IrreducibleSpace ↥(projectiveSpaceOverRing 1 (CommRingCat.of K)))
    exact hiso (Space.piFinSuccIso ((projectiveSpaceOverRing 1 (CommRingCat.of K)).asOver
      (Spec (CommRingCat.of K))) p).symm (irreducibleSpace_prod_left K _ _)

/-- **The square of a finite power of the projective line is irreducible** over a separably closed
field. -/
theorem irreducibleSpace_projectiveSpacePowerOver_prod [IsSepClosed K] (m : ℕ) :
    IrreducibleSpace ↥(projectiveSpacePowerOver K 1 m ⨯ projectiveSpacePowerOver K 1 m).left :=
  have := irreducibleSpace_projectiveSpacePowerOver K m
  irreducibleSpace_prod_left K _ _

/-- **The square of a finite power of the projective line is proper over `Spec K`.** -/
theorem isProper_projectiveSpacePowerOver_prod (m : ℕ) :
    _root_.AlgebraicGeometry.IsProper
      (projectiveSpacePowerOver K 1 m ⨯ projectiveSpacePowerOver K 1 m).hom :=
  property_overProd (@_root_.AlgebraicGeometry.IsProper.{u}) _ _
    (Space.isProper_projectiveSpacePowerOver K m) (Space.isProper_projectiveSpacePowerOver K m)

end PowerIrreducible

/-! ### The orbit of a pair of rational points is dense -/

section Orbit

variable (K : Type u) [Field K] [IsAlgClosed K] (m : ℕ)

/-- **The orbit of a pair of rational points of `(ℙ¹_K)^m` differing in every coordinate, under
the diagonal action of `(GL_{2,K})^m`, is Zariski dense in `(ℙ¹_K)^m × (ℙ¹_K)^m`.**

**This statement applies only when `xᵢ ≠ yᵢ` for every `i`.** Take for `Z` the union of the
partial diagonals `{(p, q) | pᵢ = qᵢ}` over all `i`; then a rational point off `Z` has `pᵢ ≠ qᵢ`
for every `i`, which is the coincidence pattern of `(x, y)`, so `hpat` holds, and `Z` is a proper
closed subset of an irreducible space, so `hZ'` holds too.

Outside that case the hypotheses are **contradictory** and the statement says nothing. Suppose
`xᵢ = yᵢ` for some `i`. Then `hpat` forces every rational point `(p, q)` with `pᵢ ≠ qᵢ` to lie in
`Z`. That set of rational points is nonempty and lies in a nonempty open subset of an
irreducible Jacobson space, so it is dense; `Z` is closed; hence `Z` is everything, contradicting
`hZ'`. In particular there is no closed `Z` whose complement's rational points are those of a
prescribed pattern with a nonempty agreement set — the condition `pᵢ ≠ qᵢ` is open, not closed,
so a "partial anti-diagonal" is not a closed set.

The case `xᵢ = yᵢ` for some `i` is the one the contraction step of [Stacks, Tag 0AEM] meets, and
the density it needs is density inside `(ℙ¹_K)^m ×_{(ℙ¹_K)^I} (ℙ¹_K)^m` with
`I = {i | xᵢ = yᵢ}`, not inside the square. That fibre product is again a power of the
projective line (`AlgebraicGeometry.Space.isPullback_subsetKernelPair`), so the statement has to
be restated there; it cannot be obtained by instantiating this one.

The proof is the two halves meeting: every rational point off `Z` is in the orbit, by
`AlgebraicGeometry.exists_comp_powerMatrixAut_hom_eq_and_eq`, and the rational points off `Z` are
dense, by `AlgebraicGeometry.dense_setOf_rationalPoint_notMem` applied to the square of the power,
which is irreducible and proper over `Spec K`. -/
theorem dense_setOf_exists_powerMatrixAut
    (x y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ projectiveSpacePowerOver K 1 m)
    (hxy : x ≠ y)
    (Z : Set ↥(projectiveSpacePowerOver K 1 m ⨯ projectiveSpacePowerOver K 1 m).left)
    (hZ : IsClosed Z) (hZ' : ∃ v, v ∉ Z)
    (hpat : ∀ p q : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ projectiveSpacePowerOver K 1 m,
      (prod.lift p q).left (IsLocalRing.closedPoint K) ∉ Z →
      ∀ i : Fin m,
        (p ≫ Pi.π (fun _ : Fin m => (projectiveSpaceOverRing 1 (CommRingCat.of K)).asOver
              (Spec (CommRingCat.of K))) i =
            q ≫ Pi.π (fun _ : Fin m =>
              (projectiveSpaceOverRing 1 (CommRingCat.of K)).asOver (Spec (CommRingCat.of K))) i) ↔
          (x ≫ Pi.π (fun _ : Fin m => (projectiveSpaceOverRing 1 (CommRingCat.of K)).asOver
              (Spec (CommRingCat.of K))) i =
            y ≫ Pi.π (fun _ : Fin m =>
              (projectiveSpaceOverRing 1 (CommRingCat.of K)).asOver
                (Spec (CommRingCat.of K))) i)) :
    Dense {v : ↥(projectiveSpacePowerOver K 1 m ⨯ projectiveSpacePowerOver K 1 m).left |
      ∃ M : Fin m → Matrix.GeneralLinearGroup (Fin 2) K,
        (prod.lift (x ≫ (projectiveSpacePowerMatrixAut K 1 m M).asIso.hom)
            (y ≫ (projectiveSpacePowerMatrixAut K 1 m M).asIso.hom)).left
          (IsLocalRing.closedPoint K) = v} := by
  have hproper := isProper_projectiveSpacePowerOver_prod K m
  have hirr := irreducibleSpace_projectiveSpacePowerOver_prod K m
  have hft : LocallyOfFiniteType
      (projectiveSpacePowerOver K 1 m ⨯ projectiveSpacePowerOver K 1 m).hom :=
    have := hproper
    inferInstance
  refine Dense.mono ?_ (dense_setOf_rationalPoint_notMem K
    (projectiveSpacePowerOver K 1 m ⨯ projectiveSpacePowerOver K 1 m).hom hZ hZ')
  have key : ∀ w : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
        projectiveSpacePowerOver K 1 m ⨯ projectiveSpacePowerOver K 1 m,
      w.left (IsLocalRing.closedPoint K) ∉ Z →
      ∃ M : Fin m → Matrix.GeneralLinearGroup (Fin 2) K,
        prod.lift (x ≫ (projectiveSpacePowerMatrixAut K 1 m M).asIso.hom)
          (y ≫ (projectiveSpacePowerMatrixAut K 1 m M).asIso.hom) = w := by
    intro w hwZ
    have hlift : prod.lift (w ≫ prod.fst) (w ≫ prod.snd) = w :=
      prod.hom_ext (prod.lift_fst _ _) (prod.lift_snd _ _)
    obtain ⟨M, hM₁, hM₂⟩ := exists_comp_powerMatrixAut_hom_eq_and_eq K 1 m x y
      (w ≫ prod.fst) (w ≫ prod.snd) hxy
      fun i => (hpat (w ≫ prod.fst) (w ≫ prod.snd) (by rw [hlift]; exact hwZ) i).symm
    exact ⟨M, by rw [hM₁, hM₂, hlift]⟩
  rintro v ⟨⟨r, hr, hrv⟩, hvZ⟩
  have hrz : r (IsLocalRing.closedPoint K) ∉ Z := by rw [hrv]; exact hvZ
  obtain ⟨M, hM⟩ := key (Over.homMk r hr) hrz
  exact ⟨M, by rw [hM]; exact hrv⟩

end Orbit

end AlgebraicGeometry

end
