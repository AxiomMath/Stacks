module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelSurjective
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.PicardRepresentable
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPowerSymmetricPower
public import StacksFrontier.AlgebraicGeometry.Divisors.Modification.InvertibleFiltration

/-!
# The Abel morphisms `γ_d : Hilb^d ⟶ P^d` (Stacks 0BA0 (4), (5), (6))

Let `P` represent the rigidified Picard functor of a proper smooth geometrically irreducible
curve `X` over a field `k` with a rational point `σ`, and let `H` represent `Hilb^d_{X/k}`. The
Abel morphism `γ_d : H ⟶ P` lands in the degree-`d` component `P^d`, so corestricts to a morphism
`γ_d : H ⟶ P^d` ([Stacks, Tag 0BA0] (4)); it is onto `P^d` for `d ≥ g` ((5)); and for `d = g` it is
birational ((6)): by the proof of [Stacks, Tag 0B9Z], `γ_g` is an open immersion on the nonempty
open `W ⊆ Hilb^g` of [Stacks, Tag 0B9X], and both `Hilb^g` and `P^g` are irreducible.

The claim of [Stacks, Tag 0B9X] (`hexists`, `huniq`) and [Stacks, Tag 0B9Y] (`h0B9Y`) enter (6) as
hypotheses, exactly as they enter `Stacks.RigidifiedPicard.exists_smooth_grp_iso_functor`.

## Main definitions

* `Stacks.RigidifiedPicard.abelMorphismDegree`: the Abel morphism `γ_d : Hilb^d ⟶ P^d`.

## Main results

* `Stacks.RigidifiedPicard.range_abelMorphismFull_subset_degreeLocus`: `γ_d` lands in `P^d`.
* `Stacks.RigidifiedPicard.range_abelMorphismFull_eq_degreeLocus`: `γ_d(Hilb^d) = P^d` for
  `d ≥ g`.
* `Stacks.RigidifiedPicard.isBirational_abelMorphismDegree`: `γ_g` is birational.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

universe u

namespace Stacks.RigidifiedPicard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f]
  [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f]
  (hdimX : topologicalKrullDim X ≤ 1)
  (hdim : ∀ s : Spec (.of k), topologicalKrullDim ↥(f.fiber s) ≤ 1)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _) (P : Grp (Over (Spec (.of k))))
  (e : yonedaGrp.obj P ≅ functor f σ hσ)

omit [GeometricallyIrreducible f] in
/-- The rigidified Abel class of a degree-`d` family has degree `d` on every fibre. -/
theorem relativeInvertibleDegreeHomAt_abelNormalized_zero {d : ℕ} {T : Over (Spec (.of k))}
    (Z : Stacks.Hilbert.HilbertFamily (Over.mk f) T d) (t : T.left) :
    relativeInvertibleDegreeHomAt (bcProj f T) (topologicalKrullDim_fiber_bcProj_le f hdim T) t
      (abelNormalized f σ hσ 0 Z) = d := by
  have h0 : Stacks.Picard.schemePullbackClass (pullback.fst f T.hom)
      (0 : Stacks.Picard.ofScheme X) = 0 := map_zero (Stacks.Picard.schemePullbackClassHom _)
  rw [abelNormalized, h0, sub_zero, normalize, map_sub,
    relativeInvertibleDegreeHomAt_bcProj f hdim T t, sub_zero]
  exact @Stacks.Hilbert.relativeInvertibleDegreeHomAt_abelClass _ (Over.mk f) _ d T Z
    (isProper_bcProj f T) (topologicalKrullDim_fiber_bcProj_le f hdim T) t

/-- **`γ_d` lands in `P^d`** ([Stacks, Tag 0BA0] (4)). -/
theorem range_abelMorphismFull_subset_degreeLocus {d : ℕ} {H : Over (Spec (.of k))}
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d) :
    Set.range (abelMorphismFull f σ hσ hH P e).left ⊆
      (degreeLocus f hdim σ hσ P e d : Set P.X.left) := by
  rw [range_subset_degreeLocus_iff]
  intro t
  have h := abelMorphismFull_spec f σ hσ hH P e (𝟙 H)
  rw [Category.id_comp] at h
  rw [h, classOfElt, smallEquiv_abelElementFull]
  exact relativeInvertibleDegreeHomAt_abelNormalized_zero f hdim σ hσ _ t

/-- **The Abel morphism `γ_d : Hilb^d_{X/k} ⟶ Pic^d_{X/k}`** of [Stacks, Tag 0BA0] (4): the
Abel morphism corestricted to the degree-`d` component. -/
def abelMorphismDegree {d : ℕ} {H : Over (Spec (.of k))}
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d) :
    H.left ⟶ (degreeLocus f hdim σ hσ P e d).toScheme :=
  IsOpenImmersion.lift (degreeLocus f hdim σ hσ P e d).ι (abelMorphismFull f σ hσ hH P e).left
    (by
      rw [Scheme.Opens.range_ι]
      exact range_abelMorphismFull_subset_degreeLocus f hdim σ hσ P e hH)

/-- Composing `γ_d : Hilb^d ⟶ P^d` with the inclusion `P^d ⊆ P` recovers the Abel morphism
`Hilb^d ⟶ P`. -/
@[reassoc (attr := simp)]
theorem abelMorphismDegree_ι {d : ℕ} {H : Over (Spec (.of k))}
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d) :
    abelMorphismDegree f hdim σ hσ P e hH ≫ (degreeLocus f hdim σ hσ P e d).ι =
      (abelMorphismFull f σ hσ hH P e).left :=
  IsOpenImmersion.lift_fac _ _ _

/-- The morphism `γ_d : Hilb^d ⟶ P^d` is a morphism over `Spec k`. -/
theorem abelMorphismDegree_over {d : ℕ} {H : Over (Spec (.of k))}
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d) :
    abelMorphismDegree f hdim σ hσ P e hH ≫ (degreeLocus f hdim σ hσ P e d).ι ≫ P.X.hom =
      H.hom := by
  rw [abelMorphismDegree_ι_assoc, Over.w]

include hdimX in
/-- **[Stacks, Tag 0BA0] (5), surjectivity**: for `d ≥ g` the image of `γ_d` is `P^d`. -/
theorem range_abelMorphismFull_eq_degreeLocus {d : ℕ} {H : Over (Spec (.of k))}
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d) (hd : genus f ≤ d) :
    Set.range (abelMorphismFull f σ hσ hH P e).left =
      (degreeLocus f hdim σ hσ P e d : Set P.X.left) :=
  (range_abelMorphismFull_subset_degreeLocus f hdim σ hσ P e hH).antisymm
    (degreeLocus_subset_range_abelMorphismFull f hdimX hdim σ hσ P e hH hd)

include hdimX in
/-- **[Stacks, Tag 0BA0] (5), surjectivity**: for `d ≥ g`, `γ_d : Hilb^d ⟶ P^d` is surjective. -/
theorem surjective_abelMorphismDegree {d : ℕ} {H : Over (Spec (.of k))}
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d) (hd : genus f ≤ d) :
    Surjective (abelMorphismDegree f hdim σ hσ P e hH) := by
  refine ⟨fun p => ?_⟩
  obtain ⟨h, hh⟩ := degreeLocus_subset_range_abelMorphismFull f hdimX hdim σ hσ P e hH hd p.2
  refine ⟨h, (degreeLocus f hdim σ hσ P e d).ι.isOpenEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, abelMorphismDegree_ι, hh]
  rfl

omit [Smooth f] in
/-- The scheme representing `Hilb^d` of a smooth proper geometrically irreducible curve over a
field is irreducible: it is the image of `X^d` under the finite locally free morphism of degree
`d!` to the symmetric power. -/
theorem irreducibleSpace_hilbert (H : ℕ → Over (Spec (.of k)))
    (hH : ∀ d, Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) (H d) d) (d : ℕ) :
    IrreducibleSpace (H d).left := by
  have : SmoothOfRelativeDimension 1 (Over.mk f).hom := ‹SmoothOfRelativeDimension 1 f›
  have : IsSeparated (Over.mk f).hom := (inferInstance : IsSeparated f)
  have : GeometricallyIrreducible (Over.mk f).hom := ‹GeometricallyIrreducible f›
  have : UniversallyOpen (Over.mk f).hom := (inferInstance : UniversallyOpen f)
  have := Stacks.Scheme.irreducibleSpace_fibrePower (Over.mk f) d
  have hs := Stacks.Chow.surjective_of_isFiniteLocallyFreeOfRank
    (Stacks.Hilbert.symmetricPowerMap hH d).left (Nat.factorial_pos d)
  exact hs.surj.irreducibleSpace (Stacks.Hilbert.symmetricPowerMap hH d).left.continuous

include hdimX in
/-- **The chart of [Stacks, Tag 0B9Z] is the Abel morphism on `W`.** Given the claim of
[Stacks, Tag 0B9X] and [Stacks, Tag 0B9Y], there is a nonempty open `W ⊆ Hilb^g` on which `γ_g`
is an open immersion. -/
theorem exists_nonempty_isOpenImmersion_abelMorphismFull (H : ℕ → Over (Spec (.of k)))
    (hH : ∀ d, Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) (H d) d)
    (hexists : ∀ (T : Over (Spec (.of k))) (c : Stacks.Picard.ofScheme (bc f T)),
      HasInvertibleDirectImage f T c →
        ∃ (Z : Stacks.Hilbert.HilbertFamily (Over.mk f) T (genus f))
          (n : Stacks.Picard.ofScheme T.left),
          abelClass f Z = c + Stacks.Picard.schemePullbackClass (bcProj f T) n)
    (huniq : ∀ (T : Over (Spec (.of k)))
      (Z Z' : Stacks.Hilbert.HilbertFamily (Over.mk f) T (genus f)),
      HasInvertibleDirectImage f T (abelClass f Z) →
        (∃ n : Stacks.Picard.ofScheme T.left,
          abelClass f Z' = abelClass f Z + Stacks.Picard.schemePullbackClass (bcProj f T) n) →
          Z = Z')
    (h0B9Y : ∀ (K : Type u) [Field K] [Algebra k K]
      (c : Stacks.Picard.ofScheme (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))),
      ∃ c₀ : Stacks.Picard.ofScheme X,
        Module.finrank K (cohomologyOverField K
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Stacks.Picard.picardRepresentative _ (c +
            Stacks.Picard.schemePullbackClass
              (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) c₀)).obj 0) = 1 ∧
        IsZero (cohomologyOverField K
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Stacks.Picard.picardRepresentative _ (c +
            Stacks.Picard.schemePullbackClass
              (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) c₀)).obj 1)) :
    ∃ W : (H (genus f)).left.Opens, Nonempty W ∧
      IsOpenImmersion (W.ι ≫ (abelMorphismFull f σ hσ (hH (genus f)) P e).left) := by
  obtain ⟨W, R, hR⟩ := exists_representableBy_cohomologySubfunctor_spec f σ hσ
    (perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward)
    baseChangeDerivedPushforward 0 (hH (genus f)) hexists huniq
  have hopen := (isOpenSubfunctor_cohomologySubfunctor f σ hσ
    (perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward)
    baseChangeDerivedPushforward 0).isOpenImmersion_presheaf_ι
  have hfield := exists_translate_mem_cohomologySubfunctor f hdimX σ hσ h0B9Y
  obtain ⟨j, hjo, hj⟩ := exists_isOpenImmersion_chart P e _ _ (Functor.representableByEquiv R) hopen
  have hjγ : j = chartι W ≫ abelMorphismFull f σ hσ (hH (genus f)) P e := by
    have hinj : ∀ x : Over.mk (W.ι ≫ (H (genus f)).hom) ⟶ P.X,
        (e.inv.app (op _)).hom ((e.hom.app (op _)).hom x) = x := fun x => by
      show ((e.hom ≫ e.inv).app (op _)).hom x = x
      rw [e.hom_inv_id]; rfl
    have h1 := congrArg (fun φ => φ.app (op (Over.mk (W.ι ≫ (H (genus f)).hom)))
      (𝟙 (Over.mk (W.ι ≫ (H (genus f)).hom)))) hj
    have h2 : (e.hom.app (op _)).hom j =
        (e.hom.app (op _)).hom (chartι W ≫ abelMorphismFull f σ hσ (hH (genus f)) P e) := by
      rw [← Category.id_comp j]
      refine h1.trans ?_
      show (R.homEquiv (𝟙 _)).1 = _
      refine ext_functor f σ hσ ?_
      rw [hR, abelMorphismFull_spec, smallEquiv_abelElementFull, Category.id_comp]
    rw [← hinj j, h2, hinj]
  refine ⟨W, ?_, ?_⟩
  · obtain ⟨r, a, -⟩ := exists_translate_mem_range P e _ _ (Functor.representableByEquiv R) j hj
      hfield (((e.inv.app (op (Over.mk (𝟙 (Spec (.of k)))))).hom 1).left
        (show PrimeSpectrum k from IsLocalRing.closedPoint k))
    exact ⟨a⟩
  · have : (chartι W ≫ abelMorphismFull f σ hσ (hH (genus f)) P e).left =
        W.ι ≫ (abelMorphismFull f σ hσ (hH (genus f)) P e).left := rfl
    rw [← this, ← hjγ]
    exact hjo

include hdimX in
/-- **[Stacks, Tag 0BA0] (6): `γ_g : Hilb^g_{X/k} ⟶ Pic^g_{X/k}` is birational**, given the claim
of [Stacks, Tag 0B9X] and [Stacks, Tag 0B9Y]. Both schemes are irreducible (`Hilb^g` as the
image of `X^g`, `P^g` as the image of `Hilb^g` under the surjection `γ_g`), and `γ_g` is an open
immersion on the nonempty open `W` of [Stacks, Tag 0B9X]. -/
theorem isBirational_abelMorphismDegree (H : ℕ → Over (Spec (.of k)))
    (hH : ∀ d, Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) (H d) d)
    (hexists : ∀ (T : Over (Spec (.of k))) (c : Stacks.Picard.ofScheme (bc f T)),
      HasInvertibleDirectImage f T c →
        ∃ (Z : Stacks.Hilbert.HilbertFamily (Over.mk f) T (genus f))
          (n : Stacks.Picard.ofScheme T.left),
          abelClass f Z = c + Stacks.Picard.schemePullbackClass (bcProj f T) n)
    (huniq : ∀ (T : Over (Spec (.of k)))
      (Z Z' : Stacks.Hilbert.HilbertFamily (Over.mk f) T (genus f)),
      HasInvertibleDirectImage f T (abelClass f Z) →
        (∃ n : Stacks.Picard.ofScheme T.left,
          abelClass f Z' = abelClass f Z + Stacks.Picard.schemePullbackClass (bcProj f T) n) →
          Z = Z')
    (h0B9Y : ∀ (K : Type u) [Field K] [Algebra k K]
      (c : Stacks.Picard.ofScheme (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))),
      ∃ c₀ : Stacks.Picard.ofScheme X,
        Module.finrank K (cohomologyOverField K
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Stacks.Picard.picardRepresentative _ (c +
            Stacks.Picard.schemePullbackClass
              (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) c₀)).obj 0) = 1 ∧
        IsZero (cohomologyOverField K
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Stacks.Picard.picardRepresentative _ (c +
            Stacks.Picard.schemePullbackClass
              (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) c₀)).obj 1)) :
    IsBirational (abelMorphismDegree f hdim σ hσ P e (hH (genus f))) := by
  obtain ⟨W, hW, hWo⟩ := exists_nonempty_isOpenImmersion_abelMorphismFull f hdimX σ hσ P e H hH
    hexists huniq h0B9Y
  set γ := abelMorphismDegree f hdim σ hσ P e (hH (genus f))
  have := irreducibleSpace_hilbert f H hH (genus f)
  have hsurj := surjective_abelMorphismDegree f hdimX hdim σ hσ P e (hH (genus f)) le_rfl
  have : IrreducibleSpace (degreeLocus f hdim σ hσ P e (genus f)).toScheme :=
    hsurj.surj.irreducibleSpace γ.continuous
  have hcomp : (W.ι ≫ γ) ≫ (degreeLocus f hdim σ hσ P e (genus f)).ι =
      W.ι ≫ (abelMorphismFull f σ hσ (hH (genus f)) P e).left := by
    rw [Category.assoc, abelMorphismDegree_ι]
  have : IsOpenImmersion ((W.ι ≫ γ) ≫ (degreeLocus f hdim σ hσ P e (genus f)).ι) := by
    rw [hcomp]; exact hWo
  have : IsOpenImmersion (W.ι ≫ γ) :=
    IsOpenImmersion.of_comp _ (degreeLocus f hdim σ hσ P e (genus f)).ι
  have : IrreducibleSpace W.toScheme :=
    have hpre : IsPreirreducible (W : Set (H (genus f)).left) :=
      (PreirreducibleSpace.isPreirreducible_univ (X := ((H (genus f)).left : Type u))).open_subset
        W.2 (Set.subset_univ _)
    let x := Classical.arbitrary (α := (W : Type u))
    isIrreducible_iff_irreducibleSpace.mp ⟨⟨x.1, x.2⟩, hpre⟩
  have : IsDominant W.ι := ⟨W.ι.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  exact Stacks.Divisors.isBirational_of_isOpenImmersion_factorization W.ι (W.ι ≫ γ) γ rfl

end Stacks.RigidifiedPicard

end
