module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.FlatFiniteTypeNeighborhood
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.LocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.FibrePointResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# The dimension of the non-flat locus in the fibres

Let `f : X ⟶ S` be a morphism of schemes locally of finite type, let `F` be a quasi-coherent
`𝒪_X`-module of finite type and let `n` be a natural number. The closed subset of the fibre
`X_s` of points where `F` is not flat over `S` has dimension less than `n` for every point `s`
of `S` if and only if `trdeg_{κ(f x)} κ(x) < n` for every point `x` of `X` at which `F` is not
flat over `S`; and this condition is preserved by an arbitrary base change.

The equivalence is proved fibre by fibre. A fibre of a morphism locally of finite type is
locally of finite type over the residue field of the base point, the dimension of a closed
subset of such a scheme is the supremum of the transcendence degrees of the residue fields at
the generic points of its irreducible components, and the dimension at any of its points is at
least the transcendence degree there. Stability under base change holds because the
transcendence degree of the residue field extension can only drop under base change, while
non-flatness at a point of the base-changed family forces non-flatness at its image.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_lt_iff_forall_toENat_trdeg_lt`: a closed subset of a
  scheme locally of finite type over a field has dimension less than `n` exactly when the
  residue field at each of its points has transcendence degree less than `n` over the field.
* `AlgebraicGeometry.topologicalKrullDim_not_isFlatOverAt_fiber_lt_iff`: **Stacks 0CWF**, the
  dimension criterion.
* `AlgebraicGeometry.topologicalKrullDim_not_isFlatOverAt_fiber_lt_iff_at`: the dimension
  criterion at a single point of the base.
* `AlgebraicGeometry.toENat_trdeg_lt_of_topologicalKrullDim_fiber_lt`: the transcendence degree
  of a residue field over the base is bounded by the dimension of the fibre.
* `AlgebraicGeometry.toENat_trdeg_eq_topologicalKrullDim_fiber`: at the generic point of a fibre
  it is that dimension.
* `AlgebraicGeometry.topologicalKrullDim_not_isFlatOverAt_fiber_lt_of_isPullback`:
  **Stacks 0CWF**, stability of the criterion under base change.

## Implementation notes

The non-flat locus in a fibre is the complement of the flat locus of
`AlgebraicGeometry.isOpen_isFlatOverAt_fiber_of_locallyOfFiniteType` (Stacks 05M9), a set of
points of the scheme-theoretic fibre `AlgebraicGeometry.Scheme.Hom.fiber`; its dimension is the
dimension of that set as a subspace. A closed subset is given the reduced induced structure
`AlgebraicGeometry.Scheme.IdealSheafData.subscheme` of its vanishing ideal sheaf, whose
underlying space is the subset itself, so the dimension theory of schemes locally of finite type
over a field applies to it.

Transcendence degree is cardinal-valued while dimensions take values in `WithBot ℕ∞`, so the two
are compared through `Cardinal.toENat`; for a natural number `n` this loses nothing, since an
infinite transcendence degree is not less than `n` on either side. The residue field of a fibre
carries two algebra structures over the residue field of the base point, one coming from the
structure morphism of the fibre to the spectrum of that field and one from the residue field map
of the morphism; the transcendence degrees they define agree, which is read off here from the
two dimension formulas for a fibre at a point.

Base-change stability is stated for the fibrewise dimension condition; by the dimension
criterion applied to both families it is equally the stability of the pointwise transcendence
degree condition.

## References

* [Stacks Project, Tag 0CWF](https://stacks.math.columbia.edu/tag/0CWF)
* [Stacks Project, Tag 05M9](https://stacks.math.columbia.edu/tag/05M9)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- An element of `WithBot ℕ∞` smaller than the successor of a natural number `m` is at most
`m`. -/
lemma le_natCast_of_lt_natCast_succ {a : WithBot ℕ∞} {m : ℕ}
    (h : a < ((m + 1 : ℕ) : WithBot ℕ∞)) : a ≤ (m : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe c =>
    induction c using ENat.recTopCoe with
    | top => simp at h
    | coe k =>
      have hk : k < m + 1 := by exact_mod_cast h
      have hk' : (k : ℕ∞) ≤ (m : ℕ∞) := by exact_mod_cast Nat.le_of_lt_succ hk
      exact_mod_cast hk'

/-- An element of `WithBot ℕ∞` smaller than `0` is `⊥`. -/
lemma eq_bot_of_lt_zero {a : WithBot ℕ∞} (h : a < 0) : a = ⊥ := by
  induction a using WithBot.recBotCoe with
  | bot => rfl
  | coe c => simp at h

/-- A supremum in `WithBot ℕ∞` of elements each smaller than a natural number `n` is smaller
than `n`. -/
private lemma iSup_lt_natCast {ι : Sort*} {f : ι → WithBot ℕ∞} {n : ℕ}
    (h : ∀ i, f i < (n : WithBot ℕ∞)) : (⨆ i, f i) < (n : WithBot ℕ∞) := by
  match n with
  | 0 =>
    have hb : (⨆ i, f i) = ⊥ :=
      le_antisymm (iSup_le fun i ↦ le_of_eq (eq_bot_of_lt_zero (by simpa using h i))) bot_le
    rw [hb]
    simp [bot_lt_iff_ne_bot]
  | (m + 1) =>
    refine lt_of_le_of_lt (iSup_le fun i ↦ le_natCast_of_lt_natCast_succ (h i)) ?_
    have hm : ((m : ℕ∞)) < ((m + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_self m
    exact_mod_cast WithBot.coe_lt_coe.mpr hm

/-- On a scheme locally of finite type over a field, the transcendence degree of the residue
field at a point is at most the dimension of the scheme. -/
theorem toENat_trdeg_le_topologicalKrullDim (k : Type u) [Field k] (Y : Scheme.{u})
    (q : Y ⟶ Spec (.of k)) [LocallyOfFiniteType q] (y : Y) :
    letI : Algebra k (Y.residueField y) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop ≫ Y.Γevaluation y).hom.toAlgebra
    (Cardinal.toENat (Algebra.trdeg k (Y.residueField y)) : WithBot ℕ∞) ≤
      topologicalKrullDim Y := by
  let : Algebra k (Y.residueField y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop ≫ Y.Γevaluation y).hom.toAlgebra
  have : IsLocalRing (Y.presheaf.stalk y) := Y.toLocallyRingedSpace.isLocalRing y
  calc _ ≤ topologicalKrullDimAt Y y :=
        (le_add_of_nonneg_right ringKrullDim_nonneg_of_nontrivial).trans_eq
          (topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k Y q y).symm
    _ ≤ topologicalKrullDim Y :=
        (topologicalKrullDimAt_isLeast Y y).2 ⟨Set.univ, Set.mem_univ _, isOpen_univ,
          (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph).symm⟩

/-- For a scheme locally of finite type over a field, a closed subset has dimension less than a
natural number `n` exactly when the residue field at each of its points has transcendence degree
less than `n` over the field. -/
theorem topologicalKrullDim_lt_iff_forall_toENat_trdeg_lt (k : Type u) [Field k]
    (Y : Scheme.{u}) (q : Y ⟶ Spec (.of k)) [LocallyOfFiniteType q] {Z : Set Y}
    (hZ : IsClosed Z) (n : ℕ) :
    topologicalKrullDim ↥Z < (n : WithBot ℕ∞) ↔
      ∀ y ∈ Z,
        letI : Algebra k (Y.residueField y) :=
          ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop ≫ Y.Γevaluation y).hom.toAlgebra
        (Cardinal.toENat (Algebra.trdeg k (Y.residueField y)) : WithBot ℕ∞) <
          (n : WithBot ℕ∞) := by
  let I : Y.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩
  let j : I.subscheme ⟶ Y := I.subschemeι
  have hdim : topologicalKrullDim ↥Z = topologicalKrullDim I.subscheme := rfl
  have key : ∀ z : I.subscheme,
      letI : Algebra k (Y.residueField (j z)) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop ≫ Y.Γevaluation (j z)).hom.toAlgebra
      letI : Algebra k (I.subscheme.residueField z) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (j ≫ q).appTop ≫ I.subscheme.Γevaluation z).hom.toAlgebra
      (Cardinal.toENat (Algebra.trdeg k (Y.residueField (j z))) : WithBot ℕ∞) =
        (Cardinal.toENat (Algebra.trdeg k (I.subscheme.residueField z)) : WithBot ℕ∞) :=
    fun z ↦ by rw [trdeg_residueField_of_surjectiveOnStalks k q j z]
  refine ⟨fun hlt y hy ↦ ?_, fun hpoint ↦ ?_⟩
  · calc _ = _ := key ⟨y, hy⟩
      _ ≤ topologicalKrullDim I.subscheme :=
          toENat_trdeg_le_topologicalKrullDim k I.subscheme (j ≫ q) ⟨y, hy⟩
      _ = topologicalKrullDim ↥Z := hdim.symm
      _ < (n : WithBot ℕ∞) := hlt
  · rw [hdim, topologicalKrullDim_eq_iSup_trdeg_residueField k I.subscheme (j ≫ q)]
    exact iSup_lt_natCast fun z ↦ (key z).symm.trans_lt (hpoint (j z.1) z.1.2)

/-- The residue field of a fibre at the point through `x` has the same transcendence degree over
the residue field of `f x`, computed through the structure morphism of the fibre, as the residue
field of `x` has through the residue field map of `f`. -/
private lemma toENat_trdeg_fiber_asFiber_eq {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) :
    letI : Algebra (S.residueField (f x)) ((f.fiber (f x)).residueField (f.asFiber x)) :=
      ((Scheme.ΓSpecIso (.of (S.residueField (f x)))).inv ≫
        (f.fiberToSpecResidueField (f x)).appTop ≫
        (f.fiber (f x)).Γevaluation (f.asFiber x)).hom.toAlgebra
    letI : Algebra (S.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    (Cardinal.toENat (Algebra.trdeg (S.residueField (f x))
        ((f.fiber (f x)).residueField (f.asFiber x))) : WithBot ℕ∞) =
      (Cardinal.toENat (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) :
        WithBot ℕ∞) := by
  let : Algebra (S.residueField (f x)) ((f.fiber (f x)).residueField (f.asFiber x)) :=
    ((Scheme.ΓSpecIso (.of (S.residueField (f x)))).inv ≫
      (f.fiberToSpecResidueField (f x)).appTop ≫
      (f.fiber (f x)).Γevaluation (f.asFiber x)).hom.toAlgebra
  let : Algebra (S.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  have : IsLocallyNoetherian (f.fiber (f x)) :=
    isLocallyNoetherian_fiber_of_locallyOfFiniteType f (f x)
  have h1 : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      (Cardinal.toENat (Algebra.trdeg (S.residueField (f x))
          ((f.fiber (f x)).residueField (f.asFiber x))) : WithBot ℕ∞) +
        ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
    topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk (S.residueField (f x)) (f.fiber (f x))
      (f.fiberToSpecResidueField (f x)) (f.asFiber x)
  have h2 : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) +
        (Cardinal.toENat (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) :
          WithBot ℕ∞) :=
    topologicalKrullDimAt_fiber_eq_ringKrullDim_stalk_add_trdeg f x
  exact add_right_cancel_of_ne_top_of_ne_bot
    (c := ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x))) ringKrullDim_ne_top
    (ringKrullDim_eq_bot_iff_subsingleton.not.mpr (not_subsingleton _))
    (h1.symm.trans (h2.trans (add_comm _ _)))

/-- The residue field of a point of a fibre has the same transcendence degree over the residue
field of the base point as the residue field of its image in the ambient scheme. -/
private lemma toENat_trdeg_fiber_eq {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (s : S) (y : f.fiber s) (x : X) (hx : f x = s) (hxy : f.fiberι s y = x) :
    letI : Algebra (S.residueField s) ((f.fiber s).residueField y) :=
      ((Scheme.ΓSpecIso (.of (S.residueField s))).inv ≫
        (f.fiberToSpecResidueField s).appTop ≫ (f.fiber s).Γevaluation y).hom.toAlgebra
    letI : Algebra (S.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    (Cardinal.toENat (Algebra.trdeg (S.residueField s)
        ((f.fiber s).residueField y)) : WithBot ℕ∞) =
      (Cardinal.toENat (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) :
        WithBot ℕ∞) := by
  subst hx
  have hy : y = f.asFiber x :=
    (f.fiberι (f x)).isEmbedding.injective (by rw [hxy, f.fiberι_asFiber])
  subst hy
  exact toENat_trdeg_fiber_asFiber_eq f x

/-- The transcendence degree of the residue field of a point over the residue field of its image
is less than any natural number bounding the dimension of the fibre through it from above. -/
theorem toENat_trdeg_lt_of_topologicalKrullDim_fiber_lt {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) (n : ℕ)
    (h : topologicalKrullDim (f.fiber (f x)) < (n : WithBot ℕ∞)) :
    letI : Algebra (S.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    (Cardinal.toENat (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) :
      WithBot ℕ∞) < (n : WithBot ℕ∞) :=
  ((toENat_trdeg_fiber_asFiber_eq f x).symm.trans_le
    (toENat_trdeg_le_topologicalKrullDim (S.residueField (f x)) (f.fiber (f x))
      (f.fiberToSpecResidueField (f x)) (f.asFiber x))).trans_lt h

/-- At a point which is generic in the fibre through it, the transcendence degree of the residue
field over the residue field of its image is the dimension of that fibre. -/
@[ega "IV 10.6.1" "more general"]
theorem toENat_trdeg_eq_topologicalKrullDim_fiber {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) (hx : IsGenericPoint (f.asFiber x) Set.univ) :
    letI : Algebra (S.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    (Cardinal.toENat (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) :
      WithBot ℕ∞) = topologicalKrullDim (f.fiber (f x)) := by
  rw [← toENat_trdeg_fiber_asFiber_eq f x, ← topologicalKrullDim_closure_singleton_eq_trdeg
    (S.residueField (f x)) (f.fiber (f x)) (f.fiberToSpecResidueField (f x)) (f.asFiber x),
    hx.def]
  exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph

/-- **Stacks Project, Tag 0CWF**, at one point of the base. Let `f : X ⟶ S` be locally of finite
type, let `F` be a quasi-coherent `𝒪_X`-module of finite type, let `n` be a natural number and
let `s` be a point of `S`. The closed subset of the fibre over `s` where `F` is not flat over `S`
has dimension less than `n` if and only if `trdeg_{κ(s)} κ(x) < n` at every point `x` over `s`
where `F` is not flat over `S`. -/
theorem topologicalKrullDim_not_isFlatOverAt_fiber_lt_iff_at {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (n : ℕ)
    (s : S) :
    topologicalKrullDim
        ↥{y : f.fiber s | ¬ IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s y)} <
          (n : WithBot ℕ∞) ↔
      ∀ x : X, f x = s → ¬ IsFlatOverAt f.toLRSHom.toShHom F x →
        letI : Algebra (S.residueField (f x)) (X.residueField x) :=
          (f.residueFieldMap x).hom.toAlgebra
        (Cardinal.toENat (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) :
          WithBot ℕ∞) < (n : WithBot ℕ∞) := by
  have hclosed :
      IsClosed {y : f.fiber s | ¬ IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s y)} :=
    (isOpen_isFlatOverAt_fiber_of_locallyOfFiniteType f F s).isClosed_compl
  rw [topologicalKrullDim_lt_iff_forall_toENat_trdeg_lt (S.residueField s) (f.fiber s)
    (f.fiberToSpecResidueField s) hclosed n]
  refine ⟨fun h x hx hnf ↦ ?_, fun h y hy ↦ ?_⟩
  · subst hx
    have hmem : ¬ IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι (f x) (f.asFiber x)) := by
      rwa [f.fiberι_asFiber]
    exact (toENat_trdeg_fiber_eq f (f x) (f.asFiber x) x rfl
      (f.fiberι_asFiber x)).symm.trans_lt (h (f.asFiber x) hmem)
  · exact (toENat_trdeg_fiber_eq f s y (f.fiberι s y) (f.apply_fiberι s y) rfl).trans_lt
      (h (f.fiberι s y) (f.apply_fiberι s y) hy)

/-- **Stacks Project, Tag 0CWF.** Let `f : X ⟶ S` be locally of finite type, let `F` be a
quasi-coherent `𝒪_X`-module of finite type and let `n` be a natural number. The closed subset of
each fibre where `F` is not flat over `S` has dimension less than `n` if and only if
`trdeg_{κ(f x)} κ(x) < n` at every point `x` where `F` is not flat over `S`. -/
@[stacks 0CWF "the dimension criterion"]
theorem topologicalKrullDim_not_isFlatOverAt_fiber_lt_iff {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (n : ℕ) :
    (∀ s : S, topologicalKrullDim
        ↥{y : f.fiber s | ¬ IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s y)} <
          (n : WithBot ℕ∞)) ↔
      ∀ x : X, ¬ IsFlatOverAt f.toLRSHom.toShHom F x →
        letI : Algebra (S.residueField (f x)) (X.residueField x) :=
          (f.residueFieldMap x).hom.toAlgebra
        (Cardinal.toENat (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) :
          WithBot ℕ∞) < (n : WithBot ℕ∞) :=
  ⟨fun h x hx ↦ (topologicalKrullDim_not_isFlatOverAt_fiber_lt_iff_at f F n (f x)).1
      (h (f x)) x rfl hx,
    fun h s ↦ (topologicalKrullDim_not_isFlatOverAt_fiber_lt_iff_at f F n s).2
      fun x _ hx ↦ h x hx⟩

/-- **Stacks Project, Tag 0CWF.** The dimension criterion is stable under base change: if the
non-flat locus has dimension less than `n` in every fibre of `f`, then the same holds for the
pullback of `F` along any base change of `f`. -/
@[stacks 0CWF "stability under base change"]
theorem topologicalKrullDim_not_isFlatOverAt_fiber_lt_of_isPullback {X S S' X' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'} (hsq : IsPullback g' f' f g)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (n : ℕ)
    (hF : ∀ s : S, topologicalKrullDim
        ↥{y : f.fiber s | ¬ IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s y)} <
          (n : WithBot ℕ∞)) (s' : S') :
    topologicalKrullDim
        ↥{y : f'.fiber s' | ¬ IsFlatOverAt f'.toLRSHom.toShHom
            ((Scheme.Modules.pullback g').obj F) (f'.fiberι s' y)} < (n : WithBot ℕ∞) := by
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback hsq inferInstance
  have : ((Scheme.Modules.pullback g').obj F).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent X'.toRingedSpace X.toRingedSpace
      g'.toLRSHom.toShHom F ‹F.IsQuasicoherent›
  have : ((Scheme.Modules.pullback g').obj F).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType g'.toLRSHom.toShHom F
  refine (topologicalKrullDim_not_isFlatOverAt_fiber_lt_iff f'
    ((Scheme.Modules.pullback g').obj F) n).2 (fun x' hx' ↦ ?_) s'
  have hnf : ¬ IsFlatOverAt f.toLRSHom.toShHom F (g' x') := fun hflat ↦
    hx' (@modulePullback_isFlatOverAt X S S' X' f g g' f' hsq F ‹F.IsQuasicoherent› x' hflat)
  exact lt_of_le_of_lt (WithBot.coe_le_coe.mpr (Cardinal.toENat.monotone'
      (trdeg_residueField_le_of_baseChange hsq x')))
    ((topologicalKrullDim_not_isFlatOverAt_fiber_lt_iff f F n).1 hF (g' x') hnf)

end AlgebraicGeometry

end
