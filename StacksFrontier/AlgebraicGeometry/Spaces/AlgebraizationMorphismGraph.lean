module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraizationMorphismRigidity
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.FormalFunctionsFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence

/-!
# Algebraization of morphisms of algebraic spaces: uniqueness and graphs

Let `V` be an affine object of the big fppf site of `S` with Noetherian ring of global sections
`A`, complete with respect to an ideal `I`, and let `X` be proper over `V`. For a morphism
`t : T ⟶ Q` and a system of morphisms `gₙ : X ×_V Spec (A / Iⁿ) ⟶ T` over `Q`, this file
proves that the algebraization is unique when `t` is separated, and constructs the graphs of the
`gₙ` as closed immersions into `X ×_Q T`, the input of the existence proof.

## Main results

* `AlgebraicGeometry.Space.eq_of_forall_fibreInclusion_comp_eq`: two morphisms `X ⟶ T` over `Q`
  agreeing on every infinitesimal fibre are equal (uniqueness in Stacks 0A4Z).
* `AlgebraicGeometry.Space.fibreGraph`, `AlgebraicGeometry.Space.isClosedImmersion_fibreGraph`:
  the graphs, closed immersions when `t` is separated.
* `AlgebraicGeometry.Space.range_fibreGraph_le_openSubspaceOfPoints`: every graph lies in an
  open subspace containing the points of the first one.

## References

* [Stacks Project, Tag 0A4Z](https://stacks.math.columbia.edu/tag/0A4Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

section Uniqueness

variable (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
  (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
  [IsAdicComplete I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
  {X : AlgebraicSpaces B S hS} (fX : X ⟶ schemeSpace V)

/-- **Uniqueness of the algebraization.** Two morphisms from `X`, proper over `V`, to an
algebraic space `T` separated over `Q`, which agree over `Q` and on every infinitesimal fibre
`X ×_V Spec (A / Iⁿ)`, are equal: their equalizer is a closed subspace of `X`, because `T ⟶ Q`
is separated, and it contains every infinitesimal fibre, so it is all of `X` by rigidity. -/
theorem eq_of_forall_fibreInclusion_comp_eq (hX : IsProper B S hS fX.hom)
    {Q T : AlgebraicSpaces B S hS} (t : T ⟶ Q) (ht : IsSeparated B S hS t.hom)
    (h h' : X ⟶ T) (hh : h ≫ t = h' ≫ t)
    (heq : ∀ n, fibreInclusion V I fX n ≫ h = fibreInclusion V I fX n ≫ h') : h = h' := by
  have hh' : h.hom ≫ t.hom = h'.hom ≫ t.hom := congrArg (fun k => k.hom) hh
  let L : X.1 ⟶ pullback t.hom t.hom := pullback.lift h.hom h'.hom hh'
  let E : ClosedSubspaces B S hS X.1 :=
    ⟨(Subfunctor.range (pullback.diagonal t.hom)).preimage L,
      isClosedSubspace_preimage B S hS L _
        (isAlgebraicSpace_pullback B S hS t.hom t.hom T.2 T.2 Q.2) X.2
        (isClosedSubspace_range_of_isClosedImmersion B S hS _ T.2 ht)⟩
  have hE : E.1 = ⊤ := by
    refine eq_top_of_forall_fibreThickening_le V I fX hX E fun n U x hx => ?_
    have hcomp : (fibreThickening V I fX n).1.ι ≫ h.hom ≫ pullback.diagonal t.hom =
        (fibreThickening V I fX n).1.ι ≫ L := by
      refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, L, pullback.lift_fst]
      · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, L, pullback.lift_snd]
        exact congrArg (fun k => k.hom) (heq n)
    refine ⟨h.hom.app U x, ?_⟩
    exact congrArg (fun k => k.app U ⟨x, hx⟩) hcomp
  refine ObjectProperty.hom_ext _ ?_
  ext U x
  obtain ⟨y, hy⟩ : x ∈ E.1.obj U := by
    rw [hE]
    trivial
  have h1 := congrArg ((pullback.fst t.hom t.hom).app U) hy
  have h2 := congrArg ((pullback.snd t.hom t.hom).app U) hy
  have e1 : (pullback.fst t.hom t.hom).app U (L.app U x) = h.hom.app U x :=
    congrArg (fun k => k.app U x) (pullback.lift_fst h.hom h'.hom hh')
  have e2 : (pullback.snd t.hom t.hom).app U (L.app U x) = h'.hom.app U x :=
    congrArg (fun k => k.app U x) (pullback.lift_snd h.hom h'.hom hh')
  have d1 : (pullback.fst t.hom t.hom).app U ((pullback.diagonal t.hom).app U y) = y :=
    congrArg (fun k => k.app U y) (pullback.diagonal_fst t.hom)
  have d2 : (pullback.snd t.hom t.hom).app U ((pullback.diagonal t.hom).app U y) = y :=
    congrArg (fun k => k.app U y) (pullback.diagonal_snd t.hom)
  change h.hom.app U x = h'.hom.app U x
  rw [← e1, ← e2, ← h1, ← h2, d1, d2]

end Uniqueness

section Graph

variable (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
  {X : AlgebraicSpaces B S hS} (fX : X ⟶ schemeSpace V)
  {Q T : AlgebraicSpaces B S hS} (q : X ⟶ Q) (t : T ⟶ Q)
  (g : ∀ n, fibreSpace V I fX n ⟶ T)

/-- The transition between infinitesimal fibres commutes with their inclusions, on underlying
morphisms. -/
private theorem hom_fibreTransition_comp_hom_fibreInclusion {m n : ℕ} (h : m ≤ n) :
    (fibreTransition V I fX h).hom ≫ (fibreInclusion V I fX n).hom =
      (fibreInclusion V I fX m).hom :=
  congrArg (fun k => k.hom) (fibreTransition_comp V I fX h)

/-- Morphisms into an infinitesimal fibre are equal if they agree after the inclusion. -/
private theorem fibreSpace_hom_ext {n : ℕ} {Y : AlgebraicSpaces B S hS}
    {a b : Y ⟶ fibreSpace V I fX n}
    (h : a.hom ≫ (fibreInclusion V I fX n).hom = b.hom ≫ (fibreInclusion V I fX n).hom) :
    a = b :=
  have : Mono (fibreInclusion V I fX n).hom := inferInstanceAs (Mono (Subfunctor.ι _))
  ObjectProperty.hom_ext _ ((cancel_mono (fibreInclusion V I fX n).hom).1 h)

/-- The transitions of the infinitesimal fibres compose. -/
theorem fibreTransition_trans {l m n : ℕ} (h₁ : l ≤ m) (h₂ : m ≤ n) :
    fibreTransition V I fX h₁ ≫ fibreTransition V I fX h₂ =
      fibreTransition V I fX (h₁.trans h₂) := by
  refine fibreSpace_hom_ext V I fX ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  rw [Category.assoc, hom_fibreTransition_comp_hom_fibreInclusion,
    hom_fibreTransition_comp_hom_fibreInclusion, hom_fibreTransition_comp_hom_fibreInclusion]

/-- A system compatible with the successive transitions is compatible with all transitions. -/
theorem fibreTransition_comp_eq_of_succ
    (hc : ∀ n, fibreTransition V I fX (Nat.le_succ n) ≫ g (n + 1) = g n) {m n : ℕ}
    (h : m ≤ n) : fibreTransition V I fX h ≫ g n = g m := by
  induction n, h using Nat.le_induction with
  | base =>
    have : fibreTransition V I fX (le_refl m) = 𝟙 _ :=
      fibreSpace_hom_ext V I fX
        (by
          rw [ObjectProperty.FullSubcategory.id_hom, Category.id_comp]
          exact hom_fibreTransition_comp_hom_fibreInclusion V I fX (le_refl m))
    rw [this, Category.id_comp]
  | succ n hmn ih =>
    rw [← fibreTransition_trans V I fX hmn (Nat.le_succ n), Category.assoc, hc, ih]

/-- Points of an infinitesimal fibre are sent by the transition and the inclusion to the image
under the inclusion of the smaller fibre. -/
private theorem pointsMap_fibreTransition_ι {m n : ℕ} (h : m ≤ n)
    (x : points B S hS (fibreThickening V I fX m).1.toFunctor) :
    pointsMap B S hS _ (fibreThickening V I fX n).1.ι
        (pointsMap B S hS _ (fibreTransition V I fX h).hom x) =
      pointsMap B S hS _ (fibreThickening V I fX m).1.ι x := by
  rw [← pointsMap_comp_apply]
  exact congrArg (fun k => pointsMap B S hS _ k x)
    (hom_fibreTransition_comp_hom_fibreInclusion V I fX h)

/-- **The infinitesimal fibres have the points of the first one.** Every point of
`X ×_V Spec (A / Iⁿ)` lies, in `|X|`, in the image of `X ×_V Spec (A / I)`: the closed
subschemes `Spec (A / Iⁿ)` and `Spec (A / I)` of `V` have the same points. -/
theorem range_pointsMap_fibreThickening_ι_subset (n : ℕ) :
    Set.range (pointsMap B S hS _ (fibreThickening V I fX n).1.ι) ⊆
      Set.range (pointsMap B S hS _ (fibreThickening V I fX 1).1.ι) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rintro _ ⟨x, rfl⟩
    exact ⟨_, pointsMap_fibreTransition_ι V I fX (Nat.zero_le 1) x⟩
  · have : ∀ m, Mono (adicCompletionQuotientObjHom B S hS V I m) := fun m =>
      (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
    rw [range_pointsMap_preimage_ι, range_pointsMap_preimage_ι]
    refine Set.preimage_mono ?_
    change Set.range (pointsMap B S hS
        (Subfunctor.range (yoneda.map (adicCompletionQuotientObjHom B S hS V I n))).toFunctor
        (Subfunctor.range (yoneda.map (adicCompletionQuotientObjHom B S hS V I n))).ι) ⊆
      Set.range (pointsMap B S hS
        (Subfunctor.range (yoneda.map (adicCompletionQuotientObjHom B S hS V I 1))).toFunctor
        (Subfunctor.range (yoneda.map (adicCompletionQuotientObjHom B S hS V I 1))).ι)
    rw [range_pointsMap_ι_range, range_pointsMap_ι_range, range_pointsMap_yoneda_eq_preimage,
      range_pointsMap_yoneda_eq_preimage]
    refine Set.preimage_mono ?_
    rw [range_eq_zeroLocus_ker_appTop _ (isAffineOpen_top _),
      range_eq_zeroLocus_ker_appTop _ (isAffineOpen_top _),
      ker_appTop_adicCompletionQuotientObjHom, ker_appTop_adicCompletionQuotientObjHom, pow_one,
      ← Scheme.zeroLocus_radical _ (I ^ n), Ideal.radical_pow I hn.ne', Scheme.zeroLocus_radical]

variable {V I fX q t g}

/-- **The graph of `gₙ`**, the morphism `Xₙ ⟶ X ×_Q T` with components the inclusion of the
infinitesimal fibre and `gₙ`. -/
def fibreGraph (hg : ∀ n, g n ≫ t = fibreInclusion V I fX n ≫ q) (n : ℕ) :
    (fibreSpace V I fX n).1 ⟶ pullback q.hom t.hom :=
  pullback.lift (fibreInclusion V I fX n).hom (g n).hom
    (congrArg (fun k => k.hom) (hg n)).symm

variable (hg : ∀ n, g n ≫ t = fibreInclusion V I fX n ≫ q)

/-- The first component of the graph `fibreGraph hg n` is the inclusion of the infinitesimal
fibre. -/
@[reassoc (attr := simp)]
theorem fibreGraph_fst (n : ℕ) :
    fibreGraph hg n ≫ pullback.fst q.hom t.hom = (fibreInclusion V I fX n).hom :=
  pullback.lift_fst _ _ _

/-- The second component of the graph `fibreGraph hg n` is `g n`. -/
@[reassoc (attr := simp)]
theorem fibreGraph_snd (n : ℕ) :
    fibreGraph hg n ≫ pullback.snd q.hom t.hom = (g n).hom :=
  pullback.lift_snd _ _ _

/-- The graphs are compatible with the transitions. -/
theorem fibreTransition_comp_fibreGraph
    (hc : ∀ n, fibreTransition V I fX (Nat.le_succ n) ≫ g (n + 1) = g n) {m n : ℕ}
    (h : m ≤ n) : (fibreTransition V I fX h).hom ≫ fibreGraph hg n = fibreGraph hg m := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, fibreGraph_fst, fibreGraph_fst,
      hom_fibreTransition_comp_hom_fibreInclusion]
  · rw [Category.assoc, fibreGraph_snd, fibreGraph_snd]
    exact congrArg (fun k => k.hom) (fibreTransition_comp_eq_of_succ V I fX g hc h)

/-- **The graph of a morphism to a separated target is a closed immersion.** Its composite with
the first projection, which is separated as a base change of `T ⟶ Q`, is the closed immersion
of the infinitesimal fibre. -/
theorem isClosedImmersion_fibreGraph (ht : IsSeparated B S hS t.hom) (n : ℕ) :
    IsClosedImmersion B S hS (fibreGraph hg n) := by
  refine isClosedImmersion_of_comp_of_isSeparated B S hS (fibreGraph hg n)
    (pullback.fst q.hom t.hom) ?_ (isSeparated_pullbackFst B S hS q.hom ht)
  rw [fibreGraph_fst]
  exact (fibreThickening V I fX n).2.2

/-- **Every graph lies in an open subspace containing the points of the first.** -/
theorem range_fibreGraph_le_openSubspaceOfPoints
    (hc : ∀ n, fibreTransition V I fX (Nat.le_succ n) ≫ g (n + 1) = g n)
    {O : Set (points B S hS (pullback q.hom t.hom))}
    (hO : Set.range (pointsMap B S hS _ (fibreGraph hg 1)) ⊆ O) (n : ℕ) :
    Subfunctor.range (fibreGraph hg n) ≤ openSubspaceOfPoints B S hS _ O := by
  rintro U _ ⟨x, rfl⟩
  rw [mem_openSubspaceOfPoints_iff]
  rintro _ ⟨P, rfl⟩
  rw [← yonedaEquiv_symm_naturality_right, pointsMap_comp_apply]
  set y := pointsMap B S hS _ (yonedaEquiv.symm x) P
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine hO ⟨pointsMap B S hS _ (fibreTransition V I fX (Nat.zero_le 1)).hom y, ?_⟩
    rw [← pointsMap_comp_apply, fibreTransition_comp_fibreGraph hg hc]
  · obtain ⟨y₁, hy₁⟩ := range_pointsMap_fibreThickening_ι_subset V I fX n ⟨y, rfl⟩
    have hy : pointsMap B S hS _ (fibreTransition V I fX hn).hom y₁ = y := by
      refine pointsMap_injective_of_mono B S hS (fibreThickening V I fX n).1.ι ?_
      rw [← hy₁]
      exact pointsMap_fibreTransition_ι V I fX hn y₁
    refine hO ⟨y₁, ?_⟩
    rw [← hy, ← pointsMap_comp_apply, fibreTransition_comp_fibreGraph hg hc]

end Graph

end AlgebraicGeometry.Space
