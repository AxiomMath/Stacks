module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFibreSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.VaryingBase.FiniteTypeAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraizationMorphismAdicFibre

/-!
# Algebraization of morphisms of algebraic spaces over a complete Noetherian ring

Let `A` be a Noetherian ring complete with respect to an ideal `I`, and let `X`, `Y` be algebraic
spaces over `Spec A`, with `X` proper and `Y` separated of finite type. A compatible system of
morphisms `g_n : X_n ⟶ Y_n` between the adic fibres over `Spec (A / I^{n+1})` is the system of
adic fibres of exactly one morphism `g : X ⟶ Y` over `Spec A`.

Uniqueness: two morphisms `φ, φ' : X ⟶ Y` with the same adic fibres agree on every `X_n`, so their
equalizer, a closed subspace of `X` because `Y` is separated, contains every adic fibre, hence is
all of `X` (`AlgebraicGeometry.Space.eq_top_of_forall_adicFibreSubspace_le`).

Existence is the source's argument: the graphs of the `g_n` are closed subspaces of the adic
fibres of `X ×_A Y` forming a tower, so the algebraization of closed subspaces, Stacks 08BG,
gives a closed subspace `Z ⊆ X ×_A Y` proper over `Spec A` cutting them out, and its projection
to `X` is an isomorphism.

## Main results

* `AlgebraicGeometry.Space.isClosedImmersion_pullbackLift`: the graph of a morphism out of a closed
  subspace into a separated space is a closed immersion.
* `AlgebraicGeometry.Space.range_adicGraph`: the graphs of a compatible system form a tower cut
  out by the adic fibres.
* `AlgebraicGeometry.Space.mono_ι_comp_fst_of_inf_eq_range_adicGraph`: the projection to `X` of a
  proper closed subspace cutting out the graphs is a monomorphism.
* `AlgebraicGeometry.Space.eq_of_forall_adicFibreMap_eq`: the uniqueness half.
* `AlgebraicGeometry.Space.exists_adicFibreMap_eq`: the existence half.
* `AlgebraicGeometry.Space.existsUnique_adicFibreMap_eq`: the statement of Stacks 0A4Z.

## Implementation notes

The projection `Z ⟶ X` is shown to be a closed immersion by showing it is a proper monomorphism
(Stacks 05W8), the diagonal of `Z ⟶ X` being a closed subspace of the proper space `Z ×_X Z` that
contains every adic fibre; the source instead shows it is finite through Zariski's main theorem
and identifies its direct image of `𝒪_Z` with `𝒪_X` by Stacks 08BE.

## References

* [Stacks Project, Tag 0A4Z](https://stacks.math.columbia.edu/tag/0A4Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (A : Type u) [CommRing A] (I : Ideal A) (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (.of A))) (hSn : ∀ n, B.Contains (adicThickening A I n))

/-- **The graph of a morphism out of a closed subspace is a closed immersion.** For a closed
immersion `c : P ⟶ X` and `h : P ⟶ Y` over a common base with `Y` separated, the morphism
`(c, h) : P ⟶ X ×_T Y` is a closed immersion: it is the section `(1, (c, h))` of the separated
projection `P ×_X (X ×_T Y) ⟶ P` followed by the base change of `c`. -/
theorem isClosedImmersion_pullbackLift {T P X Y : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    {fX : X ⟶ T} {fY : Y ⟶ T} (hsY : IsSeparated B _ hS fY) {c : P ⟶ X}
    (hc : IsClosedImmersion B _ hS c) (h : P ⟶ Y) (w : c ≫ fX = h ≫ fY) :
    IsClosedImmersion B _ hS (pullback.lift c h w) := by
  have sep₁ : IsSeparated B _ hS (pullback.fst fX fY) :=
    isSeparated_pullback_fst_of_snd B _ hS fY fX (isSeparated_pullback B _ hS fY fX hsY)
  have sep₂ : IsSeparated B _ hS (pullback.fst c (pullback.fst fX fY)) :=
    isSeparated_pullback_fst_of_snd B _ hS (pullback.fst fX fY) c
      (isSeparated_pullback B _ hS _ c sep₁)
  let s : P ⟶ pullback c (pullback.fst fX fY) :=
    pullback.lift (𝟙 P) (pullback.lift c h w) (by rw [Category.id_comp, pullback.lift_fst])
  have hs : IsClosedImmersion B _ hS s :=
    isClosedImmersion_of_isSeparated_of_section B _ hS _ sep₂ s (pullback.lift_fst _ _ _)
  have hsnd : IsClosedImmersion B _ hS (pullback.snd c (pullback.fst fX fY)) :=
    presheaf_of_isPullback B _ hS (IsPullback.of_hasPullback _ _) hc
  have he : pullback.lift c h w = s ≫ pullback.snd c (pullback.fst fX fY) :=
    (pullback.lift_snd _ _ _).symm
  rw [he]
  exact isClosedImmersion_comp B _ hS _ _ hs hsnd

/-- The `n`-th adic fibre subspace lies in the range of `f` when the projection `X_n ⟶ X` factors
through `f`. -/
private theorem adicFibreSubspace_le_range_of_comp_eq {X P : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤
    Type u} (hX : IsAlgebraicSpace B _ hS X) {fX : X ⟶ yoneda.obj (baseObject A B hS)}
    {f : P ⟶ X} (n : ℕ) (k : adicFibre A I B hS hSn fX n ⟶ P)
    (hk : k ≫ f = pullback.fst fX (yoneda.map (adicThickeningMap A I B hS hSn n))) :
    (adicFibreSubspace A I B hS hSn ⟨X, hX⟩ fX n).1 ≤ Subfunctor.range f := by
  show (Subfunctor.range (yoneda.map (adicThickeningMap A I B hS hSn n))).preimage fX ≤ _
  rw [← range_adicFibre_fst]
  rintro U _ ⟨x, rfl⟩
  exact ⟨k.app U x, by rw [← hk]; rfl⟩

/-- **Morphisms from a proper space to a separated space are determined by their adic fibres.**
Let `A` be Noetherian and `I`-adically complete, `X` proper and `Y` separated over `Spec A`. Two
morphisms `φ, φ' : X ⟶ Y` over `Spec A` with the same adic fibres are equal. -/
theorem eq_of_forall_adicFibreMap_eq [IsNoetherianRing A] [IsAdicComplete I A]
    {X Y : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B _ hS X) (hY : IsAlgebraicSpace B _ hS Y)
    {fX : X ⟶ yoneda.obj (baseObject A B hS)} {fY : Y ⟶ yoneda.obj (baseObject A B hS)}
    (hpX : IsProper B _ hS fX) (hsY : IsSeparated B _ hS fY)
    {φ φ' : X ⟶ Y} (hφ : φ ≫ fY = fX) (hφ' : φ' ≫ fY = fX)
    (h : ∀ n, adicFibreMap A I B hS hSn φ hφ n = adicFibreMap A I B hS hSn φ' hφ' n) :
    φ = φ' := by
  have hw : φ ≫ fY = φ' ≫ fY := hφ.trans hφ'.symm
  let l : X ⟶ pullback fY fY := pullback.lift φ φ' hw
  let e : pullback (pullback.diagonal fY) l ⟶ X := pullback.snd _ _
  have hbase : IsAlgebraicSpace B _ hS (yoneda.obj (baseObject A B hS)) :=
    isAlgebraicSpace_yoneda B _ hS _
  have hYY : IsAlgebraicSpace B _ hS (pullback fY fY) :=
    isAlgebraicSpace_pullback B _ hS fY fY hY hY hbase
  have hP : IsAlgebraicSpace B _ hS (pullback (pullback.diagonal fY) l) :=
    isAlgebraicSpace_pullback B _ hS _ _ hY hX hYY
  have he : IsClosedImmersion B _ hS e :=
    presheaf_of_isPullback B _ hS (IsPullback.of_hasPullback _ _) hsY
  let C : ClosedSubspaces B _ hS X :=
    ⟨Subfunctor.range e, isClosedSubspace_range_of_isClosedImmersion B _ hS e hP he⟩
  have hC : ∀ n, (adicFibreSubspace A I B hS hSn ⟨X, hX⟩ fX n).1 ≤ C.1 := by
    intro n
    set p := pullback.fst fX (yoneda.map (adicThickeningMap A I B hS hSn n))
    have hpφ : p ≫ φ = p ≫ φ' := by
      rw [← adicFibreMap_fst A I B hS hSn φ hφ n, ← adicFibreMap_fst A I B hS hSn φ' hφ' n, h n]
    have hfac : (p ≫ φ) ≫ pullback.diagonal fY = p ≫ l := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id, Category.assoc,
          pullback.lift_fst]
      · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, Category.assoc,
          pullback.lift_snd, hpφ]
    exact adicFibreSubspace_le_range_of_comp_eq A I B hS hSn hX n (pullback.lift (p ≫ φ) p hfac)
      (pullback.lift_snd _ _ _)
  have htop := eq_top_of_forall_adicFibreSubspace_le A I B hS hSn ⟨X, hX⟩
    (ObjectProperty.homMk fX) hpX C hC
  have hepi : Epi e := (Subfunctor.epi_iff_range_eq_top _).2 htop
  have hcond : pullback.fst (pullback.diagonal fY) l ≫ pullback.diagonal fY = e ≫ l :=
    pullback.condition
  have h₁ : e ≫ φ = pullback.fst (pullback.diagonal fY) l := by
    have := congrArg (· ≫ pullback.fst fY fY) hcond
    simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id] at this
    rw [this, pullback.lift_fst]
  have h₂ : e ≫ φ' = pullback.fst (pullback.diagonal fY) l := by
    have := congrArg (· ≫ pullback.snd fY fY) hcond
    simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id] at this
    rw [this, pullback.lift_snd]
  exact (cancel_epi e).1 (h₁.trans h₂.symm)

section Graph

variable {A I B hS hSn} {X Y : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
  {fX : X ⟶ yoneda.obj (baseObject A B hS)} {fY : Y ⟶ yoneda.obj (baseObject A B hS)}
  (g : ∀ n, adicFibre A I B hS hSn fX n ⟶ adicFibre A I B hS hSn fY n)
  (hg : ∀ n, g n ≫ pullback.snd fY (yoneda.map (adicThickeningMap A I B hS hSn n)) =
    pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n)))

/-- The graph `X_n ⟶ X ×_A Y` of the `n`-th morphism of a compatible system. -/
def adicGraph (n : ℕ) : adicFibre A I B hS hSn fX n ⟶ pullback fX fY :=
  pullback.lift (pullback.fst fX (yoneda.map (adicThickeningMap A I B hS hSn n)))
    (g n ≫ pullback.fst fY (yoneda.map (adicThickeningMap A I B hS hSn n))) (by
      rw [pullback.condition, Category.assoc, pullback.condition, reassoc_of% (hg n)])

/-- The graph of `g n` followed by the projection to `X` is the projection of `X_n` to `X`. -/
@[reassoc (attr := simp)]
theorem adicGraph_fst (n : ℕ) :
    adicGraph g hg n ≫ pullback.fst fX fY =
      pullback.fst fX (yoneda.map (adicThickeningMap A I B hS hSn n)) :=
  pullback.lift_fst _ _ _

/-- The graph of `g n` followed by the projection to `Y` is `g n` followed by the projection of
`Y_n` to `Y`. -/
@[reassoc (attr := simp)]
theorem adicGraph_snd (n : ℕ) :
    adicGraph g hg n ≫ pullback.snd fX fY =
      g n ≫ pullback.fst fY (yoneda.map (adicThickeningMap A I B hS hSn n)) :=
  pullback.lift_snd _ _ _

/-- For a system `g` compatible with the transition maps `X_n ⟶ X_{n+1}` and `Y_n ⟶ Y_{n+1}`,
the graph of `g (n + 1)` restricts along `X_n ⟶ X_{n+1}` to the graph of `g n`. -/
theorem adicFibreSucc_adicGraph
    (hgc : ∀ n, adicFibreSucc A I B hS hSn fX n ≫ g (n + 1) =
      g n ≫ adicFibreSucc A I B hS hSn fY n) (n : ℕ) :
    adicFibreSucc A I B hS hSn fX n ≫ adicGraph g hg (n + 1) = adicGraph g hg n := by
  apply pullback.hom_ext
  · rw [Category.assoc, adicGraph_fst, adicFibreSucc_fst, adicGraph_fst]
  · rw [Category.assoc, adicGraph_snd, reassoc_of% (hgc n), adicFibreSucc_fst, adicGraph_snd]

/-- **The graphs form a tower cut out by the adic fibres.** The graph of `g_n` is the part of
the graph of `g_{n+1}` lying over `Spec (A / I^{n+1})`. -/
theorem range_adicGraph
    (hgc : ∀ n, adicFibreSucc A I B hS hSn fX n ≫ g (n + 1) =
      g n ≫ adicFibreSucc A I B hS hSn fY n) (n : ℕ) :
    Subfunctor.range (adicGraph g hg n) = Subfunctor.range (adicGraph g hg (n + 1)) ⊓
      (Subfunctor.range (yoneda.map (adicThickeningMap A I B hS hSn n))).preimage
        (pullback.fst fX fY ≫ fX) := by
  have hcond : ∀ m, adicGraph g hg m ≫ pullback.fst fX fY ≫ fX =
      pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn m)) ≫
        yoneda.map (adicThickeningMap A I B hS hSn m) := fun m => by
    rw [adicGraph_fst_assoc, pullback.condition]
  apply le_antisymm
  · refine le_inf ?_ ?_
    · rintro U _ ⟨x, rfl⟩
      refine ⟨(adicFibreSucc A I B hS hSn fX n).app U x, ?_⟩
      rw [← adicFibreSucc_adicGraph g hg hgc n]
      rfl
    · rintro U _ ⟨x, rfl⟩
      refine ⟨(pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n))).app U x, ?_⟩
      exact (congrArg (fun k => k.app U x) (hcond n)).symm
  · rintro U w ⟨⟨x', rfl⟩, ⟨t, ht⟩⟩
    -- `x'` lies over `Spec (A / I^{n+1})`
    have ht' : (pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn (n + 1)))).app U x' =
        (yoneda.map (adicThickeningSuccMap A I B hS hSn n)).app U t := by
      have := mono_adicThickeningMap A I B hS hSn (n + 1)
      show _ = t ≫ adicThickeningSuccMap A I B hS hSn n
      refine (cancel_mono (adicThickeningMap A I B hS hSn (n + 1))).1 ?_
      rw [Category.assoc, adicThickeningSuccMap_adicThickeningMap]
      exact (congrArg (fun k => k.app U x') (hcond (n + 1))).symm.trans ht.symm
    obtain ⟨x, hx, -⟩ := Types.exists_of_isPullback
      ((isPullback_adicFibreSucc A I B hS hSn fX n).map ((evaluation _ _).obj U)) x' t ht'
    refine ⟨x, ?_⟩
    rw [← adicFibreSucc_adicGraph g hg hgc n]
    show (adicGraph g hg (n + 1)).app U ((adicFibreSucc A I B hS hSn fX n).app U x) = _
    rw [show (adicFibreSucc A I B hS hSn fX n).app U x = x' from hx]

/-- **A point of `Z` over `Spec (A / I^{n+1})` lies on the `n`-th graph**, when `Z` cuts out the
graphs on the adic fibres. -/
theorem exists_adicGraph_of_mem {Z : Subfunctor (pullback fX fY)}
    (hZ : ∀ n, Z ⊓ (Subfunctor.range (yoneda.map (adicThickeningMap A I B hS hSn n))).preimage
      (pullback.fst fX fY ≫ fX) = Subfunctor.range (adicGraph g hg n)) (n : ℕ)
    {U : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ} {z : (pullback fX fY).obj U} (hz : z ∈ Z.obj U)
    (hzn : (pullback.fst fX fY ≫ fX).app U z ∈
      Set.range ((yoneda.map (adicThickeningMap A I B hS hSn n)).app U)) :
    ∃ x, (adicGraph g hg n).app U x = z := by
  have h : z ∈ (Z ⊓ (Subfunctor.range (yoneda.map (adicThickeningMap A I B hS hSn n))).preimage
      (pullback.fst fX fY ≫ fX)).obj U := ⟨hz, hzn⟩
  rw [hZ n] at h
  exact h

/-- Two points of the `n`-th adic fibre of `X` with the same image in `X` are equal. -/
theorem adicFibre_ext (n : ℕ) {U : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ}
    {x₁ x₂ : (adicFibre A I B hS hSn fX n).obj U}
    (h : (pullback.fst fX (yoneda.map (adicThickeningMap A I B hS hSn n))).app U x₁ =
      (pullback.fst fX (yoneda.map (adicThickeningMap A I B hS hSn n))).app U x₂) : x₁ = x₂ := by
  have := mono_adicThickeningMap A I B hS hSn n
  have sq := (IsPullback.of_hasPullback fX (yoneda.map (adicThickeningMap A I B hS hSn n))).map
    ((evaluation _ _).obj U)
  refine Types.ext_of_isPullback sq h ?_
  show (pullback.snd fX _).app U x₁ = (pullback.snd fX _).app U x₂
  have hc : ∀ x, (pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n))).app U x ≫
      adicThickeningMap A I B hS hSn n =
      fX.app U ((pullback.fst fX (yoneda.map (adicThickeningMap A I B hS hSn n))).app U x) :=
    fun x => (congrArg (fun k => k.app U x) (pullback.condition (f := fX)
      (g := yoneda.map (adicThickeningMap A I B hS hSn n)))).symm
  refine (cancel_mono (adicThickeningMap A I B hS hSn n)).1 ?_
  rw [hc, hc, h]

/-- Two points of `Z` over the same point of `X` and over `Spec (A / I^{n+1})` agree, when `Z`
cuts out the graphs of the `g_n`: the points of `Z ×_X Z` over `Spec (A / I^{n+1})` lie on the
diagonal. -/
theorem preimage_le_range_diagonal (Z : Subfunctor (pullback fX fY))
    (hZ : ∀ n, Z ⊓ (Subfunctor.range (yoneda.map (adicThickeningMap A I B hS hSn n))).preimage
      (pullback.fst fX fY ≫ fX) = Subfunctor.range (adicGraph g hg n)) (n : ℕ) :
    (Subfunctor.range (yoneda.map (adicThickeningMap A I B hS hSn n))).preimage
        (pullback.fst (Z.ι ≫ pullback.fst fX fY) (Z.ι ≫ pullback.fst fX fY) ≫ Z.ι ≫
          pullback.fst fX fY ≫ fX) ≤
      Subfunctor.range (pullback.diagonal (Z.ι ≫ pullback.fst fX fY)) := by
  set p := Z.ι ≫ pullback.fst fX fY
  intro U y hy
  set z₁ := (pullback.fst p p).app U y
  set z₂ := (pullback.snd p p).app U y
  have hpz : p.app U z₁ = p.app U z₂ :=
    congrArg (fun k => k.app U y) (pullback.condition (f := p) (g := p))
  have h₁ : (pullback.fst fX fY ≫ fX).app U z₁.1 ∈
      Set.range ((yoneda.map (adicThickeningMap A I B hS hSn n)).app U) := hy
  have h₂ : (pullback.fst fX fY ≫ fX).app U z₂.1 ∈
      Set.range ((yoneda.map (adicThickeningMap A I B hS hSn n)).app U) := by
    show fX.app U (p.app U z₂) ∈ _
    rw [← hpz]
    exact hy
  obtain ⟨x₁, hx₁⟩ := exists_adicGraph_of_mem g hg hZ n z₁.2 h₁
  obtain ⟨x₂, hx₂⟩ := exists_adicGraph_of_mem g hg hZ n z₂.2 h₂
  have e : ∀ {x : (adicFibre A I B hS hSn fX n).obj U} {z : Z.toFunctor.obj U},
      (adicGraph g hg n).app U x = z.1 →
      (pullback.fst fX (yoneda.map (adicThickeningMap A I B hS hSn n))).app U x = p.app U z := by
    intro x z hxz
    rw [← adicGraph_fst g hg n]
    show (pullback.fst fX fY).app U ((adicGraph g hg n).app U x) = _
    rw [hxz]
    rfl
  have hx : x₁ = x₂ := adicFibre_ext n ((e hx₁).trans (hpz.trans (e hx₂).symm))
  have hz : z₁ = z₂ := Subtype.ext (hx₁.symm.trans (hx ▸ hx₂))
  refine ⟨z₁, ?_⟩
  refine Types.ext_of_isPullback ((IsPullback.of_hasPullback p p).map ((evaluation _ _).obj U))
    ?_ ?_
  · show (pullback.diagonal p ≫ pullback.fst p p).app U z₁ = z₁
    rw [pullback.diagonal_fst]
    rfl
  · show (pullback.diagonal p ≫ pullback.snd p p).app U z₁ = z₂
    rw [pullback.diagonal_snd]
    exact hz

/-- **The projection of `Z` to `X` is a monomorphism**, when `Z ⊆ X ×_A Y` is proper over `Spec A`
and cuts out the graphs of the `g_n` on the adic fibres: the diagonal of `Z ⟶ X` is a closed
subspace of the proper space `Z ×_X Z` containing every adic fibre
(`AlgebraicGeometry.Space.preimage_le_range_diagonal`), hence everything. -/
theorem mono_ι_comp_fst_of_inf_eq_range_adicGraph [IsNoetherianRing A] [IsAdicComplete I A]
    (hX : IsAlgebraicSpace B _ hS X) (hY : IsAlgebraicSpace B _ hS Y)
    (hpX : IsProper B _ hS fX) (Z : ClosedSubspaces B _ hS (pullback fX fY))
    (hZ : ∀ n, Z.1 ⊓ (Subfunctor.range (yoneda.map (adicThickeningMap A I B hS hSn n))).preimage
      (pullback.fst fX fY ≫ fX) = Subfunctor.range (adicGraph g hg n))
    (hZp : IsProper B _ hS (Z.1.ι ≫ pullback.fst fX fY ≫ fX)) :
    Mono (Z.1.ι ≫ pullback.fst fX fY) := by
  have hbase := isAlgebraicSpace_yoneda B _ hS (baseObject A B hS)
  have hZa : IsAlgebraicSpace B _ hS Z.1.toFunctor := Z.2.1
  have hpp : IsProper B _ hS (Z.1.ι ≫ pullback.fst fX fY) :=
    isProper_of_comp_of_isSeparated B _ hS hZa hX hbase _ fX
      (by rw [Category.assoc]; exact hZp) hpX.1
  have hP := isAlgebraicSpace_pullback B _ hS (Z.1.ι ≫ pullback.fst fX fY)
    (Z.1.ι ≫ pullback.fst fX fY) hZa hZa hX
  have hfP := isProper_comp' B _ hS _ _ hZa hbase
    (isProper_pullback_fst B _ hS hZa hX hZa (Z.1.ι ≫ pullback.fst fX fY)
      (Z.1.ι ≫ pullback.fst fX fY) hpp) hZp
  let E : ClosedSubspaces B _ hS _ := ⟨_,
    isClosedSubspace_range_of_isClosedImmersion B _ hS _ hZa hpp.1⟩
  have htop := eq_top_of_forall_adicFibreSubspace_le A I B hS hSn ⟨_, hP⟩
    (ObjectProperty.homMk _) hfP E (preimage_le_range_diagonal g hg Z.1 hZ)
  have hepi : Epi (pullback.diagonal (Z.1.ι ≫ pullback.fst fX fY)) :=
    (Subfunctor.epi_iff_range_eq_top _).2 htop
  have : IsIso (pullback.diagonal (Z.1.ι ≫ pullback.fst fX fY)) := isIso_of_mono_of_epi _
  exact (pullback.isIso_diagonal_iff (Z.1.ι ≫ pullback.fst fX fY)).1 inferInstance

include hg in
/-- **Stacks 0A4Z, existence.** Let `A` be Noetherian and `I`-adically complete, `X` proper and
`Y` separated of finite type over `Spec A`. A compatible system of morphisms `g_n : X_n ⟶ Y_n`
over the thickenings is the system of adic fibres of a morphism `X ⟶ Y` over `Spec A`.

The graphs of the `g_n` are closed subspaces `Γ_n` of `X ×_A Y` with `Γ_n = Γ_{n+1} ∩ (X ×_A Y)_n`,
so Stacks 08BG gives a closed subspace `Z ⊆ X ×_A Y`, proper over `Spec A`, cutting them out. Its
projection to `X` is proper and a monomorphism, hence a closed immersion (Stacks 05W8), and its
image contains every `X_n`, hence is `X`: the projection is an isomorphism, and the morphism is
its inverse followed by the projection to `Y`. -/
theorem exists_adicFibreMap_eq [IsNoetherianRing A] [IsAdicComplete I A]
    (hX : IsAlgebraicSpace B _ hS X) (hY : IsAlgebraicSpace B _ hS Y)
    (hpX : IsProper B _ hS fX) (hsY : IsSeparated B _ hS fY) (hfY : IsFiniteType B _ hS fY)
    (hgc : ∀ n, adicFibreSucc A I B hS hSn fX n ≫ g (n + 1) =
      g n ≫ adicFibreSucc A I B hS hSn fY n) :
    ∃ φ : X ⟶ Y, ∃ hφ : φ ≫ fY = fX, ∀ n, adicFibreMap A I B hS hSn φ hφ n = g n := by
  have hbase := isAlgebraicSpace_yoneda B _ hS (baseObject A B hS)
  have hW := isAlgebraicSpace_pullback B _ hS fX fY hX hY hbase
  have hsepfst : IsSeparated B _ hS (pullback.fst fX fY) :=
    isSeparated_pullback_fst_of_snd B _ hS fY fX (isSeparated_pullback B _ hS fY fX hsY)
  have hftfst : IsFiniteType B _ hS (pullback.fst fX fY) :=
    SpacesDescent.isFiniteType_of_isPullback_of_isFiniteType hW hX hY hbase
      (IsPullback.of_hasPullback fX fY).flip hfY
  let Wsp : AlgebraicSpaces B _ hS := ⟨pullback fX fY, hW⟩
  let fW : Wsp ⟶ schemeSpace (baseObject A B hS) := ObjectProperty.homMk (pullback.fst fX fY ≫ fX)
  have hft : IsFiniteType B _ hS fW.hom := isFiniteType_comp' B _ hS _ _ hX hbase hftfst hpX.2.1
  have hsep : IsSeparated B _ hS fW.hom := isSeparated_comp B _ hS _ _ hsepfst hpX.1
  -- the graphs
  have hι : ∀ n, IsClosedImmersion B _ hS (yoneda.map (adicThickeningMap A I B hS hSn n)) :=
    fun n => (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B _ hS _ _).2
      (isClosedImmersion_toScheme_map_adicThickeningMap A I B hS hSn n)
  have hγ : ∀ n, IsClosedImmersion B _ hS (adicGraph g hg n) := fun n =>
    isClosedImmersion_pullbackLift A B hS hsY
      (presheaf_of_isPullback B _ hS (IsPullback.of_hasPullback fX _).flip (hι n)) _ _
  let Γ : ℕ → ClosedSubspaces B _ hS (pullback fX fY) := fun n =>
    ⟨Subfunctor.range (adicGraph g hg n), isClosedSubspace_range_of_isClosedImmersion B _ hS _
      (isAlgebraicSpace_adicFibre A I B hS hSn hX fX n) (hγ n)⟩
  have hΓ : ∀ n, (Γ n).1 = (Γ (n + 1)).1 ⊓ (adicFibreSubspace A I B hS hSn Wsp fW.hom n).1 :=
    fun n => range_adicGraph g hg hgc n
  have hT0 := isAlgebraicSpace_yoneda B _ hS (adicThickeningObject A I B hS hSn 0)
  have hX0 := isAlgebraicSpace_adicFibre A I B hS hSn hX fX 0
  have hp0 : IsProper B _ hS ((Γ 0).1.ι ≫ fW.hom) := by
    have : Mono (adicGraph g hg 0) := mono_of_isClosedImmersion B _ hS _ (hγ 0)
    have hP0 := isAlgebraicSpace_pullback B _ hS (yoneda.map (adicThickeningMap A I B hS hSn 0))
      fX hT0 hX hbase
    have h1 : IsProper B _ hS (pullback.fst (yoneda.map (adicThickeningMap A I B hS hSn 0)) fX ≫
        yoneda.map (adicThickeningMap A I B hS hSn 0)) :=
      isProper_comp' B _ hS _ _ hT0 hbase (isProper_pullback_fst B _ hS hX hbase hT0 fX _ hpX)
        (isProper_of_isClosedImmersion B _ hS hT0 hbase _ (hι 0))
    have h2 : IsProper B _ hS ((pullbackSymmetry fX
        (yoneda.map (adicThickeningMap A I B hS hSn 0))).hom ≫
        pullback.fst (yoneda.map (adicThickeningMap A I B hS hSn 0)) fX ≫
          yoneda.map (adicThickeningMap A I B hS hSn 0)) :=
      isProper_comp' B _ hS _ _ hP0 hbase
        (isProper_of_isClosedImmersion B _ hS hX0 hP0 _ (isClosedImmersion_of_isIso B _ hS _)) h1
    have h3 := isProper_comp' B _ hS (asIso (Subfunctor.toRange (adicGraph g hg 0))).inv _ hX0 hbase
      (isProper_of_isClosedImmersion B _ hS
        (isAlgebraicSpace_of_iso B _ hS (asIso (Subfunctor.toRange (adicGraph g hg 0))) hX0)
        hX0 _ (isClosedImmersion_of_isIso B _ hS _)) h2
    rw [pullbackSymmetry_hom_comp_fst_assoc, ← pullback.condition, ← adicGraph_fst_assoc g hg 0,
      ← Category.assoc, inv_toRange_comp] at h3
    exact h3
  obtain ⟨Z, hZ, hZp⟩ :=
    exists_closedSubspace_inf_adicFibreSubspace_eq A I B hS hSn Wsp fW hft hsep Γ hΓ hp0
  have hZa : IsAlgebraicSpace B _ hS Z.1.toFunctor := Z.2.1
  set p := Z.1.ι ≫ pullback.fst fX fY
  have hpp : IsProper B _ hS p := isProper_of_comp_of_isSeparated B _ hS hZa hX hbase p fX
    (by rw [Category.assoc]; exact hZp) hpX.1
  have hmono : Mono p := mono_ι_comp_fst_of_inf_eq_range_adicGraph g hg hX hY hpX Z hZ hZp
  have htfae := (closedImmersion_conditions_tfae B _ hS hZa hX p).out 4 1
  have hpci : IsClosedImmersion B _ hS p := htfae.mp ⟨hpp.2.2, hpp.2.1.1, hmono⟩
  have hγZ : ∀ n, Subfunctor.range (adicGraph g hg n) ≤ Z.1 := fun n => by
    have h := hZ n
    change Z.1 ⊓ _ = Subfunctor.range (adicGraph g hg n) at h
    rw [← h]
    exact inf_le_left
  let δ : ∀ n, adicFibre A I B hS hSn fX n ⟶ Z.1.toFunctor := fun n =>
    Subfunctor.lift (adicGraph g hg n) (hγZ n)
  have hδ : ∀ n, δ n ≫ Z.1.ι = adicGraph g hg n := fun n => Subfunctor.lift_ι _ _
  have hδp : ∀ n, δ n ≫ p = pullback.fst fX (yoneda.map (adicThickeningMap A I B hS hSn n)) :=
    fun n => by rw [← Category.assoc, hδ, adicGraph_fst]
  let C : ClosedSubspaces B _ hS X :=
    ⟨Subfunctor.range p, isClosedSubspace_range_of_isClosedImmersion B _ hS p hZa hpci⟩
  have hC : ∀ n, (adicFibreSubspace A I B hS hSn ⟨X, hX⟩ fX n).1 ≤ C.1 :=
    fun n => adicFibreSubspace_le_range_of_comp_eq A I B hS hSn hX n (δ n) (hδp n)
  have htop := eq_top_of_forall_adicFibreSubspace_le A I B hS hSn ⟨X, hX⟩
    (ObjectProperty.homMk fX) hpX C hC
  have : Epi p := (Subfunctor.epi_iff_range_eq_top _).2 htop
  have : IsIso p := isIso_of_mono_of_epi p
  refine ⟨inv p ≫ Z.1.ι ≫ pullback.snd fX fY, ?_, fun n => ?_⟩
  · rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc Z.1.ι,
      IsIso.inv_hom_id_assoc]
  · have hfst : pullback.fst fX (yoneda.map (adicThickeningMap A I B hS hSn n)) ≫ inv p = δ n := by
      rw [← hδp n, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    apply pullback.hom_ext
    · rw [adicFibreMap_fst, reassoc_of% hfst, reassoc_of% (hδ n), adicGraph_snd]
    · rw [adicFibreMap_snd, hg n]

end Graph

/-- **Algebraization of morphisms of algebraic spaces (the statement of Stacks 0A4Z).** Let `A` be
a Noetherian ring complete with respect to an ideal `I`, `X` proper and `Y` separated of finite
type over `Spec A`. A compatible system of morphisms `g_n : X_n ⟶ Y_n` over the thickenings
`Spec (A / I^{n+1})` is the system of adic fibres of exactly one morphism `X ⟶ Y` over `Spec A`. -/
theorem existsUnique_adicFibreMap_eq [IsNoetherianRing A] [IsAdicComplete I A]
    {X Y : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B _ hS X) (hY : IsAlgebraicSpace B _ hS Y)
    (fX : X ⟶ yoneda.obj (baseObject A B hS)) (fY : Y ⟶ yoneda.obj (baseObject A B hS))
    (hpX : IsProper B _ hS fX) (hsY : IsSeparated B _ hS fY) (hfY : IsFiniteType B _ hS fY)
    (g : ∀ n, adicFibre A I B hS hSn fX n ⟶ adicFibre A I B hS hSn fY n)
    (hg : ∀ n, g n ≫ pullback.snd fY (yoneda.map (adicThickeningMap A I B hS hSn n)) =
      pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n)))
    (hgc : ∀ n, adicFibreSucc A I B hS hSn fX n ≫ g (n + 1) =
      g n ≫ adicFibreSucc A I B hS hSn fY n) :
    ∃! φ : X ⟶ Y, ∃ hφ : φ ≫ fY = fX, ∀ n, adicFibreMap A I B hS hSn φ hφ n = g n := by
  obtain ⟨φ, hφ, hφn⟩ := exists_adicFibreMap_eq g hg hX hY hpX hsY hfY hgc
  refine ⟨φ, ⟨hφ, hφn⟩, fun φ' ⟨hφ', hφ'n⟩ => ?_⟩
  exact eq_of_forall_adicFibreMap_eq A I B hS hSn hX hY hpX hsY hφ' hφ fun n =>
    (hφ'n n).trans (hφn n).symm

end AlgebraicGeometry.Space

end
