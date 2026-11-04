module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilChernPerfectPairing
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupTrace
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionGysinFlat
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.PushforwardOneBlowupSquare
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GaloisTraceDegree
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassWeilThree
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CoproductCorrespondences
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CanonicalDiagonalFlat

/-!
# `i_*1 = γ([Z])` for an open and closed immersion

Let data (D0), (D1), (D2') satisfy (A1)–(A7) (`Stacks.WeilCohomology.WeilChernData`), with the
data of Section 0FHA they define. Let `i : Z ⟶ X` be an open and closed immersion of nonempty
smooth projective schemes over `k`, equidimensional of the same dimension `d`, and let
`ι : W ⟶ X` be the inclusion of the complement. This is the case of codimension `0` of the
statement `i_*1 = γ([Z])` that Lemma 0FIR reduces Tag 0FIT to; the proof of Tag 0FIT (by a
blowing up in `Z`) does not apply to it, `Z` not being nowhere dense.

* The traces `λ` of (A6) are additive: `λ_X(a) = λ_Z(i^*a) + λ_W(ι^*a)`, by uniqueness of the
  trace (Remark 0FIK), since `μ = λ_Z ∘ i^* + λ_W ∘ ι^*` is normalised as in (A6) on `X`: by (A1)
  this may be checked after `i^*` and `ι^*`, where `(i × i)^*γ([Δ_X]) = γ([Δ_Z])` and
  `(i × ι)^*γ([Δ_X]) = 0`. If `W` is empty, `λ_X(a) = λ_Z(i^*a)`.
* Then `∫_X a ∪ γ([Z]) = ∫_Z i^*a`, as `i^*γ([Z]) = 1` and `ι^*γ([Z]) = 0`; this is
  `γ([Z]) = i_*1`.

## Main results

* `Stacks.WeilCohomology.WeilChernData.cycleClass_eq_pushforward_unitTw_of_isOpenImmersion`.

## References

* [Stacks Project, Tag 0FIT](https://stacks.math.columbia.edu/tag/0FIT)
* [Stacks Project, Tag 0FIR](https://stacks.math.columbia.edu/tag/0FIR)
* [Stacks Project, Tag 0FIK](https://stacks.math.columbia.edu/tag/0FIK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

namespace SmoothProjectiveScheme

/-- The product of two open immersions is an open immersion. -/
instance isOpenImmersion_prodMap {X' X Y' Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X' ⟶ X) (g : Y' ⟶ Y) [IsOpenImmersion f.hom.left] [IsOpenImmersion g.hom.left] :
    IsOpenImmersion (prodMap f g).hom.left :=
  Scheme.pullback_map_isOpenImmersion X'.obj.hom Y'.obj.hom X.obj.hom Y.obj.hom f.hom.left
    g.hom.left (𝟙 _) (by rw [Category.comp_id, Over.w f.hom])
    (by rw [Category.comp_id, Over.w g.hom])

/-- The first projection of `X × Y` composed with `f × g` is `f` composed with the first projection
of `X' × Y'`, on underlying schemes. -/
theorem prodMap_hom_left_fst {X' X Y' Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X' ⟶ X)
    (g : Y' ⟶ Y) :
    (prodMap f g).hom.left ≫ (fst X Y).hom.left =
      (fst X' Y').hom.left ≫ f.hom.left :=
  congrArg (fun φ ↦ φ.hom.left) (prodMap_fst f g)

/-- The second projection of `X × Y` composed with `f × g` is `g` composed with the second
projection of `X' × Y'`, on underlying schemes. -/
theorem prodMap_hom_left_snd {X' X Y' Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X' ⟶ X)
    (g : Y' ⟶ Y) :
    (prodMap f g).hom.left ≫ (snd X Y).hom.left =
      (snd X' Y').hom.left ≫ g.hom.left :=
  congrArg (fun φ ↦ φ.hom.left) (prodMap_snd f g)

/-- Two morphisms into the underlying scheme of `X × Y` with the same components are equal. -/
theorem prod_left_hom_ext {T : Scheme.{u}} {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    {a b : T ⟶ (prod X Y).obj.left} (h₁ : a ≫ (fst X Y).hom.left = b ≫ (fst X Y).hom.left)
    (h₂ : a ≫ (snd X Y).hom.left = b ≫ (snd X Y).hom.left) : a = b :=
  pullback.hom_ext (f := X.obj.hom) (g := Y.obj.hom) h₁ h₂

/-- The diagonal of `T` followed by the first projection of `T × T` is the identity, on underlying
schemes. -/
theorem diag_hom_left_fst (T : (SmoothProjectiveScheme k).FullSubcategory) :
    (diag T).hom.left ≫ (fst T T).hom.left = 𝟙 _ :=
  pullback.diagonal_fst T.obj.hom

/-- The diagonal of `T` followed by the second projection of `T × T` is the identity, on
underlying schemes. -/
theorem diag_hom_left_snd (T : (SmoothProjectiveScheme k).FullSubcategory) :
    (diag T).hom.left ≫ (snd T T).hom.left = 𝟙 _ :=
  pullback.diagonal_snd T.obj.hom

/-- **`Δ_Z = (i × i)⁻¹(Δ_X)`** for a monomorphism `i : Z ⟶ X`: the square
`Δ_Z ≫ (i × i) = i ≫ Δ_X` is cartesian. -/
theorem isPullback_diag_prodMap {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)
    [Mono i.hom.left] :
    IsPullback (diag Z).hom.left i.hom.left (prodMap i i).hom.left (diag X).hom.left := by
  have hw : (diag Z).hom.left ≫ (prodMap i i).hom.left = i.hom.left ≫ (diag X).hom.left := by
    apply prod_left_hom_ext
    · rw [Category.assoc, prodMap_hom_left_fst, ← Category.assoc, diag_hom_left_fst,
        Category.id_comp, Category.assoc, diag_hom_left_fst, Category.comp_id]
    · rw [Category.assoc, prodMap_hom_left_snd, ← Category.assoc, diag_hom_left_snd,
        Category.id_comp, Category.assoc, diag_hom_left_snd, Category.comp_id]
  have key : ∀ s : PullbackCone (prodMap i i).hom.left (diag X).hom.left,
      s.fst ≫ (fst Z Z).hom.left ≫ i.hom.left = s.snd ∧
        s.fst ≫ (snd Z Z).hom.left ≫ i.hom.left = s.snd := by
    intro s
    have h1 := congrArg (· ≫ (fst X X).hom.left) s.condition
    have h2 := congrArg (· ≫ (snd X X).hom.left) s.condition
    rw [Category.assoc, prodMap_hom_left_fst, Category.assoc, diag_hom_left_fst,
      Category.comp_id] at h1
    rw [Category.assoc, prodMap_hom_left_snd, Category.assoc, diag_hom_left_snd,
      Category.comp_id] at h2
    exact ⟨h1, h2⟩
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun s ↦ s.fst ≫ (fst Z Z).hom.left) ?_ ?_ ?_)
  · intro s
    apply prod_left_hom_ext
    · rw [Category.assoc, Category.assoc, diag_hom_left_fst, Category.comp_id]
    · rw [Category.assoc, Category.assoc, diag_hom_left_snd, Category.comp_id]
      exact (cancel_mono i.hom.left).mp (by
        rw [Category.assoc, Category.assoc, (key s).1, (key s).2])
  · exact fun s ↦ (Category.assoc _ _ _).trans (key s).1
  · intro s m hm _
    rw [← hm, Category.assoc, diag_hom_left_fst, Category.comp_id]

/-- The class of a closed subscheme with empty source vanishes. -/
theorem closedSubschemeClass_eq_zero_of_isEmpty {Y A : Scheme.{u}}
    (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sY] (ι : A ⟶ Y) [IsClosedImmersion ι]
    [IsEmpty A] (c : ℤ) : closedSubschemeClass sY ι c = 0 := by
  funext e
  rw [closedSubschemeClass_apply]
  have h0 : cycleAssociatedToClosedSubscheme (fieldChowSituation k) sY ι ((e : ℤ) - c) = 0 :=
    Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦
      cycleAssociatedToClosedSubscheme_apply_eq_zero (fieldChowSituation k) sY ι _ y
        (fun ⟨ξ, _⟩ ↦ isEmptyElim ξ.1))
  rw [h0]
  exact map_zero _

variable {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)

/-- The delta dimension of the diagonal of `X`, equidimensional of dimension `d`, is at most `d`. -/
private theorem schemeDeltaDimension_diag_le {X : (SmoothProjectiveScheme k).FullSubcategory}
    {d : ℕ} (hX : IsNonemptyEquidimensional X d) :
    schemeDeltaDimension (fieldChowSituation k) ((diag X).hom.left ≫ (prod X X).obj.hom)
      ≤ ((((d + d : ℕ) : ℤ) - (d : ℤ) : ℤ) : EInt) := by
  rw [show (((d + d : ℕ) : ℤ) - (d : ℤ)) = (d : ℤ) by push_cast; ring]
  convert schemeDeltaDimension_le_of_relativeDimension _ hX.relativeDimension using 2
  exact Over.w (diag X).hom

/-- **`(i × i)^![Δ_X] = [Δ_Z]`** for an open immersion `i : Z ⟶ X` of schemes equidimensional of
dimension `d`. -/
theorem codimensionGysin_prodMap_diagonalClass [IsOpenImmersion i.hom.left] {d : ℕ}
    (hZ : IsNonemptyEquidimensional Z d) (hX : IsNonemptyEquidimensional X d) :
    codimensionGysin (prod Z Z).obj.hom (prod X X).obj.hom (Over.w (prodMap i i).hom) d
        (diagonalClass X d) = diagonalClass Z d := by
  rw [diagonalClass, codimensionGysin_closedSubschemeClass_of_flat _ _ (Over.w (prodMap i i).hom)
    (isNonemptyEquidimensional_prod hZ hZ).relativeDimension
    (isNonemptyEquidimensional_prod hX hX).relativeDimension
    (relativeDimension_of_isOpenImmersion _) (by omega) _ _ (schemeDeltaDimension_diag_le hX),
    diagonalClass]
  have hp := isPullback_diag_prodMap i
  funext e
  rw [closedSubschemeClass_apply, closedSubschemeClass_apply,
    cycleAssociatedToClosedSubscheme_eq_of_iso (fieldChowSituation k) _ _ (diag Z).hom.left
      hp.isoPullback.symm hp.isoPullback_inv_fst]

/-- **`(f × g)^![Δ_X] = 0`** for open immersions `f, g` into `X` with disjoint images. -/
theorem codimensionGysin_prodMap_diagonalClass_of_disjoint
    {V U : (SmoothProjectiveScheme k).FullSubcategory}
    (f : V ⟶ X) (g : U ⟶ X) [IsOpenImmersion f.hom.left] [IsOpenImmersion g.hom.left]
    (hfg : Disjoint (Set.range f.hom.left) (Set.range g.hom.left)) {d e' : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hVU : RelativeDimension (prod V U).obj.hom e')
    (he' : e' = d + d) :
    codimensionGysin (prod V U).obj.hom (prod X X).obj.hom (Over.w (prodMap f g).hom) d
        (diagonalClass X d) = 0 := by
  subst he'
  rw [diagonalClass, codimensionGysin_closedSubschemeClass_of_flat _ _ (Over.w (prodMap f g).hom)
    hVU (isNonemptyEquidimensional_prod hX hX).relativeDimension
    (relativeDimension_of_isOpenImmersion _) (by omega) _ _ (schemeDeltaDimension_diag_le hX)]
  have : IsEmpty (Limits.pullback (C := Scheme.{u}) (prodMap f g).hom.left (diag X).hom.left) := by
    refine ⟨fun p ↦ ?_⟩
    have hc := congrArg (fun φ ↦ φ p) (pullback.condition (f := (prodMap f g).hom.left)
      (g := (diag X).hom.left))
    have h1 := congrArg (fun φ ↦ φ ((pullback.fst (prodMap f g).hom.left (diag X).hom.left) p))
      (prodMap_hom_left_fst f g)
    have h2 := congrArg (fun φ ↦ φ ((pullback.fst (prodMap f g).hom.left (diag X).hom.left) p))
      (prodMap_hom_left_snd f g)
    have h3 := congrArg (fun φ ↦ φ ((pullback.snd (prodMap f g).hom.left (diag X).hom.left) p))
      (diag_hom_left_fst X)
    have h4 := congrArg (fun φ ↦ φ ((pullback.snd (prodMap f g).hom.left (diag X).hom.left) p))
      (diag_hom_left_snd X)
    simp only [Scheme.Hom.comp_apply] at hc h1 h2 h3 h4
    refine hfg.le_bot ⟨⟨(fst V U).hom.left
      ((pullback.fst (prodMap f g).hom.left (diag X).hom.left) p), rfl⟩,
      ⟨(snd V U).hom.left ((pullback.fst (prodMap f g).hom.left (diag X).hom.left) p), ?_⟩⟩
    refine h2.symm.trans ?_
    rw [hc, h4, ← h1, hc, h3]
  exact closedSubschemeClass_eq_zero_of_isEmpty _ _ _

/-- An open subscheme of a scheme equidimensional of dimension `d` is equidimensional of
dimension `d` once it is nonempty. -/
theorem isNonemptyEquidimensional_of_isOpenImmersion
    {V : (SmoothProjectiveScheme k).FullSubcategory}
    (j : V ⟶ X) [IsOpenImmersion j.hom.left] [Nonempty V.obj.left] {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) : IsNonemptyEquidimensional V d where
  nonempty := inferInstance
  relativeDimension := by
    rw [relativeDimension_iff_forall_mem_dimPart]
    intro v
    rw [mem_dimPart_iff_of_isOpenImmersion V.obj.hom X.obj.hom j.hom.left (Over.w j.hom)]
    exact (relativeDimension_iff_forall_mem_dimPart X.obj.hom d).1 hX.relativeDimension _

end SmoothProjectiveScheme

namespace WeilChernData

open SmoothProjectiveScheme

variable {F : Type w} [Field F] [CharZero F] (𝔚 : WeilChernData k F)

/-- The contraction of (A6) is additive in the linear map. -/
theorem traceContract_add (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (l₁ l₂ : tateTwist F 𝔚.tate (𝔚.grade X (2 * (d : ℤ))) d →ₗ[F] F)
    (g : tateTwist F 𝔚.tate (𝔚.H (prod X X)) d) :
    𝔚.traceContract 𝔚.kunneth X d (l₁ + l₂) g =
      𝔚.traceContract 𝔚.kunneth X d l₁ g + 𝔚.traceContract 𝔚.kunneth X d l₂ g := by
  simp [FirstChernClassData.traceContract, FirstChernClassData.untwistTrace,
    DiagonalExpansion.contractRight, LinearMap.add_comp, LinearMap.lTensor_add]

/-- `λ ∘ f^*` read through `untwistTrace` is `untwistTrace λ ∘ f^*`. -/
theorem untwistTrace_comp_pullGradeTw {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y)
    (d : ℕ) (lam : tateTwist F 𝔚.tate (𝔚.grade X (2 * (d : ℤ))) d →ₗ[F] F) :
    𝔚.untwistTrace Y d (lam ∘ₗ 𝔚.pullGradeTw f (2 * (d : ℤ)) d) =
      𝔚.untwistTrace X d lam ∘ₗ (𝔚.pull f).toLinearMap :=
  LinearMap.ext fun a ↦ (𝔚.untwistTrace_pull f d lam a).symm

variable {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)

/-- `(1 ⊗ λ ∘ g^*)γ([Δ_X])` restricts to `0` along `f` when `f` and `g` are open immersions with
disjoint images. -/
theorem pull_traceContract_eq_zero_of_disjoint {V U : (SmoothProjectiveScheme k).FullSubcategory}
    (f : V ⟶ X) (g : U ⟶ X) [IsOpenImmersion f.hom.left] [IsOpenImmersion g.hom.left]
    (hfg : Disjoint (Set.range f.hom.left) (Set.range g.hom.left)) {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hV : IsNonemptyEquidimensional V d)
    (hU : IsNonemptyEquidimensional U d)
    (lam : tateTwist F 𝔚.tate (𝔚.grade U (2 * (d : ℤ))) d →ₗ[F] F) :
    𝔚.pull f (𝔚.traceContract 𝔚.kunneth X d (lam ∘ₗ 𝔚.pullGradeTw g (2 * (d : ℤ)) d)
      (𝔚.γ (prod X X) d (diagonalClass X d))) = 0 := by
  have h0 := codimensionGysin_prodMap_diagonalClass_of_disjoint f g hfg hX
    (isNonemptyEquidimensional_prod hV hU).relativeDimension rfl
  have hγ := 𝔚.isCohomologicalChernCharacter.codimensionCycleClass_codimensionGysin
    (prodMap f g) d (diagonalClass X d)
  have hT := 𝔚.tensorContractRight_symm_pull_prodMap 𝔚.kunneth f g (𝔚.untwistTrace U d lam)
    (𝔚.κ (prod X X) d (𝔚.γ (prod X X) d (diagonalClass X d)))
  rw [← FirstChernClassData.κ_pullTw, ← hγ, h0, map_zero, map_zero, map_zero, map_zero] at hT
  rw [FirstChernClassData.traceContract_eq, untwistTrace_comp_pullGradeTw]
  exact hT.symm

/-- `(1 ⊗ λ_Z ∘ i^*)γ([Δ_X])` restricts to `1` along an open immersion `i : Z ⟶ X`, `λ_Z`
normalised as in (A6) on `Z`. -/
theorem pull_traceContract_eq_one [IsOpenImmersion i.hom.left] {d : ℕ}
    (hZ : IsNonemptyEquidimensional Z d) (hX : IsNonemptyEquidimensional X d)
    (lam : tateTwist F 𝔚.tate (𝔚.grade Z (2 * (d : ℤ))) d →ₗ[F] F)
    (hlam : 𝔚.traceContract 𝔚.kunneth Z d lam (𝔚.γ (prod Z Z) d (diagonalClass Z d)) = 1) :
    𝔚.pull i (𝔚.traceContract 𝔚.kunneth X d (lam ∘ₗ 𝔚.pullGradeTw i (2 * (d : ℤ)) d)
      (𝔚.γ (prod X X) d (diagonalClass X d))) = 1 := by
  rw [← 𝔚.traceContract_pullTw_prodMap 𝔚.kunneth i d lam,
    ← 𝔚.isCohomologicalChernCharacter.codimensionCycleClass_codimensionGysin,
    codimensionGysin_prodMap_diagonalClass i hZ hX]
  exact hlam

variable [IsClosedImmersion i.hom.left] [IsOpenImmersion i.hom.left]

omit [IsClosedImmersion i.hom.left] in
/-- The image of `i` and the image of the inclusion of its complement are disjoint. -/
theorem disjoint_range_complementι [IsClosedImmersion i.hom.left] :
    Disjoint (Set.range i.hom.left) (Set.range (complementι X i.hom.left).hom.left) := by
  have hr : Set.range (complementι X i.hom.left).hom.left =
      (rangeComplement i.hom.left : Set X.obj.left) :=
    Scheme.Opens.range_ι _
  rw [hr, coe_rangeComplement]
  exact disjoint_compl_right

/-- **The trace on classes vanishing off an open and closed `Z`**, for any maps `λ_X`, `λ_Z`
normalised as in (A6). -/
theorem trace_eq_of_isOpenImmersion_of_normalised {d : ℕ} (hZ : IsNonemptyEquidimensional Z d)
    (hX : IsNonemptyEquidimensional X d)
    (lamX : tateTwist F 𝔚.tate (𝔚.grade X (2 * (d : ℤ))) d →ₗ[F] F)
    (lamZ : tateTwist F 𝔚.tate (𝔚.grade Z (2 * (d : ℤ))) d →ₗ[F] F)
    (hlamX : 𝔚.traceContract 𝔚.kunneth X d lamX (𝔚.γ (prod X X) d (diagonalClass X d)) = 1)
    (hlamZ : 𝔚.traceContract 𝔚.kunneth Z d lamZ (𝔚.γ (prod Z Z) d (diagonalClass Z d)) = 1)
    (a : tateTwist F 𝔚.tate (𝔚.grade X (2 * (d : ℤ))) d)
    (ha : 𝔚.pullGradeTw (complementι X i.hom.left) (2 * (d : ℤ)) d a = 0) :
    lamX a = lamZ (𝔚.pullGradeTw i (2 * (d : ℤ)) d a) := by
  have hcs := nonempty_isColimit_rangeComplement i.hom.left
  have hinj := (𝔚.coproduct.2 Z (complementObj X i.hom.left) X i (complementι X i.hom.left)
    (by exact hcs)).1
  have hdisj := disjoint_range_complementι i
  have huniq := fun μ (hμ : 𝔚.traceContract 𝔚.kunneth X d μ
      (𝔚.γ (prod X X) d (diagonalClass X d)) = 1) ↦
    𝔚.isCohomologicalChernCharacter.trace_unique 𝔚.coproduct 𝔚.projectiveBundle 𝔚.divisor
      𝔚.kunneth 𝔚.blowup X d hX lamX μ hlamX hμ
  have hZ1 := 𝔚.pull_traceContract_eq_one i hZ hX lamZ hlamZ
  by_cases hWne : Nonempty (complementObj X i.hom.left).obj.left
  · have hW : IsNonemptyEquidimensional (complementObj X i.hom.left) d :=
      isNonemptyEquidimensional_of_isOpenImmersion (complementι X i.hom.left) hX
    obtain ⟨lamW, hlamW⟩ := 𝔚.trace _ d hW
    have hsum : 𝔚.traceContract 𝔚.kunneth X d
        (lamZ ∘ₗ 𝔚.pullGradeTw i (2 * (d : ℤ)) d +
          lamW ∘ₗ 𝔚.pullGradeTw (complementι X i.hom.left) (2 * (d : ℤ)) d)
        (𝔚.γ (prod X X) d (diagonalClass X d)) = 1 := by
      rw [traceContract_add]
      refine hinj ?_
      simp only [map_add, map_one, Prod.mk.injEq]
      rw [hZ1, 𝔚.pull_traceContract_eq_zero_of_disjoint i _ hdisj hX hZ hW,
        𝔚.pull_traceContract_eq_zero_of_disjoint _ i hdisj.symm hX hW hZ,
        𝔚.pull_traceContract_eq_one _ hW hX lamW hlamW]
      exact ⟨add_zero _, zero_add _⟩
    have h := LinearMap.congr_fun (huniq _ hsum) a
    rwa [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, ha, map_zero,
      add_zero] at h
  · have : IsEmpty (complementObj X i.hom.left).obj.left := not_nonempty_iff.mp hWne
    have := 𝔚.coproduct.1 (complementObj X i.hom.left) this
    have hone : 𝔚.traceContract 𝔚.kunneth X d (lamZ ∘ₗ 𝔚.pullGradeTw i (2 * (d : ℤ)) d)
        (𝔚.γ (prod X X) d (diagonalClass X d)) = 1 :=
      hinj (Prod.ext (by dsimp only; rw [hZ1, map_one]) (Subsingleton.elim _ _))
    exact LinearMap.congr_fun (huniq _ hone) a

/-- **The trace of `X` on classes vanishing off an open and closed `Z`**: for an open and closed
immersion `i : Z ⟶ X` of nonempty smooth projective schemes equidimensional of dimension `d`,
and `a ∈ H^{2d}(X)(d)` restricting to `0` on the complement `W` of `Z`, `∫_X a = ∫_Z i^*a`, the
trace maps being those of (A6). By (A1) and uniqueness of the trace (Remark 0FIK),
`∫_X = ∫_Z ∘ i^* + ∫_W ∘ ι^*` (with no second term if `W` is empty). -/
theorem trace_eq_trace_pullTw_of_isOpenImmersion {d : ℕ} (hZ : IsNonemptyEquidimensional Z d)
    (hX : IsNonemptyEquidimensional X d) (a : 𝔚.toWeilData.Tw X (2 * (d : ℤ)) d)
    (ha : 𝔚.toWeilData.pullTw (complementι X i.hom.left) _ _ a = 0) :
    𝔚.toWeilData.trace X d hX a = 𝔚.toWeilData.trace Z d hZ (𝔚.toWeilData.pullTw i _ _ a) :=
  𝔚.trace_eq_of_isOpenImmersion_of_normalised i hZ hX _ _
    (𝔚.isCohomologicalChernCharacter.traceContract_toWeilData_trace 𝔚.coproduct
      𝔚.projectiveBundle 𝔚.kunneth 𝔚.trace X d hX)
    (𝔚.isCohomologicalChernCharacter.traceContract_toWeilData_trace 𝔚.coproduct
      𝔚.projectiveBundle 𝔚.kunneth 𝔚.trace Z d hZ) a ha

/-- **`γ([Z]) = i_*1` for an open and closed immersion** `i : Z ⟶ X` of nonempty smooth
projective schemes over `k`, equidimensional of the same dimension `d`: the case of codimension
`0` of the statement that Lemma 0FIR reduces Tag 0FIT to, for the data of (A1)–(A7). Pairing with
`a ∈ H^{2d}(X)(d)`: `∫_X a ∪ γ([Z]) = ∫_Z i^*a`, since `a ∪ γ([Z])` restricts to `0` on the
complement of `Z` and to `i^*a` on `Z`. -/
theorem pushforward_unitTw_eq_cycleClass_of_isOpenImmersion {d : ℕ}
    (hZ : IsNonemptyEquidimensional Z d) (hX : IsNonemptyEquidimensional X d) :
    𝔚.toWeilData.pushforward 𝔚.perfectPairing i hZ hX 0 0 (2 * 0) 0
        (by omega) (by omega) (𝔚.toWeilData.unitTw Z 0 0 rfl) =
      𝔚.toWeilData.cycleClass X 0 (closedSubschemeClass X.obj.hom i.hom.left 0) := by
  have hA := 𝔚.perfectPairing
  have hCa : 𝔚.toWeilData.CycleClassPullback :=
    𝔚.isCohomologicalChernCharacter.cycleClassPullback_toWeilData 𝔚.coproduct
      𝔚.projectiveBundle 𝔚.kunneth 𝔚.trace
  -- `ι^*γ([Z]) = 0` and `i^*γ([Z]) = 1`
  have hι : 𝔚.toWeilData.pullTw (complementι X i.hom.left) (2 * 0) 0
      (𝔚.toWeilData.cycleClass X 0 (closedSubschemeClass X.obj.hom i.hom.left 0)) = 0 := by
    rw [← hCa (complementι X i.hom.left) 0 (closedSubschemeClass X.obj.hom i.hom.left 0),
      codimensionGysin_closedSubschemeClass_of_disjoint_range (complementι X i.hom.left)
        i.hom.left (disjoint_range_complementι i).symm, map_zero]
  have hi : (𝔚.toWeilData.twCoord Z (2 * 0) 0 (𝔚.toWeilData.pullTw i (2 * 0) 0
      (𝔚.toWeilData.cycleClass X 0 (closedSubschemeClass X.obj.hom i.hom.left 0)))).1 = 1 := by
    rw [← hCa i 0 (closedSubschemeClass X.obj.hom i.hom.left 0),
      codimensionGysin_closedSubschemeClass_of_isOpenImmersion_self i]
    refine (𝔚.isCohomologicalChernCharacter.coe_twCoord_toWeilData_cycleClass 𝔚.coproduct
      𝔚.projectiveBundle 𝔚.kunneth 𝔚.trace Z 0 (fundamentalClass Z)).trans ?_
    rw [𝔚.isCohomologicalChernCharacter.codimensionCycleClass_fundamentalClass]
    exact 𝔚.κ_unitTw Z
  refine WeilData.eq_of_pairingTw_eq hA hX (2 * (d : ℤ)) (2 * 0) (by ring) d 0 (by ring)
    fun a ↦ ?_
  rw [← WeilData.pushforward_trace' hA i hZ hX 0 0 (2 * 0) 0 (by omega) (by omega) (2 * (d : ℤ))
      d (by ring) (by ring) (by ring) (by ring) a (𝔚.toWeilData.unitTw Z 0 0 rfl),
    WeilData.pairingTw_unitTw_right, WeilData.pairingTw_apply,
    𝔚.trace_eq_trace_pullTw_of_isOpenImmersion i hZ hX _ (by
      rw [WeilData.pullTw_cupTw, hι, map_zero]),
    WeilData.pullTw_cupTw,
    𝔚.toWeilData.cupTw_eq_self_of_coe_twCoord_eq_one_right Z _ _ _ _ _ _ _ _ hi]

end WeilChernData

end Stacks.WeilCohomology

end
