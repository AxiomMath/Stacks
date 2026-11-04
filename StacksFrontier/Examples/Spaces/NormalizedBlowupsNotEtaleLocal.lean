module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.LocalRingPropertyList
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.GermPropertyAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationExcisionEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSpaceConstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizedBlowupsAtClosedPointsEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.FieldPointCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.BlowupExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.ClosedPointNeighborhoodsOfDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet

/-!
# Stacks 0BHL is false without normality

Let `X` be a decent algebraic space with pairwise distinct closed points `x₁, …, xₙ` and chosen
elementary étale neighbourhoods `(Uᵢ, uᵢ) ⟶ (X, xᵢ)` (Stacks 0BH9), and let `f : Y ⟶ X`
correspond to `gᵢ : Yᵢ ⟶ Uᵢ` under the equivalence `F` of Stacks 0BHA. **Stacks 0BHL** asserts
that, when `X` satisfies the conditions of Stacks 0BB1, `f` is a sequence of normalized
blowings up at closed points over `{x₁, …, xₙ}` if and only if every `gᵢ` is a sequence of
normalized blowings up at closed points over `uᵢ`.

This is false as written: a normalized blowing up normalizes the whole space, so a sequence of
length at least one has a normal source, while an empty sequence is an isomorphism. Here is a
counterexample to the "if" direction. Let `R = ℤ/36ℤ` and `X = Spec R`, a space with exactly
two points `x₁ = (2)` and `x₂ = (3)`, at each of which the local ring (`ℤ/4ℤ`, `ℤ/9ℤ`) is not
reduced. Every elementary étale neighbourhood `Uᵢ` of `xᵢ` is then not normal, its local ring
at `uᵢ` being étale over that of `X` at `xᵢ`, and `Uᵢ ∖ {uᵢ}` has no points at all. Let `g₁` be
the normalized blowing up of `U₁` at `u₁`, let `g₂ = id`, and let `f : Y ⟶ X` correspond to
`(g₁, g₂)` under `F` (Stacks 0BHB). Both `gᵢ` are sequences as required, of lengths one and
zero. But `f` is not: an empty sequence would make `f`, hence its base change `g₁`, an
isomorphism, and then `U₁` would be normal like the source of `g₁`; a sequence of positive
length would make `Y` normal, hence its étale base change `Y ×_X U₂ ≅ U₂` normal.

## Main results

* `Stacks.Examples.NormalizedBlowupsNotEtaleLocal.exists_counterexample`: the counterexample to
  the "if" direction of Stacks 0BHL.
* `Stacks.Examples.NormalizedBlowupsNotEtaleLocal.not_stacks0BHL`: the published statement,
  quantified as the source states it and under exactly its hypotheses, is false.

## Implementation notes

The corrected statement, with `X` normal, is `nonempty_globalNormalizedBlowupFactorization_iff`
in the namespace `AlgebraicGeometry.Space.ClosedPointNeighborhoods`. The statement refuted here is
that one with the normality hypothesis removed, and nothing else changed.

The non-normality of the neighbourhoods is read off from reducedness of local rings, which is
étale local (`AlgebraicGeometry.GermOfScheme.isEtaleLocal_isReduced_stalk`): every stalk of
`Spec R` has the nonzero nilpotent `6`. That `Uᵢ ∖ {uᵢ}` has no points makes every algebraic
space over `Uᵢ` unchanged over it, so `g₁` and `g₂` are objects of `C_{Uᵢ, uᵢ}` without any
computation of the normalized blowing up: its existence is
`AlgebraicGeometry.Space.exists_isBlowupAlong_of_isLocallyNoetherian` followed by Stacks 07U4.

## References

* [Stacks Project, Tag 0BHL](https://stacks.math.columbia.edu/tag/0BHL)
* [Stacks Project, Tag 0BHA](https://stacks.math.columbia.edu/tag/0BHA)
* [Stacks Project, Tag 0BHB](https://stacks.math.columbia.edu/tag/0BHB)
* [Stacks Project, Tag 0BHJ](https://stacks.math.columbia.edu/tag/0BHJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Space CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Examples.NormalizedBlowupsNotEtaleLocal

attribute [local instance] pointTopology

/-! ### The ring `ℤ/36ℤ` -/

/-- The ring `ℤ/36ℤ`, in the universe `u`. -/
abbrev R : Type u := ULift.{u} (ZMod 36)

/-- The residue class of `n` in `R`. -/
abbrev cls (n : ZMod 36) : R.{u} := ULift.up n

/-- Multiplication of residue classes. -/
theorem cls_mul (a b : ZMod 36) : cls.{u} a * cls b = cls (a * b) := rfl

/-- Addition of residue classes. -/
theorem cls_add (a b : ZMod 36) : cls.{u} a + cls b = cls (a + b) := rfl

/-- `6 * 6 = 0` in `R`. -/
theorem cls_six_mul_six : cls.{u} 6 * cls 6 = 0 :=
  congrArg ULift.up (by decide : (6 : ZMod 36) * 6 = 0)

/-- `6` lies in every prime of `R`, its square being zero. -/
theorem cls_six_mem (P : Ideal R.{u}) [hP : P.IsPrime] : cls 6 ∈ P :=
  hP.mem_of_pow_mem 2 (by rw [pow_two, cls_six_mul_six]; exact P.zero_mem)

/-- An element killed by `6` is a multiple of `6`. -/
theorem exists_eq_cls_six_mul_of_mul_cls_six_eq_zero (s : R.{u}) (hs : s * cls 6 = 0) :
    ∃ t, s = cls 6 * t := by
  obtain ⟨s⟩ := s
  have key : ∀ s : ZMod 36, s * 6 = 0 → ∃ t, s = 6 * t := by decide
  obtain ⟨t, ht⟩ := key s (congrArg ULift.down hs)
  exact ⟨cls t, congrArg ULift.up ht⟩

/-- A prime of `R` containing `c` consists of the multiples of `c`, given that every
`x : ZMod 36` which is not a multiple of `c` satisfies `x * x + c * b = 1` for some `b`. -/
private theorem mem_iff_of_cls_mem (c : ZMod 36)
    (key : ∀ x : ZMod 36, (¬ ∃ y, x = c * y) → ∃ b, x * x + c * b = 1)
    (P : Ideal R.{u}) [hP : P.IsPrime] (hc : cls c ∈ P) (x : R.{u}) :
    x ∈ P ↔ ∃ y, x = cls c * y := by
  constructor
  · intro hx
    by_contra hne
    obtain ⟨b, hb⟩ : ∃ b, x * x + cls c * b = 1 := by
      obtain ⟨x⟩ := x
      obtain ⟨b, hb⟩ := key x fun ⟨y, hy⟩ => hne ⟨cls y, congrArg ULift.up hy⟩
      exact ⟨cls b, congrArg ULift.up hb⟩
    exact hP.ne_top ((Ideal.eq_top_iff_one _).2
      (hb ▸ P.add_mem (P.mul_mem_left x hx) (P.mul_mem_right b hc)))
  · rintro ⟨y, rfl⟩
    exact P.mul_mem_right y hc

/-- A prime of `R` containing `2` consists of the multiples of `2`. -/
theorem mem_iff_of_cls_two_mem (P : Ideal R.{u}) [hP : P.IsPrime] (h2 : cls 2 ∈ P) (x : R.{u}) :
    x ∈ P ↔ ∃ y, x = cls 2 * y :=
  mem_iff_of_cls_mem 2 (by decide) P h2 x

/-- A prime of `R` containing `3` consists of the multiples of `3`. -/
theorem mem_iff_of_cls_three_mem (P : Ideal R.{u}) [hP : P.IsPrime] (h3 : cls 3 ∈ P)
    (x : R.{u}) : x ∈ P ↔ ∃ y, x = cls 3 * y :=
  mem_iff_of_cls_mem 3 (by decide) P h3 x

/-- There is a maximal ideal of `R` containing `n`, for `n` a non-unit. -/
theorem exists_isMaximal_cls_mem (n : ZMod 36) (hn : ∀ b : ZMod 36, n * b ≠ 1) :
    ∃ M : Ideal R.{u}, M.IsMaximal ∧ cls n ∈ M := by
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {cls.{u} n}) (by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    obtain ⟨⟨b⟩, hb⟩ := hu.exists_right_inv
    exact hn b (congrArg ULift.down hb))
  exact ⟨M, hM, hle (Ideal.subset_span rfl)⟩

/-- The maximal ideal `(2)` of `R`. -/
def m₂ : PrimeSpectrum R.{u} :=
  ⟨(exists_isMaximal_cls_mem 2 (by decide)).choose,
    (exists_isMaximal_cls_mem 2 (by decide)).choose_spec.1.isPrime⟩

/-- The maximal ideal `(3)` of `R`. -/
def m₃ : PrimeSpectrum R.{u} :=
  ⟨(exists_isMaximal_cls_mem 3 (by decide)).choose,
    (exists_isMaximal_cls_mem 3 (by decide)).choose_spec.1.isPrime⟩

/-- `m₂` is a maximal ideal. -/
theorem isMaximal_m₂ : (m₂.{u}).asIdeal.IsMaximal :=
  (exists_isMaximal_cls_mem 2 (by decide)).choose_spec.1

/-- `m₃` is a maximal ideal. -/
theorem isMaximal_m₃ : (m₃.{u}).asIdeal.IsMaximal :=
  (exists_isMaximal_cls_mem 3 (by decide)).choose_spec.1

/-- `2 ∈ m₂`. -/
theorem cls_two_mem_m₂ : cls 2 ∈ (m₂.{u}).asIdeal :=
  (exists_isMaximal_cls_mem 2 (by decide)).choose_spec.2

/-- `3 ∈ m₃`. -/
theorem cls_three_mem_m₃ : cls 3 ∈ (m₃.{u}).asIdeal :=
  (exists_isMaximal_cls_mem 3 (by decide)).choose_spec.2

/-- **`R` has exactly the two primes `(2)` and `(3)`.** -/
theorem eq_m₂_or_eq_m₃ (P : PrimeSpectrum R.{u}) : P = m₂ ∨ P = m₃ := by
  have h6 : cls 2 * cls 3 ∈ P.asIdeal := by
    rw [cls_mul]
    exact cls_six_mem P.asIdeal
  rcases P.isPrime.mem_or_mem h6 with h2 | h3
  · left
    ext x
    rw [mem_iff_of_cls_two_mem P.asIdeal h2, mem_iff_of_cls_two_mem m₂.asIdeal cls_two_mem_m₂]
  · right
    ext x
    rw [mem_iff_of_cls_three_mem P.asIdeal h3,
      mem_iff_of_cls_three_mem m₃.asIdeal cls_three_mem_m₃]

/-- The primes `(2)` and `(3)` of `R` are distinct. -/
theorem m₂_ne_m₃ : m₂.{u} ≠ m₃ := by
  intro h
  have h3 : cls 3 ∈ (m₂.{u}).asIdeal := h ▸ cls_three_mem_m₃
  obtain ⟨⟨y⟩, hy⟩ := (mem_iff_of_cls_two_mem m₂.asIdeal cls_two_mem_m₂ _).1 h3
  have key : ∀ y : ZMod 36, (3 : ZMod 36) ≠ 2 * y := by decide
  exact key y (congrArg ULift.down hy)

/-- **No local ring of `Spec R` is reduced**: `6` is a nonzero nilpotent in each of them. -/
theorem not_isReduced_stalk (q : PrimeSpectrum R.{u}) :
    ¬ _root_.IsReduced ((Spec (.of R.{u})).presheaf.stalk q) := by
  intro hred
  let _ : Algebra R ((Spec (.of R.{u})).presheaf.stalk q) := StructureSheaf.stalkAlgebra R q
  have : IsLocalization.AtPrime ((Spec (.of R.{u})).presheaf.stalk q) q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R q
  have hnil : IsNilpotent (algebraMap R ((Spec (.of R.{u})).presheaf.stalk q) (cls 6)) :=
    ⟨2, by rw [← map_pow, pow_two, cls_six_mul_six, map_zero]⟩
  obtain ⟨⟨m, hm⟩, hm0⟩ :=
    (IsLocalization.map_eq_zero_iff q.asIdeal.primeCompl _ (cls 6)).1 hnil.eq_zero
  obtain ⟨t, rfl⟩ := exists_eq_cls_six_mul_of_mul_cls_six_eq_zero m hm0
  exact hm (q.asIdeal.mul_mem_right t (cls_six_mem q.asIdeal))

/-! ### Algebraic spaces over an open subspace with no points -/

section NoPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Two morphisms into an algebraic space agree when every section of their source lives over a
test scheme with no points: the target has a single section over such a test scheme. -/
theorem hom_ext_of_isEmpty {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (Y : AlgebraicSpaces B S hS)
    (hG : ∀ T : BigFppfOver B S hS, G.obj (op T) →
      IsEmpty ((BigFppfOver.toScheme B S hS).obj T))
    (a b : G ⟶ Y.obj) : a = b := by
  ext T x
  have := uniqueSectionsOfIsEmpty Y T.unop (hG T.unop x)
  exact Subsingleton.elim _ _

/-- A section of the subspace cut out by a set of points containing no point lives over a test
scheme with no points. -/
theorem isEmpty_of_openSubspaceOfPoints {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W : Set (points B S hS F)} (hW : ∀ p, p ∉ W) (T : BigFppfOver B S hS)
    (x : (openSubspaceOfPoints B S hS F W).toFunctor.obj (op T)) :
    IsEmpty ((BigFppfOver.toScheme B S hS).obj T) :=
  ⟨fun t => hW _ (x.2 ⟨(schemePointsHomeomorph B S hS T).symm t, rfl⟩)⟩

/-- **Every algebraic space over `F` is unchanged over an open subspace with no points.** Over
such a subspace all sections live over test schemes with no points, where an algebraic space
has a single section. -/
theorem isIso_pullback_snd_openSubspaceOfPoints (F Y : AlgebraicSpaces B S hS)
    (l : Y.obj ⟶ F.obj) {W : Set (points B S hS F.obj)} (hW : ∀ p, p ∉ W) :
    IsIso (pullback.snd l (openSubspaceOfPoints B S hS F.obj W).ι) := by
  set V := openSubspaceOfPoints B S hS F.obj W
  have hV := isEmpty_of_openSubspaceOfPoints hW
  let s : V.toFunctor ⟶ Y.obj :=
    { app := fun T => ↾fun x =>
        @default _ (uniqueSectionsOfIsEmpty Y T.unop (hV T.unop x)).toInhabited
      naturality := by
        intro T T' g
        ext x
        have := uniqueSectionsOfIsEmpty Y T'.unop (hV T'.unop (V.toFunctor.map g x))
        exact Subsingleton.elim _ _ }
  have hs : s ≫ l = V.ι := hom_ext_of_isEmpty F hV _ _
  have hP : ∀ T : BigFppfOver B S hS, (pullback l V.ι).obj (op T) →
      IsEmpty ((BigFppfOver.toScheme B S hS).obj T) :=
    fun T x => hV T ((pullback.snd l V.ι).app (op T) x)
  refine ⟨⟨pullback.lift s (𝟙 _) (by rw [hs, Category.id_comp]), ?_,
    pullback.lift_snd _ _ _⟩⟩
  exact pullback.hom_ext (hom_ext_of_isEmpty Y hP _ _)
    (by rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp])

end NoPoints

/-! ### The counterexample, for any neighbourhoods of a space of the right kind -/

section General

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The top of a tower of normalized blowings up is the base, up to the isomorphism `proj`, or
it is normal, being the source of a normalized blowing up. -/
theorem isIso_proj_or_isNormal {X : AlgebraicSpaces B S hS} :
    ∀ {Z : AlgebraicSpaces B S hS} (t : NormalizedBlowupTower B S hS X Z),
      IsIso t.proj ∨ Space.IsNormal B S hS Z.obj
  | _, .base e => Or.inl (by rw [NormalizedBlowupTower.proj_base]; infer_instance)
  | _, .step _ _ _ _ _ _ hb => Or.inr hb.isNormal

variable {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

/-- The finiteness condition of Stacks 0BB1 passes from `X` to its étale neighbourhoods. -/
theorem hasLocallyFiniteIrreducibleComponents_neighborhoodSpace
    (hXfin : HasLocallyFiniteIrreducibleComponents B S hS D.space.obj) (i : Fin n) :
    HasLocallyFiniteIrreducibleComponents B S hS (D.neighborhoodSpace i).obj :=
  fun V f hf => hXfin V (f ≫ (D.neighborhood i).toSpace)
    (isEtale_comp B S hS hf (D.neighborhood i).etale_toSpace)

/-- Local noetherianity passes from `X` to its étale neighbourhoods. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_neighborhoodSpace
    (hX : HasEtaleLocalProperty B S hS D.space.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (i : Fin n) :
    HasEtaleLocalProperty B S hS (D.neighborhoodSpace i).obj
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
  hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType B S hS
    (D.neighborhoodSpace i).property D.space.property (D.neighborhood i).toSpace
    (isLocallyOfFiniteType_of_isEtale' B S hS _ (D.neighborhood i).etale_toSpace) hX

/-- **The normalized blowing up of a neighbourhood at its point exists**, for a locally
Noetherian `X` satisfying the conditions of Stacks 0BB1: the blowing up exists, and its
normalization by Stacks 07U4. -/
theorem exists_isNormalizedBlowupAtClosedPoint_neighborhoodSpace
    (hXfin : HasLocallyFiniteIrreducibleComponents B S hS D.space.obj)
    (hX : HasEtaleLocalProperty B S hS D.space.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (i : Fin n) :
    ∃ (Z : AlgebraicSpaces B S hS) (g : Z ⟶ D.neighborhoodSpace i),
      IsNormalizedBlowupAtClosedPoint B S hS (isDecentSpace_yoneda B S hS _)
        (hasLocallyFiniteIrreducibleComponents_neighborhoodSpace D hXfin i)
        (D.neighborhoodPoint i) (D.isClosed_neighborhoodPoint i) g := by
  obtain ⟨X', b, hb, hfin'⟩ := exists_isBlowupAlong_of_isLocallyNoetherian
    (hasEtaleLocalProperty_isLocallyNoetherian_neighborhoodSpace D hX i)
    (closedPointSubspace B S hS (D.neighborhoodPoint i) (D.isClosed_neighborhoodPoint i))
  let N := (nonempty_normalizationData B S hS X'.property
    (hfin' (hasLocallyFiniteIrreducibleComponents_neighborhoodSpace D hXfin i))).some
  exact ⟨_, _, isNormalizedBlowupAtClosedPoint_comp _ _
    (isBlowupAtClosedPoint_of_isBlowupAlong hb) N⟩

/-- When every point of `X` is one of the chosen points, the distinguished point is the only
point of a neighbourhood. -/
theorem eq_neighborhoodPoint (hpts : ∀ x, x ∈ Set.range D.point) (i : Fin n)
    (y : points B S hS (D.neighborhoodSpace i).obj) : y = D.neighborhoodPoint i := by
  by_contra hy
  exact D.map_notMem_range_point i y hy (hpts _)

/-- When every point of `X` is one of the chosen points, every algebraic space over a
neighbourhood `Uᵢ` is an object of `C_{Uᵢ, uᵢ}`, the open `Uᵢ ∖ {uᵢ}` having no points. -/
def modificationOf (hpts : ∀ x, x ∈ Set.range D.point) (i : Fin n) {Z : AlgebraicSpaces B S hS}
    (g : Z ⟶ D.neighborhoodSpace i) : D.modificationsAt i :=
  ⟨Over.mk g.hom, Z.property, isIso_pullback_snd_openSubspaceOfPoints (D.neighborhoodSpace i) Z
    g.hom fun p hp => hp (eq_neighborhoodPoint D hpts i p)⟩

/-- **The counterexample to the "if" direction of Stacks 0BHL**, for any data of Stacks 0BHA
in which `X` is locally Noetherian, every point of `X` is one of the chosen points, there are
two of them, and no neighbourhood is normal. Take `g` to be the normalized blowing up of `U_{i₀}`
at its point and the identity of every other neighbourhood, and `f` corresponding to it under
the equivalence of Stacks 0BHB. Every `gᵢ` is a sequence of normalized blowings up, of length
one or zero. The morphism `f` is not: if it were an isomorphism, so would be its base change
`g_{i₀}`, making `U_{i₀}` normal like the source of `g_{i₀}`; otherwise `Y` would be normal,
hence its étale base change `Y ×_X U_{i₁} ≅ U_{i₁}` too. -/
theorem exists_counterexample_of
    (hXfin : HasLocallyFiniteIrreducibleComponents B S hS D.space.obj)
    (hX : HasEtaleLocalProperty B S hS D.space.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hpts : ∀ x, x ∈ Set.range D.point)
    (hnn : ∀ i, ¬ Space.IsNormal B S hS (D.neighborhoodSpace i).obj)
    (i₀ i₁ : Fin n) (h01 : i₀ ≠ i₁) :
    ∃ (M : D.modificationsAwayFromPoints) (N : ∀ i, D.modificationsAt i)
      (_ : D.restrictionFunctor.obj M ≅ N),
      (∀ i, Nonempty (D.LocalNormalizedBlowupFactorization i
        (ObjectProperty.homMk (N i).obj.hom :
          (⟨(N i).obj.left, (N i).property.1⟩ : AlgebraicSpaces B S hS) ⟶
            D.neighborhoodSpace i))) ∧
      ¬ Nonempty (D.GlobalNormalizedBlowupFactorization (ObjectProperty.homMk M.obj.hom :
        (⟨M.obj.left, M.property.1⟩ : AlgebraicSpaces B S hS) ⟶ D.space)) := by
  classical
  choose Z g hg using exists_isNormalizedBlowupAtClosedPoint_neighborhoodSpace D hXfin hX
  let N : ∀ i, D.modificationsAt i := fun i =>
    if i = i₀ then modificationOf D hpts i (g i) else modificationOf D hpts i (𝟙 _)
  have hN₀ : N i₀ = modificationOf D hpts i₀ (g i₀) := ite_eq_left rfl
  have hN₁ : N i₁ = modificationOf D hpts i₁ (𝟙 _) := ite_eq_right h01.symm
  have : D.restrictionFunctor.IsEquivalence := D.isEquivalence_restrictionFunctor
  let M := D.restrictionFunctor.objPreimage N
  let e : D.restrictionFunctor.obj M ≅ N := D.restrictionFunctor.objObjPreimageIso N
  refine ⟨M, N, e, fun i => ?_, ?_⟩
  · by_cases hi : i = i₀
    · subst hi
      rw [hN₀]
      exact ⟨NormalizedBlowupFactorization.ofBlowup _ (hg i) (Set.mem_singleton _)⟩
    · have hNi : N i = modificationOf D hpts i (𝟙 _) := ite_eq_right hi
      rw [hNi]
      exact ⟨NormalizedBlowupFactorization.ofIso _ (Iso.refl _)⟩
  · rintro ⟨F⟩
    set f : (⟨M.obj.left, M.property.1⟩ : AlgebraicSpaces B S hS) ⟶ D.space :=
      ObjectProperty.homMk M.obj.hom
    rcases isIso_proj_or_isNormal F.tower with hiso | hnorm
    · have hf : IsIso f := by
        rw [← F.iso_proj]
        infer_instance
      obtain ⟨E, hE⟩ := D.exists_iso_restrictionHom_of_iso e i₀
      have h1 : IsIso (D.restrictionHom i₀ f) :=
        (AlgebraicSpaces.isPullback_fiberProduct B S hS f (D.toSpaceHom i₀)).isIso_snd_of_isIso
      have h2 : IsIso (E.hom ≫ (ObjectProperty.homMk (N i₀).obj.hom :
          (⟨(N i₀).obj.left, (N i₀).property.1⟩ : AlgebraicSpaces B S hS) ⟶
            D.neighborhoodSpace i₀)) := by
        rw [hE]
        exact h1
      have h3 : IsIso (ObjectProperty.homMk (N i₀).obj.hom :
          (⟨(N i₀).obj.left, (N i₀).property.1⟩ : AlgebraicSpaces B S hS) ⟶
            D.neighborhoodSpace i₀) :=
        IsIso.of_isIso_comp_left E.hom _
      have hsrc : Space.IsNormal B S hS (N i₀).obj.left := by
        rw [hN₀]
        exact (hg i₀).isNormal
      exact hnn i₀ (isNormal_of_iso (asIso (ObjectProperty.homMk (N i₀).obj.hom :
          (⟨(N i₀).obj.left, (N i₀).property.1⟩ : AlgebraicSpaces B S hS) ⟶
            D.neighborhoodSpace i₀)).symm hsrc)
    · have hY : Space.IsNormal B S hS M.obj.left := isNormal_of_iso F.iso hnorm
      obtain ⟨E, -⟩ := D.exists_iso_restrictionHom_of_iso e i₁
      have hfib : Space.IsNormal B S hS
          (AlgebraicSpaces.fiberProduct B S hS f (D.toSpaceHom i₁)).obj :=
        hasEtaleLocalProperty_of_isEtale B S hS
          (AlgebraicSpaces.fiberProduct B S hS f (D.toSpaceHom i₁)).property M.property.1
          (isEtale_pullback_fst B S hS M.property.1 D.space.property
            (D.neighborhoodSpace i₁).property _ _ (D.neighborhood i₁).etale_toSpace) hY
      have hsrc : Space.IsNormal B S hS (N i₁).obj.left := isNormal_of_iso E.symm hfib
      rw [hN₁] at hsrc
      exact hnn i₁ hsrc

end General

/-! ### `Spec(ℤ/36ℤ)` -/

section Concrete

variable (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of R.{u})))

/-- `X = Spec(ℤ/36ℤ)`, as the algebraic space it represents over itself. -/
abbrev space : AlgebraicSpaces B (Spec (.of R.{u})) hS :=
  schemeSpace (baseTerminal B _ hS)

/-- The point of `X` at a prime of `R`. -/
def toPoint (P : PrimeSpectrum R.{u}) : points B (Spec (.of R.{u})) hS (space B hS).obj :=
  (schemePointsHomeomorph B _ hS (baseTerminal B _ hS)).symm P

/-- Distinct primes of `R` give distinct points of `X`. -/
theorem toPoint_injective : Function.Injective (toPoint B hS) :=
  (schemePointsHomeomorph B _ hS (baseTerminal B _ hS)).symm.injective

/-- The point of `X` at a maximal ideal of `R` is closed. -/
theorem isClosed_toPoint (P : PrimeSpectrum R.{u}) (hP : P.asIdeal.IsMaximal) :
    IsClosed ({toPoint B hS P} : Set (points B (Spec (.of R.{u})) hS (space B hS).obj)) := by
  set e := schemePointsHomeomorph B _ hS (baseTerminal B _ hS)
  have hpre : ({toPoint B hS P} : Set (points B (Spec (.of R.{u})) hS (space B hS).obj)) =
      e ⁻¹' {P} := by
    ext y
    exact e.toEquiv.eq_symm_apply
  rw [hpre]
  exact ((PrimeSpectrum.isClosed_singleton_iff_isMaximal P).2 hP).preimage e.continuous

/-- Every point of `X` is `(2)` or `(3)`. -/
theorem eq_toPoint_m₂_or_eq_toPoint_m₃ (y : points B (Spec (.of R.{u})) hS (space B hS).obj) :
    y = toPoint B hS m₂ ∨ y = toPoint B hS m₃ := by
  have hy : y = toPoint B hS (schemePointsHomeomorph B _ hS (baseTerminal B _ hS) y) :=
    ((schemePointsHomeomorph B _ hS (baseTerminal B _ hS)).symm_apply_apply y).symm
  exact (eq_m₂_or_eq_m₃ (schemePointsHomeomorph B _ hS (baseTerminal B _ hS) y)).imp
    (fun h => hy.trans (congrArg _ h)) fun h => hy.trans (congrArg _ h)

/-- **A scheme étale over `X` with a point is not normal**: its local ring at that point is
étale over a local ring of `X`, and reducedness of local rings is étale local, while no local
ring of `X` is reduced. -/
theorem not_isNormal_of_isEtale {U : BigFppfOver B (Spec (.of R.{u})) hS}
    (a : yoneda.obj U ⟶ (space B hS).obj) (ha : IsEtale B _ hS a)
    (y : points B (Spec (.of R.{u})) hS (yoneda.obj U)) :
    ¬ Space.IsNormal B _ hS (yoneda.obj U) := by
  intro hn
  have hU : _root_.AlgebraicGeometry.IsNormal ((BigFppfOver.toScheme B _ hS).obj U) :=
    (exists_atlas_iff_forall_etale B _ hS _
      (fun X : Scheme.{u} => _root_.AlgebraicGeometry.IsNormal X)
      (isAlgebraicSpace_yoneda B _ hS U)).mp hn U (𝟙 _) (presheaf_etale_of_iso B _ hS (Iso.refl _))
  obtain ⟨p, -⟩ := Quot.exists_rep y
  obtain ⟨q, hq⟩ := Quot.exists_rep (pointsMap B _ hS _ a (p.class B _ hS _))
  have h := chart_germ_property_iff B _ hS (space B hS).property a (𝟙 _)
    (presheaf_etale_of_isEtale B _ hS ha) (presheaf_etale_of_iso B _ hS (Iso.refl _)) p q
    (hq.symm.trans (congrFun (pointsMap_id B _ hS _) _).symm) _
    GermOfScheme.isEtaleLocal_isReduced_stalk
  exact not_isReduced_stalk (schemePoint B _ hS _ q) (h.mp inferInstance)

/-- The two points `(2)` and `(3)` of `X`. -/
def chosenPoints : Fin 2 → points B (Spec (.of R.{u})) hS (space B hS).obj :=
  ![toPoint B hS m₂, toPoint B hS m₃]

/-- The two chosen points are distinct. -/
theorem chosenPoints_injective : Function.Injective (chosenPoints B hS) := by
  intro i j hij
  have hne : toPoint B hS m₂ ≠ toPoint B hS m₃ := fun h => m₂_ne_m₃ (toPoint_injective B hS h)
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd hij hne
  · exact absurd hij.symm hne
  · rfl

/-- The two chosen points are closed. -/
theorem isClosed_chosenPoints (i : Fin 2) :
    IsClosed ({chosenPoints B hS i} : Set (points B (Spec (.of R.{u})) hS (space B hS).obj)) := by
  fin_cases i
  · exact isClosed_toPoint B hS _ isMaximal_m₂
  · exact isClosed_toPoint B hS _ isMaximal_m₃

/-- The data of Stacks 0BHA for `X` and its two points. -/
def neighborhoods : ClosedPointNeighborhoods B (Spec (.of R.{u})) hS 2 :=
  ClosedPointNeighborhoods.ofPoints (space B hS) (isDecentSpace_yoneda B _ hS _)
    (chosenPoints B hS) (chosenPoints_injective B hS) (isClosed_chosenPoints B hS)

/-- Every point of `X` is one of the two chosen points. -/
theorem mem_range_point (y : points B (Spec (.of R.{u})) hS (neighborhoods B hS).space.obj) :
    y ∈ Set.range (neighborhoods B hS).point := by
  rcases eq_toPoint_m₂_or_eq_toPoint_m₃ B hS y with h | h
  · exact ⟨0, h.symm⟩
  · exact ⟨1, h.symm⟩

/-- `X` satisfies the finiteness condition of Stacks 0BB1. -/
theorem hasLocallyFiniteIrreducibleComponents_space :
    HasLocallyFiniteIrreducibleComponents B _ hS (neighborhoods B hS).space.obj := by
  have : IsIso (𝟙 (Spec (.of R.{u})) :
      (BigFppfOver.toScheme B _ hS).obj (baseTerminal B _ hS) ⟶ Spec (.of R.{u})) := IsIso.id _
  exact hasLocallyFiniteIrreducibleComponents_of_isLocallyOfFiniteType B _ hS (A := R.{u}) (𝟙 _)
    (𝟙 (Spec (.of R.{u})) : (BigFppfOver.toScheme B _ hS).obj (baseTerminal B _ hS) ⟶ _)
    (isLocallyOfFiniteType_of_isEtale' B _ hS _ (isEtale_of_iso B _ hS (Iso.refl _)))

/-- `X` is locally Noetherian. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_space :
    HasEtaleLocalProperty B _ hS (neighborhoods B hS).space.obj
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
  hasEtaleLocalProperty_of_representable B _ hS _ (fun T : Scheme.{u} => IsLocallyNoetherian T)
    (baseTerminal B _ hS) (Iso.refl _) (inferInstanceAs (IsLocallyNoetherian (Spec (.of R.{u}))))

end Concrete

/-- **The "if" direction of Stacks 0BHL fails without normality.** There are a scheme `S`,
a decent algebraic space `X` over `S` satisfying the conditions of Stacks 0BB1 with closed points
`x₁, x₂` and neighbourhoods as in Stacks 0BHA, and `f : Y ⟶ X` corresponding to `(g₁, g₂)`
under the functor `F` of Stacks 0BHA, such that each `gᵢ` is a sequence of normalized blowings
up at closed points over `uᵢ` but `f` is not a sequence of normalized blowings up at closed
points over `{x₁, x₂}`. Here `X = S = Spec(ℤ/36ℤ)`. -/
theorem exists_counterexample :
    ∃ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
      (D : ClosedPointNeighborhoods B S hS 2)
      (_ : HasLocallyFiniteIrreducibleComponents B S hS D.space.obj)
      (M : D.modificationsAwayFromPoints) (N : ∀ i, D.modificationsAt i)
      (_ : D.restrictionFunctor.obj M ≅ N),
      (∀ i, Nonempty (D.LocalNormalizedBlowupFactorization i
        (ObjectProperty.homMk (N i).obj.hom :
          (⟨(N i).obj.left, (N i).property.1⟩ : AlgebraicSpaces B S hS) ⟶
            D.neighborhoodSpace i))) ∧
      ¬ Nonempty (D.GlobalNormalizedBlowupFactorization (ObjectProperty.homMk M.obj.hom :
        (⟨M.obj.left, M.property.1⟩ : AlgebraicSpaces B S hS) ⟶ D.space)) := by
  obtain ⟨B, hS⟩ := BigFppfSite.exists_contains (Spec (.of R.{u}))
  have hnn : ∀ i, ¬ Space.IsNormal B _ hS ((neighborhoods B hS).neighborhoodSpace i).obj :=
    fun i => not_isNormal_of_isEtale B hS ((neighborhoods B hS).neighborhood i).toSpace
      ((neighborhoods B hS).neighborhood i).etale_toSpace ((neighborhoods B hS).neighborhoodPoint i)
  obtain ⟨M, N, e, hl, hg⟩ := exists_counterexample_of (neighborhoods B hS)
    (hasLocallyFiniteIrreducibleComponents_space B hS)
    (hasEtaleLocalProperty_isLocallyNoetherian_space B hS) (mem_range_point B hS) hnn 0 1
    (by decide)
  exact ⟨B, _, hS, neighborhoods B hS, hasLocallyFiniteIrreducibleComponents_space B hS, M, N, e,
    hl, hg⟩

/-- **Stacks 0BHL is false as published.** The source asserts, for every scheme `S`, every
decent algebraic space `X` over `S` satisfying the equivalent conditions of Stacks 0BB1, every
choice of pairwise distinct closed points `x₁, …, xₙ` and elementary étale neighbourhoods
`(Uᵢ, uᵢ) ⟶ (X, xᵢ)` as in Stacks 0BHA, and every `f : Y ⟶ X` corresponding to `gᵢ : Yᵢ ⟶ Uᵢ`
under the functor `F` of Stacks 0BHA, that `f` is a sequence of normalized blowings up at closed
points over `{x₁, …, xₙ}` if and only if each `gᵢ` is one at closed points over `uᵢ`. This is
the negation of that assertion, with exactly its hypotheses; `exists_counterexample` is a
counterexample to the "if" direction.

The statement holds once `X` is normal: this is `nonempty_globalNormalizedBlowupFactorization_iff`
in the namespace `AlgebraicGeometry.Space.ClosedPointNeighborhoods`. -/
@[stacks 0BHL "refutation of the published statement: false without X normal; at X = Spec(Z/36Z), \
two closed points with non-reduced local rings, g₁ the normalized blowing up of U₁ at u₁ and \
g₂ = id are sequences of normalized blowings up, but the f corresponding to them is not, a \
nonempty sequence having a normal source and the empty one being an isomorphism"]
theorem not_stacks0BHL :
    ¬ ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (n : ℕ)
      (D : ClosedPointNeighborhoods B S hS n)
      (_ : HasLocallyFiniteIrreducibleComponents B S hS D.space.obj)
      (M : D.modificationsAwayFromPoints) (N : ∀ i, D.modificationsAt i)
      (_ : D.restrictionFunctor.obj M ≅ N),
      Nonempty (D.GlobalNormalizedBlowupFactorization (ObjectProperty.homMk M.obj.hom :
          (⟨M.obj.left, M.property.1⟩ : AlgebraicSpaces B S hS) ⟶ D.space)) ↔
        ∀ i, Nonempty (D.LocalNormalizedBlowupFactorization i
          (ObjectProperty.homMk (N i).obj.hom :
            (⟨(N i).obj.left, (N i).property.1⟩ : AlgebraicSpaces B S hS) ⟶
              D.neighborhoodSpace i)) := by
  intro h
  obtain ⟨B, S, hS, D, hXfin, M, N, e, hl, hg⟩ := exists_counterexample.{u}
  exact hg ((h B S hS 2 D hXfin M N e).2 hl)

end Stacks.Examples.NormalizedBlowupsNotEtaleLocal

end
