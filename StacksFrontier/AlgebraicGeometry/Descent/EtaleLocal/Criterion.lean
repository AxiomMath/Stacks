module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Defs
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.Precomposition
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.BaseChange
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.EtaleUnramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.EtaleUniversallyBounded
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFiniteUniversallyBounded
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBounded
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Diagonal

/-!
# Étale locality on the source and target from separate localities

A property of morphisms of schemes that is étale local on the source, étale local on the
target, and preserved by postcomposition with open immersions, is étale local on the source
and target in the sense of `AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget`.

## Main results

* `AlgebraicGeometry.isEtaleLocalOnSourceAndTarget_of_isLocalAtSource_isLocalAtTarget`:
  the combined locality criterion.
* `AlgebraicGeometry.etale_boundsFiberDegrees_fieldFibers`: a bound on the fibre degrees of an
  étale morphism bounds the number of points of each of its base changes to a field.
* `AlgebraicGeometry.etale_bounds_zero_source_isEmpty`: an étale morphism whose fibre degrees are
  bounded by zero has empty source.

## Implementation notes

Separate locality is expressed using Mathlib's source and target locality classes for the
étale precoverage. Stability under postcomposition with an open immersion is expressed by
`CategoryTheory.MorphismProperty.RespectsRight`.

## References

* [Stacks Project, Tag 04R2](https://stacks.math.columbia.edu/tag/04R2)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

universe u

/-- Postcomposition with a universally injective étale morphism preserves a property that is
stable under postcomposition with open immersions. -/
private theorem postcomp_universallyInjective_etale
    (P : MorphismProperty Scheme.{u})
    [P.RespectsRight (@IsOpenImmersion : MorphismProperty Scheme.{u})]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (hf : P f) (g : Y ⟶ Z)
    [Etale g] [UniversallyInjective g] : P (f ≫ g) :=
  ‹P.RespectsRight (@IsOpenImmersion : MorphismProperty Scheme.{u})›.postcomp g
    (isOpenImmersion_of_etale_universallyInjective g) f hf

/-- An étale morphism out of an affine scheme has universally bounded fibres. -/
private theorem etale_affine_hasUniversallyBoundedFibers
    {Y Z : Scheme.{u}} (g : Y ⟶ Z) [IsAffine Y] [Etale g] :
    HasUniversallyBoundedFibers g := by
  have : LocallyQuasiFinite g := ⟨fun {U} hU {V} hV e => by
    let φ := g.appLE U V e
    algebraize [φ.hom]
    have : Algebra.Etale _ _ := (g.etale_appLE hU hV e).toAlgebra
    have : Algebra.EssFiniteType Γ(Z, U) Γ(Y, V) := .of_finiteType _ _
    show Algebra.QuasiFinite _ _
    infer_instance⟩
  exact hasUniversallyBoundedFibers_of_locallyQuasiFinite g

/-- An étale morphism out of an affine scheme admits a natural number bounding its fibre
degrees. -/
private theorem etale_affine_exists_nat_bound
    {Y Z : Scheme.{u}} (g : Y ⟶ Z) [IsAffine Y] [Etale g] :
    ∃ n : ℕ, BoundsFiberDegrees g (n : ℤ) := by
  obtain ⟨N, hN⟩ := etale_affine_hasUniversallyBoundedFibers g
  refine ⟨N.toNat, fun z => ?_⟩
  obtain ⟨r, hr, hrank⟩ := hN z
  exact ⟨r, hr.trans N.self_le_toNat, hrank⟩

/-- A bound on the fibre degrees of an étale morphism bounds the number of points of every
base change to a field. -/
theorem etale_boundsFiberDegrees_fieldFibers
    {Y Z : Scheme.{u}} (g : Y ⟶ Z) [Etale g] (n : ℕ)
    (h : BoundsFiberDegrees g (n : ℤ)) :
    ∀ (K : Type u) [Field K] (z : Spec (.of K) ⟶ Z),
      Cardinal.mk (Limits.pullback z g : Scheme.{u}) ≤ n :=
  ((etale_boundsFiberDegrees_tfae g n).out 1 2).mp h

/-- An étale morphism whose fibre degrees are bounded by zero has empty source. -/
theorem etale_bounds_zero_source_isEmpty
    {Y Z : Scheme.{u}} (g : Y ⟶ Z) [Etale g]
    (h : BoundsFiberDegrees g (0 : ℤ)) : IsEmpty Y := by
  classical
  refine ⟨fun y => ?_⟩
  let K := Y.residueField y
  let z : Spec (.of K) ⟶ Z := Y.fromSpecResidueField y ≫ g
  have hcard := etale_boundsFiberDegrees_fieldFibers g 0 h K z
  have hne : Nonempty (Limits.pullback z g : Scheme.{u}) := by
    let φ : Spec (.of K) ⟶ (Limits.pullback z g : Scheme.{u}) :=
      Limits.pullback.lift (𝟙 _) (Y.fromSpecResidueField y) (by simp [z])
    exact ⟨φ (IsLocalRing.closedPoint K)⟩
  exact not_le_of_gt (pos_iff_ne_zero.mpr (Cardinal.mk_ne_zero _)) hcard

/-- The image of the diagonal of an étale morphism between affine schemes is clopen. -/
private theorem etale_diagonal_range_isClopen
    {Y Z : Scheme.{u}} (g : Y ⟶ Z) [IsAffine Y] [IsAffine Z] [Etale g] :
    IsClopen (Set.range (Limits.pullback.diagonal g).base) := by
  have : Unramified g := unramified_of_etale g
  have : IsOpenImmersion (Limits.pullback.diagonal g) :=
    Unramified.isOpenImmersion_diagonal g
  constructor
  · exact (inferInstance : IsClosedImmersion (Limits.pullback.diagonal g))
      |>.isClosedEmbedding.isClosed_range
  · exact IsOpenImmersion.isOpen_range (Limits.pullback.diagonal g)

/-- The complement of a clopen image inside an affine scheme is an affine open. -/
private theorem clopen_range_complement_isAffine
    {S T : Scheme.{u}} [IsAffine T] (d : S ⟶ T)
    (hd : IsClopen (Set.range d.base)) :
    ∃ U : T.Opens, (U : Set T) = (Set.range d.base)ᶜ ∧ IsAffine U.toScheme := by
  let U : T.Opens := ⟨(Set.range d.base)ᶜ, hd.1.isOpen_compl⟩
  refine ⟨U, rfl, ?_⟩
  have : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion U.ι (by simpa [U] using hd.2.isClosed_compl)
  exact AlgebraicGeometry.isAffine_of_isAffineHom U.ι

/-- The complement of the diagonal image inside the fibre square of an étale morphism between
affine schemes is an affine open. -/
private theorem etale_diagonal_complement_isAffine
    {Y Z : Scheme.{u}} (g : Y ⟶ Z) [IsAffine Y] [IsAffine Z] [Etale g] :
    ∃ U : (Limits.pullback.diagonalObj (C := Scheme) g).Opens,
      U.1 =
        (Set.range (Limits.pullback.diagonal g).base)ᶜ ∧ IsAffine U.toScheme :=
  clopen_range_complement_isAffine (Limits.pullback.diagonal g) (etale_diagonal_range_isClopen g)

/-- Removing the unique point satisfying a subsingleton predicate from a finite type drops the
cardinality bound by one. -/
private theorem card_compl_singleton_le {α : Type u} [Fintype α]
    (p : α → Prop) [DecidablePred p] [Subsingleton {x // p x}]
    (hp : ∃ x, p x) (n : ℕ) (hn : Fintype.card α ≤ n) :
    Fintype.card {x // ¬ p x} ≤ n - 1 := by
  obtain ⟨x, hx⟩ := hp
  have : Fintype.card {x // p x} = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨⟨x, hx⟩, fun _ => Subsingleton.elim _ _⟩
  have := Fintype.card_subtype_compl p
  omega

/-- For an étale morphism between affine schemes with fibre degrees bounded by `n`, the
complement of the diagonal image in the fibre square is affine and the restriction of the
second projection to it has fibre degrees bounded by `n - 1`. -/
private theorem etale_diagonal_complement_bounds
    {Y Z : Scheme.{u}} (g : Y ⟶ Z) [IsAffine Y] [IsAffine Z] [Etale g]
    (n : ℕ) (h : BoundsFiberDegrees g (n : ℤ)) :
    ∃ U : (Limits.pullback.diagonalObj g).Opens,
      U.1 = (Set.range (Limits.pullback.diagonal g).base)ᶜ ∧ IsAffine U.toScheme ∧
      BoundsFiberDegrees (U.ι ≫ Limits.pullback.snd g g) ((n - 1 : ℕ) : ℤ) := by
  classical
  obtain ⟨U, hU, hUA⟩ := etale_diagonal_complement_isAffine g
  let d : Y ⟶ Limits.pullback g g := Limits.pullback.diagonal g
  let p := Limits.pullback.snd g g
  let q : U.toScheme ⟶ Y := U.ι ≫ p
  have : Etale p := inferInstance
  have : Etale q := inferInstance
  have hp : BoundsFiberDegrees p (n : ℤ) := by
    have : MorphismProperty.IsStableUnderBaseChange
        (fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ BoundsFiberDegrees f (n : ℤ)) :=
      boundsFiberDegrees_isStableUnderBaseChange (n : ℤ)
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ BoundsFiberDegrees f (n : ℤ))
      (IsPullback.of_hasPullback g g) h
  have hqfield : ∀ (K : Type u) [Field K] (z : Spec (.of K) ⟶ Y),
      Cardinal.mk (Limits.pullback z q : Scheme.{u}) ≤ (n - 1 : ℕ) := by
    intro K hK z
    let F := (Limits.pullback z p : Scheme.{u})
    let F' := (Limits.pullback z q : Scheme.{u})
    let e := pullbackLeftPullbackSndIso z p U.ι
    let j : F' ⟶ F := e.inv ≫ Limits.pullback.fst (Limits.pullback.snd z p) U.ι
    have hj : IsOpenImmersion j := IsOpenImmersion.comp _ _
    let x₀ : F := Limits.pullback.lift (𝟙 _) (z ≫ d) (by simp [d, p])
      (IsLocalRing.closedPoint K)
    have hFp := etale_boundsFiberDegrees_fieldFibers p n hp K z
    let p₀ : F → Prop := fun x => x = x₀
    have hp₀ : ∃ x, p₀ x := ⟨x₀, rfl⟩
    have hsub : Subsingleton {x : F // p₀ x} := ⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩
    have hne : ∀ x : F', j.base x ≠ x₀ := by
      intro x hx
      have heq : U.ι.base (Limits.pullback.snd z q x) =
          d.base (z.base (IsLocalRing.closedPoint K)) := by
        have hjcoord : j ≫ Limits.pullback.snd z p =
            Limits.pullback.snd z q ≫ U.ι := by
          dsimp [j, e]
          rw [Category.assoc, Limits.pullback.condition, ← Category.assoc,
            pullbackLeftPullbackSndIso_inv_snd_snd]
        calc
          U.ι.base (Limits.pullback.snd z q x) =
              (Limits.pullback.snd z q ≫ U.ι).base x := by simp [Scheme.Hom.comp_base]
          _ = (j ≫ Limits.pullback.snd z p).base x := by rw [hjcoord]
          _ = (Limits.pullback.snd z p).base x₀ := by
                simp [Scheme.Hom.comp_base, hx]
          _ = d.base (z.base (IsLocalRing.closedPoint K)) := by
                have hlift :
                    Limits.pullback.lift (𝟙 _) (z ≫ d) (by simp [d, p]) ≫
                      Limits.pullback.snd z p = z ≫ d :=
                  Limits.pullback.lift_snd (𝟙 _) (z ≫ d) (by simp [d, p])
                show (Limits.pullback.snd z p)
                    ((Limits.pullback.lift (𝟙 _) (z ≫ d) (by simp [d, p]))
                      (IsLocalRing.closedPoint K)) = _
                exact congrArg (fun t : Spec (.of K) ⟶ Limits.pullback g g =>
                  t (IsLocalRing.closedPoint K)) hlift
      have hcompl : U.ι.base (Limits.pullback.snd z q x) ∉ Set.range d.base := by
        rw [← Set.mem_compl_iff, ← hU]
        exact (Limits.pullback.snd z q x).property
      exact hcompl (heq ▸ Set.mem_range_self _)
    have : Finite F := Cardinal.lt_aleph0_iff_finite.mp (hFp.trans_lt Cardinal.natCast_lt_aleph0)
    let : Fintype F := Fintype.ofFinite F
    have hcard : Fintype.card F ≤ n := by
      simpa using hFp
    have hcompl := card_compl_singleton_le p₀ hp₀ n hcard
    let e : F' → {x : F // ¬ p₀ x} := fun x => ⟨j.base x, hne x⟩
    have hle : Cardinal.mk F' ≤ Cardinal.mk {x : F // ¬ p₀ x} :=
      Cardinal.mk_le_of_injective (f := e) fun x y hxy =>
        j.isOpenEmbedding.injective (congrArg Subtype.val hxy)
    have hle' : Cardinal.mk F' ≤ Fintype.card {x : F // ¬ p₀ x} := by
      simpa using hle
    exact hle'.trans (by exact_mod_cast hcompl)
  have hq : BoundsFiberDegrees q ((n - 1 : ℕ) : ℤ) :=
    (etale_boundsFiberDegrees_tfae q (n - 1)).out 2 1 |>.mp hqfield
  exact ⟨U, hU, hUA, hq⟩

/-- An étale morphism between affine schemes with fibre degrees bounded by one is universally
injective. -/
private theorem etale_affine_universallyInjective_of_bound_one
    {Y Z : Scheme.{u}} (g : Y ⟶ Z) [IsAffine Y] [IsAffine Z] [Etale g]
    (h : BoundsFiberDegrees g (1 : ℤ)) : UniversallyInjective g := by
  obtain ⟨U, hU, hUA, hq⟩ := etale_diagonal_complement_bounds g 1 (by simpa using h)
  have hEmpty : IsEmpty U.toScheme := etale_bounds_zero_source_isEmpty _ (by simpa using hq)
  refine (UniversallyInjective.iff_diagonal g).2 ⟨fun x => ?_⟩
  by_contra hx
  have hxU : x ∈ U.1 := by
    rw [hU]
    simpa using hx
  exact hEmpty.false ⟨x, hxU⟩

/-- A property étale local on the target can be checked after base change along a surjective
étale morphism. -/
private theorem of_baseChange_along_surjective_etale
    (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtTarget Scheme.etalePrecoverage]
    {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [Etale g] [Surjective g]
    (h : P (Limits.pullback.snd f g)) : P f := by
  classical
  let 𝒰 : Z.Cover Scheme.etalePrecoverage :=
    Scheme.Cover.mkOfCovers Z (fun _ : Z => Y) (fun _ => g)
      (fun z => by
        obtain ⟨y, hy⟩ := g.surjective z
        exact ⟨z, y, hy⟩)
      (fun _ => inferInstance)
  exact (‹P.IsLocalAtTarget Scheme.etalePrecoverage›).of_zeroHypercover
    (f := f) 𝒰 (fun _ => h)

/-- A property étale local on the source holds for every morphism out of an empty scheme. -/
private theorem property_of_empty_source
    (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.etalePrecoverage]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsEmpty X] : P f := by
  let 𝒰 : X.Cover Scheme.etalePrecoverage :=
    Scheme.Cover.mkOfCovers (Empty : Type) (fun i => isEmptyElim i)
      (fun i => isEmptyElim i) (fun x => isEmptyElim x)
      (fun i => isEmptyElim i)
  have hindex : IsEmpty 𝒰.I₀ := by
    dsimp [𝒰, Scheme.Cover.mkOfCovers]
    infer_instance
  exact (‹P.IsLocalAtSource Scheme.etalePrecoverage›).of_zeroHypercover
    (f := f) 𝒰 (fun i => False.elim (hindex.false i))

/-- A Zariski covering is an étale covering. -/
private def etaleCoverOfZariskiCover {T : Scheme.{u}}
    (𝒰 : T.Cover Scheme.zariskiPrecoverage) :
    T.Cover Scheme.etalePrecoverage :=
  𝒰.changeProp (fun i => by infer_instance)

/-- A property respecting isomorphisms transfers along `e.hom ≫ f = g`. -/
private theorem property_of_iso_hom_comp_eq
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {A B C : Scheme.{u}} (e : A ≅ B) (f : B ⟶ C) (g : A ⟶ C) (h : e.hom ≫ f = g) (hg : P g) :
    P f :=
  (MorphismProperty.cancel_left_of_respectsIso P e.hom f).mp (h ▸ hg)

/-- An étale morphism factors as a surjective étale morphism followed by the inclusion of an
open subscheme. -/
private theorem exists_surjective_etale_comp_ι_eq
    {Y Z : Scheme.{u}} (g : Y ⟶ Z) [Etale g] :
    ∃ (O : Z.Opens) (gO : Y ⟶ O.toScheme), Etale gO ∧ Surjective gO ∧ gO ≫ O.ι = g := by
  let O : Z.Opens := ⟨Set.range g.base, g.isOpenMap.isOpen_range⟩
  have hgRange : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ O := fun y _ => ⟨y, rfl⟩
  have hgOι : (Y.topIso.inv ≫ g.resLE O ⊤ hgRange) ≫ O.ι = g := by
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.toIso_inv_ι,
      Category.id_comp]
  refine ⟨O, _, ?_, ⟨fun z => ?_⟩, hgOι⟩
  · have : Etale (g.resLE O ⊤ hgRange) := inferInstance
    infer_instance
  · obtain ⟨y, hy⟩ := z.2
    exact ⟨y, Subtype.ext ((congrArg (fun a : Y ⟶ Z => a y) hgOι).trans hy)⟩

/-- For a property étale local on both source and target separately and stable under
postcomposition with open immersions, postcomposition with an étale morphism between affine
schemes whose fibre degrees are bounded preserves the property. -/
private theorem postcomp_etale_affine_bound
    (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.etalePrecoverage]
    [P.IsLocalAtTarget Scheme.etalePrecoverage]
    [P.RespectsRight (@IsOpenImmersion : MorphismProperty Scheme.{u})]
    {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (f : X ⟶ Y) (hf : P f) (g : Y ⟶ Z) [Etale g]
    (n : ℕ) (hn : BoundsFiberDegrees g (n : ℤ)) : P (f ≫ g) := by
  induction n using Nat.strong_induction_on generalizing X Y Z f g with
  | h n ih =>
    obtain rfl | rfl | hn2 : n = 0 ∨ n = 1 ∨ 2 ≤ n := by omega
    · have hEmpty : IsEmpty Y := etale_bounds_zero_source_isEmpty g (by simpa using hn)
      have : IsEmpty X := ⟨fun x => hEmpty.false (f x)⟩
      exact property_of_empty_source P (f ≫ g)
    · have : UniversallyInjective g :=
        etale_affine_universallyInjective_of_bound_one g (by simpa using hn)
      exact postcomp_universallyInjective_etale P f hf g
    let T := Limits.pullback g g
    let p₁ : T ⟶ Y := Limits.pullback.fst g g
    let p₂ : T ⟶ Y := Limits.pullback.snd g g
    let d : Y ⟶ T := Limits.pullback.diagonal g
    have : Etale p₁ := inferInstance
    have : Unramified g := unramified_of_etale g
    have : IsOpenImmersion d := Unramified.isOpenImmersion_diagonal g
    obtain ⟨U, hU, hUA, hq⟩ := etale_diagonal_complement_bounds g n hn
    let q : U.toScheme ⟶ Y := U.ι ≫ p₂
    have hqbound : BoundsFiberDegrees q ((n - 1 : ℕ) : ℤ) := hq
    have : Etale q := inferInstance
    let B := Limits.pullback f p₁
    let k : B ⟶ T := Limits.pullback.snd f p₁
    have hk : P k := pullbackSnd_of_etale P f p₁ hf inferInstance
    let V : T.Cover Scheme.zariskiPrecoverage :=
      Scheme.Cover.mkOfCovers Bool
        (fun b => match b with | false => Y | true => U.toScheme)
        (fun b => match b with | false => d | true => U.ι)
        (fun t => by
          by_cases ht : t ∈ Set.range d.base
          · obtain ⟨y, hy⟩ := ht
            exact ⟨false, y, hy⟩
          · have htu : t ∈ U.1 := by
              rw [hU]
              simpa using ht
            exact ⟨true, ⟨t, htu⟩, rfl⟩)
        (fun b => by cases b <;> infer_instance)
    have hsplit : P (k ≫ p₂) := by
      let W := etaleCoverOfZariskiCover (V.pullback₁ k)
      refine (‹P.IsLocalAtSource Scheme.etalePrecoverage›).of_zeroHypercover
        (f := k ≫ p₂) W fun b => ?_
      cases b
      · let e := pullbackLeftPullbackSndIso f p₁ d
        have he : P (e.hom ≫ Limits.pullback.snd f (d ≫ p₁)) :=
          precomp_of_etale P e.hom _ inferInstance
            (pullbackSnd_of_etale P f (d ≫ p₁) hf inferInstance)
        have heq : e.hom ≫ Limits.pullback.snd f (d ≫ p₁) = Limits.pullback.snd k d :=
          pullbackLeftPullbackSndIso_hom_snd f p₁ d
        have hcomp : W.f false ≫ (k ≫ p₂) = Limits.pullback.snd k d := by
          show Limits.pullback.fst k d ≫ k ≫ p₂ = _
          rw [Limits.pullback.condition_assoc]
          simp [d, p₂]
        rw [hcomp, ← heq]
        exact he
      · let c := Limits.pullback.snd k U.ι
        have : IsAffine U.toScheme := hUA
        have hcomp : W.f true ≫ (k ≫ p₂) = c ≫ q := by
          show Limits.pullback.fst k U.ι ≫ k ≫ p₂ = c ≫ q
          exact Limits.pullback.condition_assoc p₂
        rw [hcomp]
        exact ih (n - 1) (by omega) c (pullbackSnd_of_etale P k U.ι hk inferInstance) q hqbound
    let r : X ⟶ Z := f ≫ g
    have hpull : P (Limits.pullback.snd r g) :=
      property_of_iso_hom_comp_eq P _ _ _ (pullbackRightPullbackFstIso_hom_snd g g f) hsplit
    obtain ⟨O, gO, _, _, hgOι⟩ := exists_surjective_etale_comp_ι_eq g
    let rO : X ⟶ O.toScheme := f ≫ gO
    have hrOι : rO ≫ O.ι = r := by rw [Category.assoc, hgOι]
    have hpullO : P (Limits.pullback.snd rO gO) := by
      have h : IsPullback (Limits.pullback.fst rO gO) (Limits.pullback.snd rO gO) r g :=
        hrOι ▸ hgOι ▸ IsPullback.of_isLimit (pullbackIsPullbackOfCompMono rO gO O.ι)
      exact property_of_iso_hom_comp_eq P (h.isoIsPullback _ _ (.of_hasPullback r g)).symm _ _
        (by simp) hpull
    have hr : P (rO ≫ O.ι) :=
      ‹P.RespectsRight (@IsOpenImmersion : MorphismProperty Scheme.{u})›.postcomp O.ι
        (by infer_instance) rO (of_baseChange_along_surjective_etale P rO gO hpullO)
    simpa [hrOι] using hr

/-- For a property étale local on each of source and target separately and stable under
postcomposition with open immersions, postcomposition with an arbitrary étale morphism
preserves the property. -/
private theorem postcomp_etale_general
    (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.etalePrecoverage]
    [P.IsLocalAtTarget Scheme.etalePrecoverage]
    [P.RespectsRight (@IsOpenImmersion : MorphismProperty Scheme.{u})]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (hf : P f) (g : Y ⟶ Z) [Etale g] :
    P (f ≫ g) := by
  classical
  obtain ⟨O, gO, _, _, hgOι⟩ := exists_surjective_etale_comp_ι_eq g
  let rO : X ⟶ O.toScheme := f ≫ gO
  let 𝒵 := etaleCoverOfZariskiCover (O.toScheme.affineCover)
  have hlocal : P rO := by
    apply (‹P.IsLocalAtTarget Scheme.etalePrecoverage›).of_zeroHypercover
      (f := rO) 𝒵
    intro i
    let Zi := (O.toScheme.affineCover).X i
    let b := (O.toScheme.affineCover).f i
    have : IsOpenImmersion b := (O.toScheme.affineCover).map_prop i
    have : Etale b := inferInstance
    let Q := Limits.pullback gO b
    let qY := Limits.pullback.fst gO b
    let qO := Limits.pullback.snd gO b
    let C := Limits.pullback f qY
    let cQ := Limits.pullback.snd f qY
    let s : C ⟶ Zi := cQ ≫ qO
    have : Etale qY := inferInstance
    have : Etale qO := inferInstance
    have hcQ : P cQ := pullbackSnd_of_etale P f qY hf inferInstance
    let Qcover := Q.affineCover
    let W := etaleCoverOfZariskiCover (Qcover.pullback₁ cQ)
    have hs : P s := by
      refine (‹P.IsLocalAtSource Scheme.etalePrecoverage›).of_zeroHypercover
        (f := s) W ?_
      intro j
      let Vj := Qcover.X j
      let v := Qcover.f j
      have : IsOpenImmersion v := Qcover.map_prop j
      have : Etale v := inferInstance
      let m : Vj ⟶ Zi := v ≫ qO
      let Cj := Limits.pullback cQ v
      let aC := Limits.pullback.fst cQ v
      let aQ := Limits.pullback.snd cQ v
      have haQ : P aQ := pullbackSnd_of_etale P cQ v hcQ inferInstance
      have : IsAffine Zi := Scheme.isAffine_affineCover O.toScheme i
      have : IsAffine Vj := Scheme.isAffine_affineCover Q j
      have : Etale m := by
        dsimp [m]
        infer_instance
      have hCj : P (aQ ≫ m) := by
        let Acover := etaleCoverOfZariskiCover Cj.affineCover
        refine (‹P.IsLocalAtSource Scheme.etalePrecoverage›).of_zeroHypercover
          (f := aQ ≫ m) Acover ?_
        intro k
        let A := Cj.affineCover.X k
        let a := Cj.affineCover.f k
        have : IsOpenImmersion a := Cj.affineCover.map_prop k
        have : Etale a := inferInstance
        have : IsAffine A := Scheme.isAffine_affineCover Cj k
        have hA : P (a ≫ aQ) := precomp_of_etale P a aQ inferInstance haQ
        obtain ⟨n, hn⟩ := etale_affine_exists_nat_bound m
        exact postcomp_etale_affine_bound P (a ≫ aQ) hA m n hn
      have hcomp : W.f j ≫ s = aQ ≫ m := by
        show aC ≫ cQ ≫ qO = aQ ≫ v ≫ qO
        exact Limits.pullback.condition_assoc qO
      rw [hcomp]
      exact hCj
    exact property_of_iso_hom_comp_eq P _ _ _ (pullbackRightPullbackFstIso_hom_snd gO b f) hs
  have hfinal : P (rO ≫ O.ι) :=
    ‹P.RespectsRight (@IsOpenImmersion : MorphismProperty Scheme.{u})›.postcomp O.ι
      (by infer_instance) rO hlocal
  simpa [rO, Category.assoc, hgOι] using hfinal

/-- A morphism property that is étale local on each of the source and target separately,
and is preserved by postcomposition with open immersions, is étale local on the source
and target together. -/
@[stacks 04R2]
theorem isEtaleLocalOnSourceAndTarget_of_isLocalAtSource_isLocalAtTarget
    (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.etalePrecoverage]
    [P.IsLocalAtTarget Scheme.etalePrecoverage]
    [P.RespectsRight (@IsOpenImmersion : MorphismProperty Scheme.{u})] :
    IsEtaleLocalOnSourceAndTarget P :=
  { precomp := ⟨fun {X Y Z} a ha f hf => precomp_of_etale P a f ha hf⟩
    pullbackSnd_of_etale := fun f hf g hg =>
      AlgebraicGeometry.pullbackSnd_of_etale P f g hf hg
    iff_forall_exists_etale_neighborhood := by
      intro X Y f
      constructor
      · intro hf x
        exact ⟨X, Y, 𝟙 X, 𝟙 Y, f, x, inferInstance, inferInstance, by simp,
          by simp, hf⟩
      · intro h
        classical
        choose U V a b k u ha hb hu hcomm hP using h
        let 𝒰 : X.Cover Scheme.etalePrecoverage :=
          Scheme.Cover.mkOfCovers X U a (fun x => ⟨x, u x, hu x⟩) ha
        exact (‹P.IsLocalAtSource Scheme.etalePrecoverage›).of_zeroHypercover
          (f := f) 𝒰 (fun x => by
            have hk : P (k x) := hP x
            have : Etale (b x) := hb x
            have hkb : P (k x ≫ b x) := postcomp_etale_general P (k x) hk (b x)
            show P (a x ≫ f)
            rw [← hcomm x]
            exact hkb) }

end AlgebraicGeometry
