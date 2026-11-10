module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.EtaleSmoothFromLocality.RelativeProperty

/-!
# Étale-smooth locality from locality hypotheses: étale postcomposition

Fibre bounds for étale morphisms and the complement of the diagonal (Stacks 03J4, Stacks 03WU),
and the stability of the induced property of morphisms of schemes over `S` under postcomposition
with an étale morphism over `S`, with its consequences for the largest open locus.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace AlgebraicGeometry

attribute [local instance] bounded_open
attribute [local instance] bounded_pullback
attribute [local instance] bounded_affineSpace
attribute [local instance] pullbackCanonicallyOverRight
attribute [local instance] pullbackSnd_isOver
attribute [local instance] pullbackFst_isOver
attribute [local instance] pullbackLift_isOver
attribute [local instance] affineCoverCanonicallyOver
attribute [local instance] affineCoverMap_isOver
attribute [local instance] bounded_affineCover

section EtaleGeometry

open CategoryTheory.Limits

/-- An étale morphism with quasi-compact source has universally bounded fibres. -/
private theorem etale_compact_hasUniversallyBoundedFibers
    {Y Z : Scheme.{u}} (g : Y ⟶ Z) [CompactSpace Y] [Etale g] :
    HasUniversallyBoundedFibers g := by
  have : LocallyQuasiFinite g := {
    quasiFinite_appLE := by
      intro U hU V hV e
      let φ := g.appLE U V e
      algebraize [φ.hom]
      have hφ : φ.hom.Etale := g.etale_appLE hU hV e
      have : Algebra.Etale _ _ := hφ.toAlgebra
      have : Algebra.EssFiniteType (Γ(Z, U)) (Γ(Y, V)) :=
        Algebra.EssFiniteType.of_finiteType (Γ(Z, U)) (Γ(Y, V))
      change Algebra.QuasiFinite _ _
      infer_instance
  }
  exact hasUniversallyBoundedFibers_of_locallyQuasiFinite_of_compactSpace g

/-- A morphism with universally bounded fibres admits a natural number bounding its fibre
degrees. -/
private theorem exists_nat_bound_of_universallyBoundedFibers
    {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (h : HasUniversallyBoundedFibers g) :
    ∃ n : ℕ, BoundsFiberDegrees g (n : ℤ) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N.toNat, fun z => ?_⟩
  obtain ⟨r, hr, hrank⟩ := hN z
  exact ⟨r, hr.trans (by omega), hrank⟩

/-- The image of the diagonal of a separated unramified morphism is open and closed. -/
private theorem unramified_diagonal_range_isClopen
    {Y Z : Scheme.{u}} (g : Y ⟶ Z) [IsSeparated g] [Unramified g] :
    IsClopen (Set.range (Limits.pullback.diagonal g).base) := by
  constructor
  · exact (inferInstance : IsClosedImmersion (Limits.pullback.diagonal g))
      |>.isClosedEmbedding.isClosed_range
  · exact IsOpenImmersion.isOpen_range (Limits.pullback.diagonal g)

/-- The complement of a clopen subset of an affine scheme is an affine open subscheme. -/
private theorem clopen_complement_isAffine
    {T : Scheme.{u}} [IsAffine T] (S : Set T) (hd : IsClopen S) :
    ∃ U : T.Opens, (U : Set T) = Sᶜ ∧ IsAffine U.toScheme := by
  let U : T.Opens := ⟨Sᶜ, hd.1.isOpen_compl⟩
  refine ⟨U, rfl, ?_⟩
  have : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion U.ι (by simpa [U] using hd.2.isClosed_compl)
  exact AlgebraicGeometry.isAffine_of_isAffineHom U.ι

/-- A predicate on a finite type which holds somewhere has at most one less than the cardinality of
the type as the cardinality of its complement. -/
private theorem card_compl_nonempty_le {α : Type u} [Fintype α]
    (p : α → Prop) [DecidablePred p]
    (hp : ∃ x, p x) (n : ℕ) (hn : Fintype.card α ≤ n) :
    Fintype.card {x // ¬ p x} ≤ n - 1 := by
  classical
  have hcard : 0 < Fintype.card {x // p x} := Fintype.card_pos_iff.mpr
    ⟨⟨Classical.choose hp, Classical.choose_spec hp⟩⟩
  have hcompl := Fintype.card_subtype_compl p
  omega

/-- Over a field-valued point, no point of the fibre of the second projection restricted to the
complement of the diagonal maps to the diagonal point of the full fibre. -/
private lemma pullback_diagonal_compl_fiber_ne
    {Y Z : Scheme.{u}} (g : Y ⟶ Z) (U : (Limits.pullback.diagonalObj g).Opens)
    (hU : U.1 = (Set.range (Limits.pullback.diagonal g).base)ᶜ)
    (K : Type u) [Field K] (z : Spec (.of K) ⟶ Y)
    (x : (Limits.pullback z (U.ι ≫ Limits.pullback.snd g g) : Scheme.{u})) :
    ((pullbackLeftPullbackSndIso z (Limits.pullback.snd g g) U.ι).inv ≫
        Limits.pullback.fst (Limits.pullback.snd z (Limits.pullback.snd g g)) U.ι).base x ≠
      Limits.pullback.lift (f := z) (g := Limits.pullback.snd g g) (𝟙 _)
        (z ≫ Limits.pullback.diagonal g) (by simp) (IsLocalRing.closedPoint K) := by
  let d : Y ⟶ Limits.pullback g g := Limits.pullback.diagonal g
  let p := Limits.pullback.snd g g
  let q : U.toScheme ⟶ Y := U.ι ≫ p
  let F := (Limits.pullback z p : Scheme.{u})
  let e := pullbackLeftPullbackSndIso z p U.ι
  let j : (Limits.pullback z q : Scheme.{u}) ⟶ F :=
    e.inv ≫ Limits.pullback.fst (Limits.pullback.snd z p) U.ι
  let x₀ : F := Limits.pullback.lift (𝟙 _) (z ≫ d) (by simp [d, p])
    (IsLocalRing.closedPoint K)
  intro hx
  change j.base x = x₀ at hx
  have hUmem : U.ι.base (Limits.pullback.snd z q x) ∈ U.1 := by
    change U.ι.base (Limits.pullback.snd z q x) ∈ U
    exact (Limits.pullback.snd z q x).property
  have heq : U.ι.base (Limits.pullback.snd z q x) =
      d.base (z.base (IsLocalRing.closedPoint K)) := by
    have hjcoord : j ≫ Limits.pullback.snd z p =
        Limits.pullback.snd z q ≫ U.ι := by
      dsimp [j]
      calc
        e.inv ≫ Limits.pullback.fst (Limits.pullback.snd z p) U.ι ≫
            Limits.pullback.snd z p =
            e.inv ≫ Limits.pullback.snd (Limits.pullback.snd z p) U.ι ≫ U.ι := by
              rw [Limits.pullback.condition (f := Limits.pullback.snd z p) (g := U.ι)]
        _ = Limits.pullback.snd z q ≫ U.ι := by
              dsimp [e]
              rw [← Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd]
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
            change (Limits.pullback.snd z p)
                ((Limits.pullback.lift (𝟙 _) (z ≫ d) (by simp [d, p]))
                  (IsLocalRing.closedPoint K)) = _
            exact congrArg (fun t : Spec (.of K) ⟶ Limits.pullback g g =>
              t (IsLocalRing.closedPoint K)) hlift
  have hdiag : d.base (z.base (IsLocalRing.closedPoint K)) ∈ Set.range d.base :=
    ⟨z.base (IsLocalRing.closedPoint K), rfl⟩
  have hcompl : U.ι.base (Limits.pullback.snd z q x) ∉ Set.range d.base :=
    (congrArg (fun s : Set _ => U.ι.base (Limits.pullback.snd z q x) ∈ s)
      hU).mp hUmem
  exact hcompl (heq ▸ hdiag)

/-- For a separated étale morphism with affine self-product, the complement of the diagonal is an
affine open whose second projection has fibre degrees bounded by one less. -/
private theorem etale_diagonal_complement_bounds
    {Y Z : Scheme.{u}} (g : Y ⟶ Z) [IsSeparated g]
    [IsAffine (Limits.pullback g g)] [Etale g]
    (n : ℕ) (h : BoundsFiberDegrees g (n : ℤ)) :
    ∃ U : (Limits.pullback.diagonalObj g).Opens,
      U.1 = (Set.range (Limits.pullback.diagonal g).base)ᶜ ∧ IsAffine U.toScheme ∧
      BoundsFiberDegrees (U.ι ≫ Limits.pullback.snd g g) ((n - 1 : ℕ) : ℤ) := by
  classical
  have : Unramified g := unramified_of_etale g
  obtain ⟨U, hU, hUA⟩ := clopen_complement_isAffine
    (Set.range (Limits.pullback.diagonal g).base) (unramified_diagonal_range_isClopen g)
  let d : Y ⟶ Limits.pullback g g := Limits.pullback.diagonal g
  let p := Limits.pullback.snd g g
  let q : U.toScheme ⟶ Y := U.ι ≫ p
  have hp : BoundsFiberDegrees p (n : ℤ) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ BoundsFiberDegrees f (n : ℤ))
      (IsPullback.of_hasPullback g g) h
  have hqfield : ∀ (K : Type u) [Field K] (z : Spec (.of K) ⟶ Y),
      Cardinal.mk (Limits.pullback z q : Scheme.{u}) ≤ (n - 1 : ℕ) := by
    intro K hK z
    let F := (Limits.pullback z p : Scheme.{u})
    let F' := (Limits.pullback z q : Scheme.{u})
    let e := pullbackLeftPullbackSndIso z p U.ι
    let j : F' ⟶ F := e.inv ≫ Limits.pullback.fst (Limits.pullback.snd z p) U.ι
    have hj : IsOpenImmersion j := by
      dsimp [j]
      infer_instance
    let x₀ : F := Limits.pullback.lift (𝟙 _) (z ≫ d) (by simp [d, p])
      (IsLocalRing.closedPoint K)
    have hFp := etale_boundsFiberDegrees_fieldFibers p n hp K z
    let p₀ : F → Prop := fun x => x = x₀
    have hne : ∀ x : F', j.base x ≠ x₀ := pullback_diagonal_compl_fiber_ne g U hU K z
    have : Finite F :=
      Cardinal.lt_aleph0_iff_finite.mp (hFp.trans_lt Cardinal.natCast_lt_aleph0)
    let : Fintype F := Fintype.ofFinite F
    have hcard : Fintype.card F ≤ n := by
      simpa using hFp
    have hcompl := card_compl_nonempty_le p₀ ⟨x₀, rfl⟩ n hcard
    let e : F' → {x : F // ¬ p₀ x} := fun x => ⟨j.base x, hne x⟩
    have he : Function.Injective e := fun x y hxy =>
      j.isOpenEmbedding.injective (congrArg Subtype.val hxy)
    have hle' : Cardinal.mk F' ≤ Fintype.card {x : F // ¬ p₀ x} := by
      simpa using Cardinal.mk_le_of_injective he
    exact hle'.trans (by exact_mod_cast hcompl)
  exact ⟨U, hU, hUA, (etale_boundsFiberDegrees_tfae q (n - 1)).out 2 1 |>.mp hqfield⟩

end EtaleGeometry

/-- A member of an open cover of a scheme of size below the cutoff of the site again has size
below it. -/
theorem bounded_openCover
    (B : BigFppfSite.{u}) {X : Scheme.{u}} [Fact (B.Contains X)]
    (C : X.OpenCover) (i : C.I₀) : Fact (B.Contains (C.X i)) :=
  ⟨Scheme.size_lt_of_isOpenImmersion (C.f i) Fact.out⟩

attribute [local instance] bounded_openCover

/-- The diagonal of a morphism with open diagonal, together with the complement of its image,
covers the fibre product. -/
private noncomputable def diagonalComplementCover {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    [IsOpenImmersion (Limits.pullback.diagonal g)] (U : (Limits.pullback.diagonalObj g).Opens)
    (hU : U.1 = (Set.range (Limits.pullback.diagonal g).base)ᶜ) :
    (Limits.pullback.diagonalObj g).OpenCover :=
  Scheme.Cover.mkOfCovers Bool
    (fun b => match b with | false => Y | true => U.toScheme)
    (fun b => match b with | false => Limits.pullback.diagonal g | true => U.ι)
    (by
      intro t
      by_cases ht : t ∈ Set.range (Limits.pullback.diagonal g).base
      · obtain ⟨y, hy⟩ := ht
        exact ⟨false, y, hy⟩
      · have htu : t ∈ U.1 := by
          rw [hU]
          simpa using ht
        exact ⟨true, ⟨t, htu⟩, rfl⟩)
    (fun b => by cases b <;> infer_instance)

section RelativeEtale

open CategoryTheory.Limits

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (P : MorphismProperty (AlgebraicSpaces B S hS))
  [hsource : P.IsLocalAtSource (Space.Topology.precoverage.{u, u + 1} .etale B S hS)]
  [htarget : P.IsLocalAtTarget (Space.Topology.precoverage.{u, u + 1} .smooth B S hS)]
  [hopen : P.RespectsRight (fun ⦃X Y : AlgebraicSpaces B S hS⦄
    (f : X ⟶ Y) => Space.IsOpenImmersion B S hS f.hom)]

local notation "R" => relativeProperty B S hS P

/-- The induced property of morphisms of schemes over `S` holds for a composite with an étale
morphism over `S` once it holds for the base change of the composite along that morphism. -/
private theorem relative_of_pullback_snd_comp_etale
    {X Y Z : Scheme.{u}} [Y.Over S] [Z.Over S]
    [Fact (B.Contains X)] [Fact (B.Contains Y)] [Fact (B.Contains Z)]
    (f : X ⟶ Y) (g : Y ⟶ Z) [g.IsOver S] [Etale g]
    (hpull : R (pullback.snd (f ≫ g) g)) : R (f ≫ g) := by
  let r : X ⟶ Z := f ≫ g
  replace hpull : R (pullback.snd r g) := hpull
  let O : Z.Opens := ⟨Set.range g.base, g.isOpenMap.isOpen_range⟩
  have hgRange : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ O := fun y _ => ⟨y, rfl⟩
  let gO : Y ⟶ O.toScheme := Y.topIso.inv ≫ g.resLE O ⊤ hgRange
  let rO : X ⟶ O.toScheme := f ≫ gO
  have hgOι : gO ≫ O.ι = g := by
    dsimp [gO]
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
      Scheme.toIso_inv_ι, Category.id_comp]
  have : gO.IsOver S := ⟨by
    change gO ≫ (O.ι ≫ Z ↘ S) = Y ↘ S
    rw [← Category.assoc, hgOι, comp_over]⟩
  have hrOι : rO ≫ O.ι = r := by simp [rO, r, Category.assoc, hgOι]
  have hpb : IsPullback (pullback.fst rO gO) (pullback.snd rO gO) r g := by
    simpa only [PullbackCone.mk, hrOι, hgOι] using
      (IsPullback.of_isLimit (pullbackIsPullbackOfCompMono rO gO O.ι))
  let e : pullback r g ≅ pullback rO gO :=
    (IsPullback.of_hasPullback r g).isoIsPullback _ _ hpb
  have hpullO : R (pullback.snd rO gO) := by
    have heq : e.hom ≫ pullback.snd rO gO = pullback.snd r g :=
      (IsPullback.of_hasPullback r g).isoIsPullback_hom_snd _ _ hpb
    exact (relative_cancel_left_iso B S hS P e.hom _).mp (heq ▸ hpull)
  have : Surjective gO := ⟨by
    intro z
    obtain ⟨y, hy⟩ := z.2
    exact ⟨y, O.ι.isOpenEmbedding.injective
      ((congrArg (fun a : Y ⟶ Z => a y) hgOι).trans hy)⟩⟩
  simpa only [hrOι] using
    relative_postcomp_open B S hS P rO O.ι (relative_of_pullback_snd B S hS P rO gO hpullO)

/-- The induced property of morphisms of schemes over `S` is stable under postcomposition with an
affine étale morphism over `S` whose fibre degrees are bounded. -/
private theorem relative_postcomp_etale_affine_bound
    {X Y Z : Scheme.{u}} [Y.Over S] [Z.Over S]
    [Fact (B.Contains X)] [Fact (B.Contains Y)] [Fact (B.Contains Z)]
    [IsAffine Y] [IsAffine Z]
    (f : X ⟶ Y) (hf : R f) (g : Y ⟶ Z) [g.IsOver S] [Etale g]
    (n : ℕ) (hn : BoundsFiberDegrees g (n : ℤ)) : R (f ≫ g) := by
  induction n using Nat.strong_induction_on generalizing X Y Z f g with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      have hEmpty : IsEmpty Y := etale_bounds_zero_source_isEmpty g (by simpa using hn)
      have : IsEmpty X := ⟨fun x => hEmpty.false (f x)⟩
      exact relative_of_empty_source B S hS P (f ≫ g)
    · let T := pullback g g
      let p₁ : T ⟶ Y := pullback.fst g g
      let p₂ : T ⟶ Y := pullback.snd g g
      let d : Y ⟶ T := pullback.diagonal g
      have : d.IsOver S := ⟨by
        change d ≫ (p₂ ≫ Y ↘ S) = Y ↘ S
        rw [← Category.assoc, show d ≫ p₂ = 𝟙 Y from pullback.diagonal_snd g,
          Category.id_comp]⟩
      obtain ⟨U, hU, hUA, hq⟩ := etale_diagonal_complement_bounds g n hn
      let q : U.toScheme ⟶ Y := U.ι ≫ p₂
      let D := pullback f p₁
      let k : D ⟶ T := pullback.snd f p₁
      have hk : R k := relative_pullback_snd B S hS P f p₁ hf
      let V : T.OpenCover := diagonalComplementCover g U hU
      have hsplit : R (k ≫ p₂) := by
        let W : D.OpenCover := V.pullback₁ k
        apply relative_of_source_cover B S hS P (k ≫ p₂) W.X W.f
          (fun i => have := W.map_prop i; inferInstance) W.exists_eq
        intro b
        cases b
        · have hcomp : W.f false ≫ (k ≫ p₂) = pullback.snd k d := by
            change (pullback.fst k d ≫ k ≫ p₂) = _
            rw [← Category.assoc, pullback.condition, Category.assoc]
            simp [d, p₂]
          rw [hcomp]
          exact relative_pullback_snd B S hS P k d hk
        · let c := pullback.snd k U.ι
          have hc : R c := relative_pullback_snd B S hS P k U.ι hk
          have : IsAffine U.toScheme := hUA
          have hcomp : W.f true ≫ (k ≫ p₂) = c ≫ q := by
            change (pullback.fst k U.ι ≫ k ≫ p₂) = c ≫ q
            rw [← Category.assoc, pullback.condition, Category.assoc]
          rw [hcomp]
          exact ih (n - 1) (by omega) c hc q hq
      let e := pullbackRightPullbackFstIso g g f
      have heq : e.hom ≫ pullback.snd (f ≫ g) g = k ≫ p₂ := by
        dsimp [e, k, D, p₁, p₂, T]
        rw [pullbackRightPullbackFstIso_hom_snd]
      exact relative_of_pullback_snd_comp_etale B S hS P f g
        ((relative_cancel_left_iso B S hS P e.hom _).mp (heq ▸ hsplit))

end RelativeEtale

section RelativeEtaleGeneral

open CategoryTheory.Limits

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (P : MorphismProperty (AlgebraicSpaces B S hS))
  [hsource : P.IsLocalAtSource (Space.Topology.precoverage.{u, u + 1} .etale B S hS)]
  [htarget : P.IsLocalAtTarget (Space.Topology.precoverage.{u, u + 1} .smooth B S hS)]
  [hopen : P.RespectsRight (fun ⦃X Y : AlgebraicSpaces B S hS⦄
    (f : X ⟶ Y) => Space.IsOpenImmersion B S hS f.hom)]

local notation "R" => relativeProperty B S hS P
local notation "W" => relativeLargestOpen B S hS P

/-- The induced property of morphisms of schemes over `S` is stable under postcomposition with an
étale morphism over `S`. -/
private theorem relative_postcomp_etale
    {X Y Z : Scheme.{u}} [Y.Over S] [Z.Over S]
    [Fact (B.Contains X)] [Fact (B.Contains Y)] [Fact (B.Contains Z)]
    (f : X ⟶ Y) (hf : R f) (g : Y ⟶ Z) [g.IsOver S] [Etale g] : R (f ≫ g) := by
  apply relative_of_target_affineCover B S hS P (f ≫ g)
  intro i
  let Zi := Z.affineCover.X i
  let b := Z.affineCover.f i
  let Q := pullback g b
  let : Q.Over S := inferInstance
  have : Fact (B.Contains Q) := inferInstance
  let qY := pullback.fst g b
  let qO := pullback.snd g b
  let C := pullback f qY
  let cQ := pullback.snd f qY
  let s : C ⟶ Zi := cQ ≫ qO
  have hcQ : R cQ := relative_pullback_snd B S hS P f qY hf
  let 𝒲 : C.OpenCover := Q.affineCover.pullback₁ cQ
  have hs : R s := by
    apply relative_of_source_cover B S hS P s 𝒲.X 𝒲.f
      (fun j => have := 𝒲.map_prop j; inferInstance) 𝒲.exists_eq
    intro j
    let Vj := Q.affineCover.X j
    let v := Q.affineCover.f j
    have : IsOpenImmersion v := Q.affineCover.map_prop j
    let : Vj.Over S := ⟨v ≫ Q ↘ S⟩
    have : v.IsOver S := ⟨rfl⟩
    have : Fact (B.Contains Vj) := ⟨Scheme.size_lt_of_isOpenImmersion v Fact.out⟩
    let m : Vj ⟶ Zi := v ≫ qO
    let aC := pullback.fst cQ v
    let aQ := pullback.snd cQ v
    have haQ : R aQ := relative_pullback_snd B S hS P cQ v hcQ
    have : IsAffine Zi := Scheme.isAffine_affineCover Z i
    have : IsAffine Vj := Scheme.isAffine_affineCover Q j
    have hCj : R (aQ ≫ m) := by
      obtain ⟨n, hn⟩ := exists_nat_bound_of_universallyBoundedFibers
        m (etale_compact_hasUniversallyBoundedFibers m)
      exact relative_postcomp_etale_affine_bound B S hS P aQ haQ m n hn
    have hcomp : 𝒲.f j ≫ s = aQ ≫ m := by
      change aC ≫ cQ ≫ qO = aQ ≫ v ≫ qO
      rw [← Category.assoc, pullback.condition, Category.assoc]
    rwa [hcomp]
  let e := pullbackRightPullbackFstIso g b f
  have heq : e.hom ≫ pullback.snd (f ≫ g) b = s := by
    dsimp [e, s, cQ, qO, Q, qY, C]
    rw [pullbackRightPullbackFstIso_hom_snd]
  exact (relative_cancel_left_iso B S hS P e.hom _).mp (heq ▸ hs)

omit hopen in
/-- An étale postcomposition over `S` may be cancelled from the induced property of morphisms of
schemes over `S`. -/
private theorem relative_cancel_postcomp_etale
    {X Y Z : Scheme.{u}} [Y.Over S] [Z.Over S]
    [Fact (B.Contains X)] [Fact (B.Contains Y)] [Fact (B.Contains Z)]
    (f : X ⟶ Y) (g : Y ⟶ Z) [g.IsOver S] [Etale g]
    (hf : R (f ≫ g)) : R f := by
  let : X.Over S := ⟨f ≫ Y ↘ S⟩
  have : f.IsOver S := ⟨rfl⟩
  rw [relativeProperty_iff B S hS P (f ≫ g)] at hf
  rw [relativeProperty_iff B S hS P f]
  change P ((schemeEmbedding B S hS).map
    (relativeMap B S hS f ≫ relativeMap B S hS g)) at hf
  rw [Functor.map_comp] at hf
  exact of_postcomp_etale B S hS P _ _
    (etale_of_presheaf_etale B S hS _
      (schemeMap_presheaf_property B S hS (@Etale) (relativeMap B S hS g)
        (show Etale g from inferInstance))) hf

/-- Postcomposing with an étale morphism over `S` does not change the largest open locus. -/
private theorem relativeLargestOpen_postcomp_etale
    {X Y Z : Scheme.{u}} [Y.Over S] [Z.Over S]
    [Fact (B.Contains X)] [Fact (B.Contains Y)] [Fact (B.Contains Z)]
    (f : X ⟶ Y) (g : Y ⟶ Z) [g.IsOver S] [Etale g] : W (f ≫ g) = W f := by
  unfold relativeLargestOpen
  congr 1
  ext U
  change R (U.ι ≫ (f ≫ g)) ↔ R (U.ι ≫ f)
  rw [← Category.assoc]
  exact ⟨relative_cancel_postcomp_etale B S hS P _ g,
    fun h => relative_postcomp_etale B S hS P _ h g⟩

/-- In a commutative square whose two horizontal arrows are étale, the inverse image of the largest
open locus of the lower arrow is the largest open locus of the upper arrow. -/
private theorem relativeLargestOpen_etale_square
    {A X T Y : Scheme.{u}} [T.Over S] [Y.Over S]
    [Fact (B.Contains A)] [Fact (B.Contains X)]
    [Fact (B.Contains T)] [Fact (B.Contains Y)]
    (f : X ⟶ Y) (h : A ⟶ T) (a : A ⟶ X) (b : T ⟶ Y)
    [b.IsOver S] [Etale a] [Etale b] (hcomm : a ≫ f = h ≫ b) :
    a ⁻¹ᵁ W f = W h := by
  rw [preimage_relativeLargestOpen_etale B S hS P, hcomm,
    relativeLargestOpen_postcomp_etale B S hS P]

/-- In a commutative square whose right vertical arrow and comparison arrow are étale at the
relevant points, the two source points lie in their largest open loci simultaneously. -/
theorem mem_relativeLargestOpen_etaleAt
    {X' X Y' Y : Scheme.{u}} [Y'.Over S] [Y.Over S]
    [Fact (B.Contains X')] [Fact (B.Contains X)]
    [Fact (B.Contains Y')] [Fact (B.Contains Y)]
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    [g.IsOver S] (hcomm : g' ≫ f = f' ≫ g) (x' : X')
    (hg' : EtaleAt g' x')
    (hg : EtaleAt g (f'.base x')) :
    g'.base x' ∈ W f ↔ x' ∈ W f' := by
  obtain ⟨U, hxU, hU⟩ := (etaleAt_iff_exists_open g' x').mp hg'
  obtain ⟨V, hxV, hV⟩ := (etaleAt_iff_exists_open g (f'.base x')).mp hg
  let A : X'.Opens := U ⊓ f' ⁻¹ᵁ V
  have hxA : x' ∈ A := ⟨hxU, hxV⟩
  let i : A.toScheme ⟶ X' := A.ι
  let a : A.toScheme ⟶ X := A.ι ≫ g'
  let b : V.toScheme ⟶ Y := V.ι ≫ g
  have hAV : A ≤ f' ⁻¹ᵁ V := inf_le_right
  let h : A.toScheme ⟶ V.toScheme := f'.resLE V A hAV
  have : Etale a := by
    change Etale (A.ι ≫ g')
    rw [← Scheme.homOfLE_ι X' (inf_le_left : A ≤ U), Category.assoc]
    have : Etale (U.ι ≫ g') := hU
    infer_instance
  have : Etale b := hV
  have hSquare : a ≫ f = h ≫ b := by
    simp only [a, h, b, Category.assoc, hcomm, Scheme.Hom.resLE_comp_ι_assoc]
  let z : A.toScheme := ⟨x', hxA⟩
  have hsq := congrArg (fun W' => z ∈ W')
    (relativeLargestOpen_etale_square B S hS P f h a b hSquare)
  have hrestr : i ≫ f' = h ≫ V.ι := (Scheme.Hom.resLE_comp_ι f' hAV).symm
  have hsource := preimage_relativeLargestOpen_etale B S hS P i f'
  have htarget := relativeLargestOpen_postcomp_etale B S hS P h V.ι
  change a.base z ∈ W f ↔ i.base z ∈ W f'
  change (a.base z ∈ W f) = (z ∈ W h) at hsq
  rw [Iff.of_eq hsq, ← htarget, ← hrestr, ← hsource]
  rfl

end RelativeEtaleGeneral

end AlgebraicGeometry

end
