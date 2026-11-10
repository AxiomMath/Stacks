module

public import StacksFrontier.AlgebraicGeometry.Topologies.V.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Vtopology.StandardFpqcCoverings

/-!
# Permanence properties of V coverings

The V coverings of a scheme are stable in the three ways a topology must be: an isomorphism is a
V covering, a V covering stays one after an arbitrary base change, and composing a V covering
with V coverings of each of its members gives a V covering.

## Main results

* `AlgebraicGeometry.isVCovering_of_isIso`: an isomorphism, as a singleton family, is a V
  covering.
* `AlgebraicGeometry.isVCovering_pullback`: the pullback of a V covering along any morphism of
  schemes is a V covering.
* `AlgebraicGeometry.IsVCovering.comp`: V coverings are stable under composition.

## Implementation notes

Being a V covering is a condition on affine opens of the target: each must admit a finite affine
refinement that is a standard V covering. The base-change proof therefore refines the given
affine open by the affine open cover of the original target, cuts that down to a finite
subcover, and composes the standard V coverings obtained on each piece. The composition proof
transports along the index-type equalities produced by `PreZeroHypercover.pullback₂`, which is
why the chosen refinements are extracted before the families are assembled.

## References

* [Stacks Project, Tag 0ETJ](https://stacks.math.columbia.edu/tag/0ETJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

/-- The map of `𝒰.finiteSubcover` at an index `j` is the map of `𝒰` at the index that `𝒰`
assigns to the point underlying `j`. Mathlib's generated `finiteSubcover_f` states the same
equation, but with an index argument typed by the underlying `Classical.choose` rather than
by `𝒰.finiteSubcover.I₀`, so it does not apply to a consumer holding the latter. -/
private lemma openCover_finiteSubcover_f {Z : Scheme.{u}} (𝒰 : Z.OpenCover) [CompactSpace Z]
    (j : 𝒰.finiteSubcover.I₀) : 𝒰.finiteSubcover.f j = 𝒰.f (𝒰.idx j.1) := rfl

/-- A map into the `idx`-th member of the pullback of `𝒰` along `gg`, followed by the
projection to the `idx`-th member of `𝒰` viewed as the affine open it is the range of, and
then the inclusion of that open, is the same map followed by the pullback cover's own
structure morphism and `gg`. -/
private lemma comp_isoOpensRange_hom_ι {Y Z W : Scheme.{u}} (𝒰 : Y.OpenCover) (gg : Z ⟶ Y)
    (idx : 𝒰.I₀) (h : W ⟶ (𝒰.pullback₁ gg).X idx) :
    (h ≫ 𝒰.pullbackHom gg idx) ≫ (𝒰.f idx).isoOpensRange.hom ≫ (𝒰.f idx).opensRange.ι =
      (h ≫ (𝒰.pullback₁ gg).f idx) ≫ gg := by
  rw [Scheme.Hom.isoOpensRange_hom_ι, Category.assoc, 𝒰.pullbackHom_map, Category.assoc]

/-- If `h` maps into the pullback of `f` and `x` and has second component `w`, then `h` followed
by the first projection and `f` is `w` followed by `x`. -/
private lemma comp_fst_comp_eq_comp {W S T R : Scheme.{u}} {f : S ⟶ T} {x : R ⟶ T}
    {h : W ⟶ pullback f x} {w : W ⟶ R} (hw : h ≫ pullback.snd f x = w) :
    (h ≫ pullback.fst f x) ≫ f = w ≫ x := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, hw]

/-- An isomorphism of schemes, regarded as a singleton family, is a V covering. -/
@[stacks 0ETJ "isomorphism"]
lemma isVCovering_of_isIso {T' T : Scheme.{u}} (f : T' ⟶ T) [IsIso f] :
    AlgebraicGeometry.IsVCovering (fun _ : Unit ↦ T') (fun _ ↦ f) := by
  intro U hU
  let 𝒰 : PreZeroHypercover U.toScheme := PreZeroHypercover.singleton (𝟙 U.toScheme)
  refine ⟨𝒰, Finite.of_fintype _, fun _ ↦ hU, ?_, ?_⟩
  · intro V _ _ _ g
    refine ⟨V, inferInstance, inferInstance, inferInstance, RingHom.id V,
      ⟨fun _ _ h => h, isLocalHom_id V⟩, PUnit.unit, g, ?_⟩
    simp [𝒰, PreZeroHypercover.singleton]
  · refine ⟨{
      s₀ := fun _ => ()
      h₀ := fun _ => Limits.pullback.lift (U.ι ≫ inv f) (𝟙 U.toScheme) ?_
      w₀ := fun _ => ?_ }⟩
    · change (U.ι ≫ inv f) ≫ f = (𝟙 U.toScheme) ≫ U.ι
      simp [Category.assoc]
    · exact Limits.pullback.lift_snd (f := f) (g := U.ι) (U.ι ≫ inv f) (𝟙 U.toScheme)
        (by simp [Category.assoc])

/-- The pullback of a V covering along any morphism of schemes is a V covering. -/
@[stacks 0ETJ "base_change"]
lemma isVCovering_pullback {T : Scheme.{u}} {I : Type v}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T) {T' : Scheme.{u}}
    (g : T' ⟶ T) (hf : AlgebraicGeometry.IsVCovering X f) :
    AlgebraicGeometry.IsVCovering
      (fun i ↦ pullback (f i) g)
      (fun i ↦ pullback.snd (f i) g) := by
  rw [AlgebraicGeometry.isVCovering_iff]
  intro U hU
  let : IsAffine U.toScheme := hU
  let 𝒯 := T.affineOpenCover
  let 𝒱 : U.toScheme.OpenCover := 𝒯.openCover.pullback₁ (U.ι ≫ g)
  let 𝒜 := 𝒱.affineRefinement
  let ℬ := 𝒜.openCover.finiteSubcover
  let : Finite ℬ.I₀ := inferInstance
  let 𝒞 : U.toScheme.AffineCover @Flat :=
    { I₀ := ℬ.I₀
      X j := 𝒜.X (𝒜.openCover.idx j.1)
      f j := ℬ.f j
      idx := ℬ.idx
      covers := ℬ.covers
      map_prop j := by
        change Flat (𝒜.openCover.f (𝒜.openCover.idx j.1))
        infer_instance }
  let k (j : ℬ.I₀) := 𝒜.openCover.idx j.1
  let i (j : ℬ.I₀) : 𝒯.openCover.I₀ := 𝒱.fromAffineRefinement.s₀ (k j)
  have hopen (j : ℬ.I₀) : IsOpenImmersion (𝒯.f (i j)) := 𝒯.map_prop (i j)
  let Uold (j : ℬ.I₀) := @Scheme.Hom.opensRange _ _ (𝒯.f (i j)) (hopen j)
  have hUold (j : ℬ.I₀) : IsAffineOpen (Uold j) :=
    @isAffineOpen_opensRange _ _ (inferInstance : IsAffine (Spec (𝒯.X (i j)))) (𝒯.f (i j)) (hopen j)
  let q (j : ℬ.I₀) : ℬ.X j ⟶ (Uold j).toScheme :=
    (𝒱.fromAffineRefinement.h₀ (k j) ≫ 𝒯.openCover.pullbackHom (U.ι ≫ g) (i j)) ≫
      (@Scheme.Hom.isoOpensRange _ _ (𝒯.f (i j)) (hopen j)).hom
  rw [AlgebraicGeometry.isVCovering_iff] at hf
  let E (j : ℬ.I₀) := (hf (Uold j) (hUold j)).choose
  have hE (j : ℬ.I₀) := (hf (Uold j) (hUold j)).choose_spec
  let (j : ℬ.I₀) : Finite (E j).I₀ := (hE j).1
  let (j : ℬ.I₀) : ∀ a, IsAffine ((E j).X a) := (hE j).2.1
  have hWaff (j : ℬ.I₀) : IsAffine (ℬ.X j) := by
    change IsAffine (Spec (𝒞.X j))
    infer_instance
  let hpbAff (j : ℬ.I₀) (a : (E j).I₀) : IsAffine (pullback ((E j).f a) (q j)) := by
    let : IsAffine (ℬ.X j) := hWaff j
    let : IsAffine (Uold j).toScheme := hUold j
    infer_instance
  have hinner (j : ℬ.I₀) : AlgebraicGeometry.IsStandardVCovering
      (fun a ↦ pullback ((E j).f a) (q j))
      (fun a ↦ pullback.snd ((E j).f a) (q j)) := by
    let : IsAffine (ℬ.X j) := hWaff j
    let : IsAffine (Uold j).toScheme := hUold j
    exact AlgebraicGeometry.isStandardVCovering_pullback (E j).X (E j).f (q j) (hE j).2.2.1
  have hcomp := AlgebraicGeometry.IsStandardVCovering.comp
    (fun j ↦ Spec (𝒞.X j)) 𝒞.f
    (AlgebraicGeometry.isStandardVCovering_of_flat_affineCover 𝒞)
    (fun j a ↦ pullback ((E j).f a) (q j))
    (fun j a ↦ pullback.snd ((E j).f a) (q j)) hinner
  let W : PreZeroHypercover U.toScheme :=
    { I₀ := Σ j : ℬ.I₀, (E j).I₀
      X ja := pullback ((E ja.1).f ja.2) (q ja.1)
      f ja := pullback.snd ((E ja.1).f ja.2) (q ja.1) ≫ ℬ.f ja.1 }
  have hq (j : ℬ.I₀) : q j ≫ (Uold j).ι = ℬ.f j ≫ U.ι ≫ g := by
    have h1 := comp_isoOpensRange_hom_ι 𝒯.openCover (U.ι ≫ g) (i j)
      (𝒱.fromAffineRefinement.h₀ (k j))
    have h2 := congrArg (fun m ↦ m ≫ U.ι ≫ g)
      ((𝒱.fromAffineRefinement.w₀ (k j)).trans (openCover_finiteSubcover_f _ j).symm)
    exact (Category.assoc _ _ _).trans (h1.trans h2)
  let familyOld (j : ℬ.I₀) :=
    ({ I₀ := I, X := X, f := f } : PreZeroHypercover T).pullback₂ (Uold j).ι
  let familyNew :=
    ({ I₀ := I, X := fun i ↦ pullback (f i) g,
       f := fun i ↦ pullback.snd (f i) g } : PreZeroHypercover T').pullback₂ U.ι
  let φ (j : ℬ.I₀) : (E j).Hom (familyOld j) :=
    Classical.choice (hE j).2.2.2
  have hW : W.Hom familyNew := by
    refine ⟨fun ja ↦ (φ ja.1).s₀ ja.2, fun ja ↦ ?_, ?_⟩
    · let j := ja.1
      let a := ja.2
      let b : I := (φ j).s₀ a
      let h₁ : pullback ((E j).f a) (q j) ⟶ pullback (f b) g :=
        pullback.lift
          (pullback.fst ((E j).f a) (q j) ≫ (φ j).h₀ a ≫
            pullback.fst (f b) (Uold j).ι)
          (pullback.snd ((E j).f a) (q j) ≫ ℬ.f j ≫ U.ι) (by
            have hφ : ((φ j).h₀ a ≫ pullback.fst (f b) (Uold j).ι) ≫ f b =
                (E j).f a ≫ (Uold j).ι := comp_fst_comp_eq_comp ((φ j).w₀ a)
            rw [Category.assoc, hφ, ← Category.assoc, pullback.condition, Category.assoc, hq j,
              Category.assoc, Category.assoc])
      refine pullback.lift h₁ (pullback.snd ((E j).f a) (q j) ≫ ℬ.f j) ?_
      change pullback.lift _ _ _ ≫ pullback.snd (f b) g = _
      rw [pullback.lift_snd]
      simp [Category.assoc]
    · intro ja
      let j := ja.1
      let a := ja.2
      let b : I := (φ j).s₀ a
      change
        (pullback.lift _ _ _ ≫ pullback.snd (pullback.snd (f b) g) U.ι) =
          pullback.snd ((E j).f a) (q j) ≫ ℬ.f j
      rw [pullback.lift_snd]
  exact ⟨W, inferInstance, fun ja ↦ hpbAff ja.1 ja.2, hcomp, ⟨hW⟩⟩

/-- Composing a V covering with V coverings of each of its members gives a V
covering. -/
@[stacks 0ETJ "composition"]
theorem IsVCovering.comp {T : Scheme.{u}} {I : Type v}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hf : AlgebraicGeometry.IsVCovering X f) {J : I → Type w}
    (Y : ∀ i, J i → Scheme.{u}) (g : ∀ i j, Y i j ⟶ X i)
    (hg : ∀ i, AlgebraicGeometry.IsVCovering (Y i) (g i)) :
    AlgebraicGeometry.IsVCovering
      (fun ij : Σ i, J i ↦ Y ij.1 ij.2)
      (fun ij ↦ g ij.1 ij.2 ≫ f ij.1) := by
  classical
  intro U hU
  let : IsAffine U.toScheme := hU
  let E₀ : PreZeroHypercover T := ⟨I, X, f⟩
  obtain ⟨A, hAfin, hAaff, hAstd, hAref⟩ := hf U hU
  obtain ⟨α⟩ := hAref
  change A.Hom (E₀.pullback₂ U.ι) at α
  let i : A.I₀ → I := α.s₀
  let x : ∀ a, A.X a ⟶ X (i a) := fun a => α.h₀ a ≫ pullback.fst (f (i a)) U.ι
  have hx (a : A.I₀) : x a ≫ f (i a) = A.f a ≫ U.ι := comp_fst_comp_eq_comp (α.w₀ a)
  have hex (a : A.I₀) : ∃ (B : PreZeroHypercover (A.X a))
      (hBfin : Finite B.I₀) (hBaff : ∀ b, IsAffine (B.X b)),
      @AlgebraicGeometry.IsStandardVCovering (A.X a) (hAaff a) B.I₀ hBfin B.X hBaff B.f ∧
      Nonempty (B.Hom (({ I₀ := J (i a), X := Y (i a), f := g (i a) } :
        PreZeroHypercover (X (i a))).pullback₂ (x a))) := by
    let P : PreZeroHypercover (A.X a) :=
      ({ I₀ := J (i a), X := Y (i a), f := g (i a) } :
        PreZeroHypercover (X (i a))).pullback₂ (x a)
    have hP : AlgebraicGeometry.IsVCovering P.X P.f :=
      AlgebraicGeometry.isVCovering_pullback (Y (i a)) (g (i a)) (x a) (hg (i a))
    obtain ⟨B₀, hB₀fin, hB₀aff, hB₀std, ⟨β₀⟩⟩ :=
      hP ⊤ (isAffineOpen_top (A.X a))
    let e : (⊤ : (A.X a).Opens).toScheme ≅ A.X a := Scheme.topIso (A.X a)
    let B : PreZeroHypercover (A.X a) :=
      ⟨B₀.I₀, B₀.X, fun b => B₀.f b ≫ e.hom⟩
    have hBstd : @AlgebraicGeometry.IsStandardVCovering (A.X a) (hAaff a) B.I₀
        hB₀fin B.X hB₀aff B.f := by
      intro V _ _ _ q
      obtain ⟨W, hW, hWd, hWv, eW, hExt, b, h, hEq⟩ := hB₀std V (q ≫ e.inv)
      refine ⟨W, hW, hWd, hWv, eW, hExt, b, h, ?_⟩
      simpa [B, Category.assoc] using
        congrArg (fun k => k ≫ e.hom) hEq
    exact ⟨B, hB₀fin, hB₀aff, hBstd,
      ⟨⟨β₀.s₀, fun b => β₀.h₀ b ≫ pullback.fst _ _, fun b ↦ comp_fst_comp_eq_comp (β₀.w₀ b)⟩⟩⟩
  choose B hBfin hBaff hBstd hBref using hex
  let β : ∀ a, (B a).Hom
      (({ I₀ := J (i a), X := Y (i a), f := g (i a) } :
        PreZeroHypercover (X (i a))).pullback₂ (x a)) := fun a => Classical.choice (hBref a)
  let : Finite A.I₀ := hAfin
  let : ∀ a, IsAffine (A.X a) := hAaff
  let : ∀ a, Finite (B a).I₀ := hBfin
  let : ∀ a b, IsAffine ((B a).X b) := hBaff
  let C : PreZeroHypercover U.toScheme := {
    I₀ := Σ a : A.I₀, (B a).I₀
    X := fun c => (B c.1).X c.2
    f := fun c => (B c.1).f c.2 ≫ A.f c.1
  }
  have hCfin : Finite C.I₀ := by
    dsimp [C, PreZeroHypercover.bind]
    infer_instance
  let : Finite C.I₀ := hCfin
  have hCstd : @AlgebraicGeometry.IsStandardVCovering U.toScheme hU C.I₀ hCfin
      C.X (fun c => hBaff c.1 c.2) C.f := by
    simpa [C, PreZeroHypercover.bind] using
      (AlgebraicGeometry.IsStandardVCovering.comp A.X A.f hAstd (fun a => (B a).X)
        (fun a => (B a).f) hBstd)
  refine ⟨C, hCfin, fun c => hBaff c.1 c.2, hCstd, ?_⟩
  let D : PreZeroHypercover T := {
    I₀ := Σ i, J i
    X := fun ij => Y ij.1 ij.2
    f := fun ij => g ij.1 ij.2 ≫ f ij.1
  }
  change Nonempty (C.Hom (D.pullback₂ U.ι))
  refine ⟨⟨fun c ↦ ⟨i c.1, (β c.1).s₀ c.2⟩, fun c ↦ ?_, fun c ↦ ?_⟩⟩
  · exact pullback.lift ((β c.1).h₀ c.2 ≫ pullback.fst _ _) (C.f c)
      (by
        refine (congrArg (· ≫ _) (comp_fst_comp_eq_comp ((β c.1).w₀ c.2))).trans ?_
        rw [Category.assoc, hx c.1, ← Category.assoc])
  · exact pullback.lift_snd _ _ _

end AlgebraicGeometry
