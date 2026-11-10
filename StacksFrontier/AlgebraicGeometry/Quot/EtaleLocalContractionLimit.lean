module

public import StacksFrontier.AlgebraicGeometry.Quot.EtaleLocalContractionBaseChange
public import StacksFrontier.RingTheory.GRing.EssFiniteType
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extending a contraction of a fibre étale locally on an affine base

Let `A` be a ring, `𝔭 ⊂ A` a prime with `ψ : κ(𝔭) ≅ K`, and `f : X ⟶ Spec A` a family of curves
(flat, proper, of finite presentation and of relative dimension at most one) in a big fppf site.
If the fibre of `X` over `k : Spec K ⟶ Spec A` is presented by a scheme `F` of dimension at most
one and `h₀ : F ⟶ Y₀` is a morphism over `K` to a proper scheme of dimension at most one with
`𝒪_{Y₀} ≅ h₀,*𝒪_F` and `R¹h₀,*𝒪_F = 0`, the conclusion of [Stacks, Tag 0E7C] holds at `k`.

This is the reduction of the proof of [Stacks, Tag 0E7C] to a base of finite type over `ℤ`:

* `A` is the filtered colimit of its finitely generated subrings `A_j`, and `X` descends to a
  family of curves over some `Spec A_j` ([Stacks, Tags 07SK, 08K0, 08K1]);
* `κ(𝔭)` is the filtered colimit of the residue fields `κ(𝔭_j)` at `𝔭_j = 𝔭 ∩ A_j`, so `Y₀` and
  `h₀` descend to a stage `κ(𝔭_j)` (the same limit statements, over the spectra of these fields);
  the descended fibres are schemes ([Stacks, Tag 0ADD]) and the conditions `𝒪 = h_*𝒪`, `R¹h_*𝒪 = 0`
  descend along the field extension ([Stacks, Tag 02KH] and faithful flatness);
* `A_j` is Noetherian and its local rings are G-rings ([Stacks, Tag 07PX]), so the Noetherian
  case `AlgebraicGeometry.EtaleLocalContraction.hasEtaleLocalExtension_of_isNoetherianRing`
  applies at the stage, and its conclusion base changes back to `Spec A`
  (`AlgebraicGeometry.EtaleLocalContraction.HasEtaleLocalExtension.baseChange`).

## Main results

* `CommRingCat.isColimitOfInjectiveOfJointlySurjective`: a cocone of rings over a directed
  preorder with injective, jointly surjective legs is a colimit.
* `AlgebraicGeometry.EtaleLocalContraction.hasEtaleLocalExtension_of_affine`: the statement above.

## References

* [Stacks Project, Tag 0E7C](https://stacks.math.columbia.edu/tag/0E7C)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 07PX](https://stacks.math.columbia.edu/tag/07PX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

namespace CommRingCat

variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] {F : ι ⥤ CommRingCat.{u}}
  (c : Cocone F) (hinj : ∀ i, Function.Injective (c.ι.app i))
  (hsurj : ∀ x : c.pt, ∃ i y, c.ι.app i y = x)

include hinj in
/-- In a cocone of rings over a directed preorder with injective legs, two elements identified
in the vertex are identified by every other cocone. -/
theorem cocone_ι_apply_eq_of_injective (s : Cocone F) {i j : ι} {y : F.obj i} {z : F.obj j}
    (h : c.ι.app i y = c.ι.app j z) : s.ι.app i y = s.ι.app j z := by
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  have hc : ∀ {a : ι} (hak : a ≤ k) (w : F.obj a),
      c.ι.app a w = c.ι.app k (F.map (homOfLE hak) w) :=
    fun hak w => (ConcreteCategory.congr_hom (c.w (homOfLE hak)) w).symm
  have hs : ∀ {a : ι} (hak : a ≤ k) (w : F.obj a),
      s.ι.app a w = s.ι.app k (F.map (homOfLE hak) w) :=
    fun hak w => (ConcreteCategory.congr_hom (s.w (homOfLE hak)) w).symm
  rw [hc hik, hc hjk] at h
  rw [hs hik, hs hjk, hinj k h]

include hinj hsurj in
/-- **A cocone of rings with injective, jointly surjective legs is a colimit.** -/
def isColimitOfInjectiveOfJointlySurjective : IsColimit c := by
  classical
  have hi : Nonempty ι := ⟨(hsurj 0).choose⟩
  let sec : c.pt → Σ i, F.obj i := fun x => ⟨(hsurj x).choose, (hsurj x).choose_spec.choose⟩
  have hsec : ∀ x, c.ι.app (sec x).1 (sec x).2 = x := fun x => (hsurj x).choose_spec.choose_spec
  let d : ∀ s : Cocone F, c.pt → s.pt := fun s x => s.ι.app (sec x).1 (sec x).2
  have hd : ∀ (s : Cocone F) {i : ι} (y : F.obj i), d s (c.ι.app i y) = s.ι.app i y :=
    fun s i y => cocone_ι_apply_eq_of_injective c hinj s (hsec _)
  have hcommon : ∀ x₁ x₂ : c.pt, ∃ (k : ι) (y₁ y₂ : F.obj k),
      c.ι.app k y₁ = x₁ ∧ c.ι.app k y₂ = x₂ := by
    intro x₁ x₂
    obtain ⟨i, y, rfl⟩ := hsurj x₁
    obtain ⟨j, z, rfl⟩ := hsurj x₂
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    exact ⟨k, F.map (homOfLE hik) y, F.map (homOfLE hjk) z,
      ConcreteCategory.congr_hom (c.w (homOfLE hik)) y,
      ConcreteCategory.congr_hom (c.w (homOfLE hjk)) z⟩
  let D : ∀ s : Cocone F, c.pt →+* s.pt := fun s =>
    { toFun := d s
      map_one' := by
        obtain ⟨i⟩ := hi
        rw [← map_one (c.ι.app i).hom, hd, map_one]
      map_mul' := fun x₁ x₂ => by
        obtain ⟨k, y₁, y₂, rfl, rfl⟩ := hcommon x₁ x₂
        rw [← map_mul (c.ι.app k).hom, hd, hd, hd, map_mul]
      map_zero' := by
        obtain ⟨i⟩ := hi
        rw [← map_zero (c.ι.app i).hom, hd, map_zero]
      map_add' := fun x₁ x₂ => by
        obtain ⟨k, y₁, y₂, rfl, rfl⟩ := hcommon x₁ x₂
        rw [← map_add (c.ι.app k).hom, hd, hd, hd, map_add] }
  exact
    { desc s := ofHom (D s)
      fac s i := by
        ext y
        exact hd s y
      uniq s m hm := by
        ext x
        obtain ⟨i, y, rfl⟩ := hsurj x
        change m (c.ι.app i y) = d s (c.ι.app i y)
        rw [hd]
        exact ConcreteCategory.congr_hom (hm i) y }

end CommRingCat

namespace AlgebraicGeometry.EtaleLocalContraction

/-! ### A ring as the filtered colimit of its finitely generated subrings -/

section Subrings

variable (A : Type u) [CommRing A]

/-- The finitely generated subrings of `A` (as `ℤ`-subalgebras), ordered by inclusion. -/
abbrev FGSubring : Type u := {S : Subalgebra ℤ A // S.FG}

/-- The finitely generated subrings of `A` form a directed order. -/
instance : IsDirectedOrder (FGSubring A) where
  directed S T := ⟨⟨S.1 ⊔ T.1, S.2.sup T.2⟩, le_sup_left (a := S.1), le_sup_right (a := S.1)⟩

/-- The smallest subring of `A` is finitely generated, so `FGSubring A` is nonempty. -/
instance : Nonempty (FGSubring A) := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩

/-- The diagram of the finitely generated subrings of `A` and their inclusions. -/
def fgSubringDiagram : FGSubring A ⥤ CommRingCat.{u} where
  obj S := .of S.1
  map h := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom h)).toRingHom

/-- The cocone of inclusions of the finitely generated subrings into `A`. -/
def fgSubringCocone : Cocone (fgSubringDiagram A) where
  pt := .of A
  ι := { app S := CommRingCat.ofHom S.1.val.toRingHom }

/-- **A ring is the filtered colimit of its finitely generated subrings.** -/
def isColimitFgSubringCocone : IsColimit (fgSubringCocone A) := by
  classical
  exact CommRingCat.isColimitOfInjectiveOfJointlySurjective _ (fun S => Subtype.val_injective)
    fun x => ⟨⟨Algebra.adjoin ℤ (({(show A from x)} : Finset A) : Set A),
      Subalgebra.fg_adjoin_finset _⟩, ⟨(show A from x), Algebra.subset_adjoin
        (Finset.mem_coe.mpr (Finset.mem_singleton_self _))⟩, rfl⟩

end Subrings

/-! ### The residue fields at the finitely generated subrings -/

section ResidueSystem

/-- Two ring homomorphisms out of the residue field `κ(𝔭)` agreeing on the image of `A` agree. -/
theorem residueField_ringHom_ext {A L : Type*} [CommRing A] [CommRing L] {𝔭 : Ideal A} [𝔭.IsPrime]
    {f g : 𝔭.ResidueField →+* L} (h : ∀ a : A, f (algebraMap A _ a) = g (algebraMap A _ a)) :
    f = g := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (A ⧸ 𝔭)) ?_
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
  have e : algebraMap (A ⧸ 𝔭) 𝔭.ResidueField (Ideal.Quotient.mk 𝔭 a) = algebraMap A _ a := rfl
  simp only [RingHom.comp_apply, e, h]

variable (A : Type u) [CommRing A] (𝔭 : Ideal A) [𝔭.IsPrime]

/-- The prime `𝔭 ∩ A_j` of a finitely generated subring `A_j` of `A`. -/
abbrev stagePrime (j : FGSubring A) : Ideal j.1 :=
  𝔭.comap j.1.val.toRingHom

/-- The finitely generated subrings of `A` containing a given one. -/
abbrev StageTail (j₀ : FGSubring A) : Type u := {j : FGSubring A // j₀ ≤ j}

/-- The finitely generated subrings containing `j₀` form a directed order. -/
instance (j₀ : FGSubring A) : IsDirectedOrder (StageTail A j₀) where
  directed a b :=
    ⟨⟨⟨a.1.1 ⊔ b.1.1, a.1.2.sup b.1.2⟩, a.2.trans (le_sup_left (a := a.1.1))⟩,
      le_sup_left (a := a.1.1), le_sup_right (a := a.1.1)⟩

/-- There is a finitely generated subring containing `j₀`, namely `j₀` itself. -/
instance (j₀ : FGSubring A) : Nonempty (StageTail A j₀) := ⟨⟨j₀, le_rfl⟩⟩

omit [𝔭.IsPrime] in
/-- For `A_j ⊆ A_{j'}`, the prime `𝔭_j` is the preimage of `𝔭_{j'}` under the inclusion. -/
theorem stagePrime_comap {j j' : FGSubring A} (h : j ≤ j') :
    stagePrime A 𝔭 j =
      (stagePrime A 𝔭 j').comap (Subalgebra.inclusion (leOfHom (homOfLE h))).toRingHom :=
  rfl

/-- The residue field map `κ(𝔭_j) ⟶ κ(𝔭_{j'})` of an inclusion of finitely generated subrings. -/
def stageResidueMap {j j' : FGSubring A} (h : j ≤ j') :
    (stagePrime A 𝔭 j).ResidueField →+* (stagePrime A 𝔭 j').ResidueField :=
  Ideal.ResidueField.map _ _ (Subalgebra.inclusion h).toRingHom rfl

/-- The residue field map `κ(𝔭_j) ⟶ κ(𝔭)`. -/
def stageResidueToResidue (j : FGSubring A) :
    (stagePrime A 𝔭 j).ResidueField →+* 𝔭.ResidueField :=
  Ideal.ResidueField.map _ _ j.1.val.toRingHom rfl

/-- The residue field map `κ(𝔭_j) ⟶ κ(𝔭_{j'})` sends the image of `a ∈ A_j` to the image of `a`
in `A_{j'}`. -/
theorem stageResidueMap_algebraMap {j j' : FGSubring A} (h : j ≤ j') (a : j.1) :
    stageResidueMap A 𝔭 h (algebraMap j.1 _ a) = algebraMap j'.1 _ (Subalgebra.inclusion h a) :=
  Ideal.ResidueField.map_algebraMap _ _ _ _ a

/-- The residue field map `κ(𝔭_j) ⟶ κ(𝔭)` sends the image of `a ∈ A_j` to the image of `a` in
`A`. -/
theorem stageResidueToResidue_algebraMap (j : FGSubring A) (a : j.1) :
    stageResidueToResidue A 𝔭 j (algebraMap j.1 _ a) = algebraMap A _ (a : A) :=
  Ideal.ResidueField.map_algebraMap _ _ _ _ a

/-- The residue field maps `κ(𝔭_j) ⟶ κ(𝔭_{j'}) ⟶ κ(𝔭)` compose to `κ(𝔭_j) ⟶ κ(𝔭)`. -/
theorem stageResidueMap_comp_toResidue {j j' : FGSubring A} (h : j ≤ j') :
    (stageResidueToResidue A 𝔭 j').comp (stageResidueMap A 𝔭 h) = stageResidueToResidue A 𝔭 j := by
  refine residueField_ringHom_ext fun a => ?_
  simp only [RingHom.comp_apply, stageResidueMap_algebraMap, stageResidueToResidue_algebraMap]
  rfl

/-- The residue fields `κ(𝔭_j)` of the finitely generated subrings containing `j₀`, as a
diagram of rings. -/
def stageResidueDiagram (j₀ : FGSubring A) : StageTail A j₀ ⥤ CommRingCat.{u} where
  obj j := .of (stagePrime A 𝔭 j.1).ResidueField
  map {j j'} h := CommRingCat.ofHom (stageResidueMap A 𝔭 (leOfHom h))
  map_id j := by
    have : stageResidueMap A 𝔭 (le_refl j.1) = RingHom.id _ :=
      residueField_ringHom_ext fun a => by
        rw [stageResidueMap_algebraMap]
        rfl
    exact CommRingCat.hom_ext this
  map_comp {j j' j''} h h' := by
    have : stageResidueMap A 𝔭 ((leOfHom h).trans (leOfHom h')) =
        (stageResidueMap A 𝔭 (leOfHom h')).comp (stageResidueMap A 𝔭 (leOfHom h)) :=
      residueField_ringHom_ext fun a => by
        simp only [RingHom.comp_apply, stageResidueMap_algebraMap]
        rfl
    exact CommRingCat.hom_ext this

variable {K : Type u} [Field K] (ψ : 𝔭.ResidueField ≃+* K)

/-- The cocone of the residue fields `κ(𝔭_j)` with vertex `K ≅ κ(𝔭)`. -/
def stageResidueCocone (j₀ : FGSubring A) : Cocone (stageResidueDiagram A 𝔭 j₀) where
  pt := .of K
  ι :=
    { app j := CommRingCat.ofHom (ψ.toRingHom.comp (stageResidueToResidue A 𝔭 j.1))
      naturality _ _ h := CommRingCat.hom_ext (RingHom.ext fun x =>
        congrArg ψ (RingHom.congr_fun (stageResidueMap_comp_toResidue A 𝔭 (leOfHom h)) x)) }

/-- **`κ(𝔭)` is the filtered colimit of the residue fields `κ(𝔭_j)`.** -/
def isColimitStageResidueCocone (j₀ : FGSubring A) :
    IsColimit (stageResidueCocone A 𝔭 ψ j₀) := by
  classical
  refine CommRingCat.isColimitOfInjectiveOfJointlySurjective _
    (fun j => (ψ.toRingHom.comp (stageResidueToResidue A 𝔭 j.1)).injective) fun x => ?_
  obtain ⟨⟨a, b⟩, hy⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (A ⧸ 𝔭)) (ψ.symm x)
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b', hb'⟩ := Ideal.Quotient.mk_surjective (b : A ⧸ 𝔭)
  let j₁ : FGSubring A :=
    ⟨Algebra.adjoin ℤ (({a', b'} : Finset A) : Set A), Subalgebra.fg_adjoin_finset _⟩
  let j : FGSubring A := ⟨j₀.1 ⊔ j₁.1, j₀.2.sup j₁.2⟩
  have hj₀ : j₀ ≤ j := le_sup_left (a := j₀.1)
  have hj₁ : j₁ ≤ j := le_sup_right (a := j₀.1)
  have ha : a' ∈ j.1 := hj₁ (Algebra.subset_adjoin (by simp))
  have hb : b' ∈ j.1 := hj₁ (Algebra.subset_adjoin (by simp))
  refine ⟨⟨j, hj₀⟩, algebraMap j.1 (stagePrime A 𝔭 j).ResidueField ⟨a', ha⟩ /
    algebraMap j.1 (stagePrime A 𝔭 j).ResidueField ⟨b', hb⟩, ?_⟩
  change ψ (stageResidueToResidue A 𝔭 j _) = x
  dsimp only at hy
  rw [map_div₀, stageResidueToResidue_algebraMap, stageResidueToResidue_algebraMap,
    ← ψ.apply_symm_apply x, ← hy, IsFractionRing.mk'_eq_div, ← hb']
  rfl

end ResidueSystem

/-! ### The affine case -/

section Affine

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

attribute [local instance] Space.preservesLimitsOfShape_walkingCospan_toScheme

/-- `Spec` takes a commuting triangle of rings to a commuting triangle of schemes. -/
theorem spec_map_comp_eq_of_comp_eq {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (h : R ⟶ T)
    (hfg : f ≫ g = h) : Spec.map g ≫ Spec.map f = Spec.map h := by
  rw [← Spec.map_comp, hfg]

/-- A morphism of schemes to the spectrum of a field is flat. -/
@[ega "IV 11.9.9" "Parenthetical clause"]
theorem flat_of_target_spec_field {K : Type u} [Field K] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of K)) :
    Flat p := by
  have : Subsingleton (Spec (.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  infer_instance

/-- `R¹ f_* 𝒪_X = 0` in the `ℤ`-indexed spelling is the same as in Mathlib's `ℕ`-indexed one. -/
private theorem isZero_firstDirectImageStructureSheaf_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsZero (Stacks.AlgebraicGeometry.TopDegreeBaseChange.firstDirectImageStructureSheaf f) ↔
      IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
        (SheafOfModules.unit X.ringCatSheaf)) := by
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard Y.Modules
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ 1 _).symm

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
/-- **[Stacks, Tag 0E7C] from a residue field stage.** Let `X` over `T` be the base change along
`τ : T ⟶ Spec R` of a flat proper `X'` of finite presentation, where `R` is Noetherian with a
G-ring local ring at a prime `𝔭'`, and let `k : K ⟶ T` be a point over the point
`k' : Spec κ(𝔭') ⟶ Spec R` through `m : K ⟶ Spec κ(𝔭')`. If the fibre of `X` over `k` is presented
by `F` and the morphism `h₀ : F ⟶ Y₀` over `K` is, through cartesian squares over `m`, the base
change of a morphism `c₀ : X'_{κ(𝔭')} ⟶ Y'` to a flat proper `Y'` over `κ(𝔭')` of finite
presentation and relative dimension at most one, the conclusion of [Stacks, Tag 0E7C] holds at
`k`. -/
theorem hasEtaleLocalExtension_of_residueStage {T KO F Y0O : BigFppfOver B integerBase hZ}
    {X : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj T) {kK : KO ⟶ T}
    {tX : F ⟶ KO} {iX : yoneda.obj F ⟶ X} (hiX : IsPullback iX (yoneda.map tX) f (yoneda.map kK))
    (hdimF : topologicalKrullDim ((𝒯).obj F) ≤ 1) (yp : Y0O ⟶ KO)
    (hyd : Space.HasRelativeDimensionLE 1 B integerBase hZ (yoneda.map yp))
    (h₀O : F ⟶ Y0O) (hh₀O : h₀O ≫ yp = tX)
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit ((𝒯).map h₀O)))
    (hR' : IsZero (firstDirectImageStructureSheaf ((𝒯).map h₀O)))
    (R : Type u) [CommRing R] [IsNoetherianRing R] (hR : B.Contains (Spec (.of R)))
    (𝔭' : Ideal R) [𝔭'.IsPrime] (hG : IsGRing (Localization.AtPrime 𝔭'))
    (hκ₀ : B.Contains (Spec (.of 𝔭'.ResidueField)))
    {X' : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (hX' : IsAlgebraicSpace B integerBase hZ X')
    (f' : X' ⟶ yoneda.obj (integerSiteObject B hZ hR)) (hflX' : Space.IsFlat B integerBase hZ f')
    (hprX' : Space.IsProper B integerBase hZ f')
    (hfpX' : Space.IsFinitePresentation B integerBase hZ f') (q : X ⟶ X')
    (τ : T ⟶ integerSiteObject B hZ hR) (sq : IsPullback q f f' (yoneda.map τ))
    (m : KO ⟶ integerSiteObject B hZ hκ₀) [Flat ((𝒯).map m)] [Surjective ((𝒯).map m)]
    (hm : Space.IsFpqcCovering B integerBase hZ (fun _ : Unit => yoneda.map m))
    (hkm : kK ≫ τ = m ≫ integerSiteMap B hZ hκ₀ hR (Spec.map (CommRingCat.ofHom
      ((RingEquiv.refl 𝔭'.ResidueField).toRingHom.comp (algebraMap R 𝔭'.ResidueField)))))
    {XM YM : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (hXM : IsAlgebraicSpace B integerBase hZ XM)
    (hYM : IsAlgebraicSpace B integerBase hZ YM)
    (fM : XM ⟶ yoneda.obj (integerSiteObject B hZ hκ₀))
    (gM : YM ⟶ yoneda.obj (integerSiteObject B hZ hκ₀))
    (hflXM : Space.IsFlat B integerBase hZ fM) (hprXM : Space.IsProper B integerBase hZ fM)
    (hfpXM : Space.IsFinitePresentation B integerBase hZ fM)
    (hflM : Space.IsFlat B integerBase hZ gM) (hprM : Space.IsProper B integerBase hZ gM)
    (hfpM : Space.IsFinitePresentation B integerBase hZ gM) (cM : XM ⟶ YM) (hcM : cM ≫ gM = fM)
    (qXM : yoneda.obj F ⟶ XM) (qYM : yoneda.obj Y0O ⟶ YM)
    (sqqXM : IsPullback qXM (yoneda.map tX) fM (yoneda.map m))
    (sqqYM : IsPullback qYM (yoneda.map yp) gM (yoneda.map m))
    (hcomp : yoneda.map h₀O ≫ qYM = qXM ≫ cM)
    (ψXM : XM ⟶ X') (sqXM' : IsPullback ψXM fM f' (yoneda.map (integerSiteMap B hZ hκ₀ hR
      (Spec.map (CommRingCat.ofHom
        ((RingEquiv.refl 𝔭'.ResidueField).toRingHom.comp (algebraMap R 𝔭'.ResidueField)))))))
    (hqq : iX ≫ q = qXM ≫ ψXM) :
    HasEtaleLocalExtension f kK tX iX ((𝒯).map yp) ((𝒯).map h₀O) := by
  have hFa := isAlgebraicSpace_yoneda B integerBase hZ F
  have hYa := isAlgebraicSpace_yoneda B integerBase hZ Y0O
  have hcP : yoneda.map h₀O ≫ yoneda.map yp = yoneda.map tX := by
    rw [← Functor.map_comp, hh₀O]
  have hdX : Space.HasRelativeDimensionLE 1 B integerBase hZ (yoneda.map tX) := fun x =>
    Space.relativeDimensionLE_schemeSpaceMap B integerBase hZ tX 1 (by exact_mod_cast hdimF) x
  obtain ⟨FX₀, F₁₀, tX₀, t₁₀, eX₀, e₁₀, a₁₀, heX₀, he₁₀, hdX₀, hd₁₀, ha₁₀, hat₁₀, -, h0₀, hR₀,
      -⟩ :=
    Space.exists_closedFibreData_of_isPullback_field hκ₀ m hm hXM hYM hYM fM gM gM hflXM hprXM
      hfpXM hflM hprM hfpM hprM cM cM hcM hcM hFa hYa hYa (yoneda.map tX) (yoneda.map yp)
      (yoneda.map yp) qXM qYM qYM sqqXM sqqYM sqqYM hdX hyd (yoneda.map h₀O) (yoneda.map h₀O)
      hcP hcomp hcomp (Iso.refl _) (Iso.refl _) tX yp (by simp) (by simp) h₀O (by simp) h0 hR'
      (Iso.refl _) (by simp) (by simp)
  have hiX' : IsPullback (eX₀.hom ≫ ψXM) (yoneda.map tX₀) f' (yoneda.map (integerSiteMap B hZ hκ₀ hR
      (Spec.map (CommRingCat.ofHom
        ((RingEquiv.refl 𝔭'.ResidueField).toRingHom.comp (algebraMap R 𝔭'.ResidueField)))))) :=
    IsPullback.of_iso sqXM' eX₀.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
      (by simp [← heX₀]) (by simp) (by simp)
  have : IsProper ((𝒯).map t₁₀) := Space.isProper_toScheme_map_of_iso B integerBase hZ e₁₀ gM t₁₀
    he₁₀ hprM
  let pY₀' : (𝒯).obj F₁₀ ⟶ Spec (.of 𝔭'.ResidueField) := (𝒯).map t₁₀
  have : IsProper pY₀' := ‹IsProper ((𝒯).map t₁₀)›
  have HN := hasEtaleLocalExtension_of_isNoetherianRing R hR 𝔭' hG 𝔭'.ResidueField hκ₀
    (RingEquiv.refl _) hX' f' hflX' hprX' hfpX' tX₀ (eX₀.hom ≫ ψXM) hiX' hdX₀
    pY₀' hd₁₀ ((𝒯).map a₁₀) (by
      change (𝒯).map a₁₀ ≫ (𝒯).map t₁₀ = _
      rw [← Functor.map_comp, hat₁₀]) h0₀
    ((isZero_firstDirectImageStructureSheaf_iff _).1 hR₀)
  have sqc : IsPullback qXM (yoneda.map h₀O) cM qYM :=
    IsPullback.of_bot (by rwa [hcP, hcM]) hcomp.symm sqqYM
  obtain ⟨rX, r, hrX, hr, hpbr, -⟩ := Space.exists_isPullback_toScheme_of_isPullback_of_iso B
    integerBase hZ sqc (Iso.refl _) (Iso.refl _) eX₀ e₁₀ h₀O a₁₀ (by simp) ha₁₀
  have haF : iX ≫ q = yoneda.map rX ≫ eX₀.hom ≫ ψXM := by
    rw [hqq, hrX]
    simp
  have haFt : rX ≫ tX₀ = tX ≫ m := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp, hrX, ← heX₀, Iso.refl_hom, Category.id_comp,
      Category.assoc, Iso.inv_hom_id_assoc, sqqXM.w]
  have hbY : IsPullback ((𝒯).map r) ((𝒯).map yp) ((𝒯).map t₁₀) ((𝒯).map m) := by
    have h₁ : IsPullback (yoneda.map r) (yoneda.map yp) (yoneda.map t₁₀) (yoneda.map m) :=
      IsPullback.of_iso sqqYM (Iso.refl _) e₁₀.symm (Iso.refl _) (Iso.refl _)
        (by simp [hr]) (by simp) (by simp [← he₁₀]) (by simp)
    have h₂ : IsPullback r yp t₁₀ m :=
      IsPullback.of_map yoneda (yoneda.map_injective (by simpa only [Functor.map_comp] using h₁.w))
        h₁
    exact h₂.map (𝒯)
  have hh₀b : (𝒯).map h₀O ≫ (𝒯).map r = (𝒯).map rX ≫ (𝒯).map a₁₀ := by
    rw [← Functor.map_comp, ← Functor.map_comp, hpbr.w]
  exact HN.baseChange f q τ sq kK m hkm tX iX hiX rX haF haFt ((𝒯).map yp)
    ((𝒯).map r) hbY ((𝒯).map h₀O) (by rw [← Functor.map_comp, hh₀O]) hh₀b

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
/-- **[Stacks, Tag 0E7C] over an affine base.** Let `A` be a ring, `𝔭 ⊂ A` a prime with
`ψ : κ(𝔭) ≅ K`, and `k : Spec K ⟶ Spec A` the corresponding point. Let `f : X ⟶ Spec A` be a family
of curves whose fibre over `k` is presented by `tX : F ⟶ Spec K` with `dim F ≤ 1`, and let
`h₀ : F ⟶ Y₀` be a morphism over `K` to a proper scheme of dimension at most one with
`𝒪_{Y₀} ≅ h₀,*𝒪_F` and `R¹h₀,*𝒪_F = 0`. Then the conclusion of the tag holds at `k`. -/
theorem hasEtaleLocalExtension_of_affine (A : Type u) [CommRing A]
    (hA : B.Contains (Spec (.of A))) (𝔭 : Ideal A) [𝔭.IsPrime] (K : Type u) [Field K]
    (hK : B.Contains (Spec (.of K))) (ψ : 𝔭.ResidueField ≃+* K)
    {X : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B integerBase hZ X)
    (f : X ⟶ yoneda.obj (integerSiteObject B hZ hA)) (hfl : Space.IsFlat B integerBase hZ f)
    (hpr : Space.IsProper B integerBase hZ f) (hfp : Space.IsFinitePresentation B integerBase hZ f)
    {F : BigFppfOver B integerBase hZ} (tX : F ⟶ integerSiteObject B hZ hK)
    (iX : yoneda.obj F ⟶ X)
    (hiX : IsPullback iX (yoneda.map tX) f (yoneda.map (integerSiteMap B hZ hK hA
      (Spec.map (CommRingCat.ofHom (ψ.toRingHom.comp (algebraMap A 𝔭.ResidueField)))))))
    (hdimF : topologicalKrullDim ((𝒯).obj F) ≤ 1)
    {Y₀ : Scheme.{u}} (pY₀ : Y₀ ⟶ Spec (.of K)) [IsProper pY₀]
    (hdimY : topologicalKrullDim Y₀ ≤ 1) (h₀ : (𝒯).obj F ⟶ Y₀) (hh₀ : h₀ ≫ pY₀ = (𝒯).map tX)
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit h₀))
    (hR1 : IsZero (((Scheme.Modules.pushforward h₀).rightDerived 1).obj
      (SheafOfModules.unit ((𝒯).obj F).ringCatSheaf))) :
    HasEtaleLocalExtension f (integerSiteMap B hZ hK hA
      (Spec.map (CommRingCat.ofHom (ψ.toRingHom.comp (algebraMap A 𝔭.ResidueField)))))
      tX iX pY₀ h₀ := by
  classical
  let κR : A →+* K := ψ.toRingHom.comp (algebraMap A 𝔭.ResidueField)
  let kK := integerSiteMap B hZ hK hA (Spec.map (CommRingCat.ofHom κR))
  have hft : ∀ i : FGSubring A, Algebra.FiniteType ℤ i.1 :=
    fun i => (Subalgebra.fg_iff_finiteType _).mp i.2
  have hRd : ∀ i, B.Contains (Spec ((fgSubringDiagram A).obj i)) := fun i => by
    have := hft i
    exact Space.contains_spec_of_essFiniteType B i.1
  let ε : (𝒯).obj (integerSiteObject B hZ hA) ≅ Spec (fgSubringCocone A).pt := Iso.refl _
  let D := Space.specStageDiagram (hZ := hZ) (fgSubringDiagram A) hRd
  let cn := Space.specStageCone (fgSubringDiagram A) hRd (fgSubringCocone A).ι ε
  have hcn : IsLimit ((𝒯).mapCone cn) := Space.isLimitSpecStageCone (fgSubringDiagram A) hRd
    (fgSubringCocone A).ι (isColimitFgSubringCocone A) ε
  have hD : ∀ j, IsAffine ((𝒯).obj (D.obj j)) := fun j =>
    inferInstanceAs (IsAffine (Spec ((fgSubringDiagram A).obj j.unop)))
  have Pfp := Space.isFinitePresentationColimit_of_isLimit_of_isAffine hD hcn
  obtain ⟨i₀, X₀, f₀, q₀, hX₀, hfp₀, sq₀⟩ :=
    Space.exists_isPullback_of_isFinitePresentationColimit Pfp hX f hfp
  obtain ⟨N, hN, hflN, hprN⟩ :=
    Space.exists_stage_isFlat_isProper D hD cn hcn i₀.unop hX₀ hX f₀ hfp₀ f q₀ sq₀ hfl hpr
  have hTa := fun j => isAlgebraicSpace_yoneda B integerBase hZ (D.obj j)
  set e₀ : op N ⟶ i₀ := (homOfLE hN).op
  have hX₁ := isAlgebraicSpace_pullback B integerBase hZ f₀ (yoneda.map (D.map e₀)) hX₀ (hTa _)
    (hTa _)
  have hfp₁ :
      Space.IsFinitePresentation B integerBase hZ (pullback.snd f₀ (yoneda.map (D.map e₀))) :=
    Space.isFinitePresentation_of_isPullback B integerBase hZ hX₁ hX₀ (hTa _) (hTa _)
      (IsPullback.of_hasPullback f₀ _) hfp₀
  have sq₁ := Space.isPullback_lift_cone cn e₀ sq₀
  set X₁ := pullback f₀ (yoneda.map (D.map e₀))
  set f₁ : X₁ ⟶ yoneda.obj (D.obj (op N)) := pullback.snd f₀ (yoneda.map (D.map e₀))
  obtain ⟨q₁, sq₁⟩ : ∃ q₁ : X ⟶ X₁, IsPullback q₁ f f₁ (yoneda.map (cn.π.app (op N))) := ⟨_, sq₁⟩
  have hRf : ∀ j, B.Contains (Spec ((stageResidueDiagram A 𝔭 N).obj j)) := fun j => by
    change (Spec (.of (stagePrime A 𝔭 j.1).ResidueField)).size < B.cutoff
    have h : (Spec (.of K)).size < B.cutoff := hK
    rw [Scheme.size_Spec] at h ⊢
    exact lt_of_le_of_lt (max_le_max le_rfl (Cardinal.mk_le_of_injective
      (ψ.toRingHom.comp (stageResidueToResidue A 𝔭 j.1)).injective)) h
  let εf : (𝒯).obj (integerSiteObject B hZ hK) ≅ Spec (stageResidueCocone A 𝔭 ψ N).pt :=
    Iso.refl _
  let Df := Space.specStageDiagram (hZ := hZ) (stageResidueDiagram A 𝔭 N) hRf
  let cf := Space.specStageCone (stageResidueDiagram A 𝔭 N) hRf (stageResidueCocone A 𝔭 ψ N).ι εf
  have hcf : IsLimit ((𝒯).mapCone cf) := Space.isLimitSpecStageCone (stageResidueDiagram A 𝔭 N)
    hRf (stageResidueCocone A 𝔭 ψ N).ι (isColimitStageResidueCocone A 𝔭 ψ N) εf
  have hDf : ∀ j, IsAffine ((𝒯).obj (Df.obj j)) := fun j =>
    inferInstanceAs (IsAffine (Spec ((stageResidueDiagram A 𝔭 N).obj j.unop)))
  let ρN : ∀ j : StageTail A N, N.1 →+* (stagePrime A 𝔭 j.1).ResidueField := fun j =>
    (algebraMap j.1.1 _).comp (Subalgebra.inclusion j.2).toRingHom
  let τf : ∀ j, Df.obj j ⟶ D.obj (op N) := fun j =>
    integerSiteMap B hZ (hRf j.unop) (hRd N) (Spec.map (CommRingCat.ofHom (ρN j.unop)))
  have hτf : ∀ {i j : (StageTail A N)ᵒᵖ} (e : i ⟶ j), Df.map e ≫ τf j = τf i := by
    intro i j e
    refine (integerSiteMap_comp _ _).trans ?_
    congr 1
    exact spec_map_comp_eq_of_comp_eq _ _ _ (CommRingCat.hom_ext (RingHom.ext fun x =>
      stageResidueMap_algebraMap A 𝔭 (leOfHom e.unop) _))
  have hwf : ∀ j, cf.π.app j ≫ τf j = kK ≫ cn.π.app (op N) := by
    intro j
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change (𝟙 _ ≫ Spec.map ((stageResidueCocone A 𝔭 ψ N).ι.app j.unop)) ≫
        Spec.map (CommRingCat.ofHom (ρN j.unop)) =
      Spec.map (CommRingCat.ofHom κR) ≫ 𝟙 _ ≫ Spec.map ((fgSubringCocone A).ι.app N)
    rw [Category.id_comp, Category.id_comp]
    refine (spec_map_comp_eq_of_comp_eq _ _ _ rfl).trans
      ((spec_map_comp_eq_of_comp_eq _ _ _ (CommRingCat.hom_ext (RingHom.ext fun x => ?_))).symm)
    change ψ (algebraMap A 𝔭.ResidueField (x : A)) =
      ψ (stageResidueToResidue A 𝔭 j.unop.1 (algebraMap j.unop.1.1
        (stagePrime A 𝔭 j.unop.1).ResidueField (Subalgebra.inclusion j.unop.2 x)))
    rw [stageResidueToResidue_algebraMap]
    rfl
  have hKa := isAlgebraicSpace_yoneda B integerBase hZ (integerSiteObject B hZ hK)
  have hFa := isAlgebraicSpace_yoneda B integerBase hZ F
  let l : StageTail A N := ⟨N, le_rfl⟩
  have sqPf : IsPullback (iX ≫ q₁) (yoneda.map tX) f₁
      (yoneda.map (cf.π.app (op l) ≫ τf (op l))) := by
    have h := hiX.paste_horiz sq₁
    convert h using 1
    exact (congrArg yoneda.map (hwf (op l))).trans (Functor.map_comp _ _ _)
  have hY₀ : B.Contains Y₀ := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact pY₀ hK
  let yp := integerSiteMap B hZ hY₀ hK pY₀
  let h₀O : F ⟶ integerSiteObject B hZ hY₀ := Over.homMk (ObjectProperty.homMk h₀)
    (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))
  have hh₀O : h₀O ≫ yp = tX := Over.OverMorphism.ext (ObjectProperty.hom_ext _ hh₀)
  have hYa := isAlgebraicSpace_yoneda B integerBase hZ (integerSiteObject B hZ hY₀)
  have : Flat pY₀ := flat_of_target_spec_field pY₀
  have : IsNoetherianRing K := inferInstance
  have hfpY : FinitePresentation pY₀ := finitePresentation_of_finiteType pY₀
  have hyfl : Space.IsFlat B integerBase hZ (yoneda.map yp) :=
    Space.isFlat_yoneda_map B integerBase hZ yp (inferInstanceAs (Flat pY₀))
  have hypr : Space.IsProper B integerBase hZ (yoneda.map yp) :=
    Space.isProper_yoneda_map B integerBase hZ yp (inferInstanceAs (IsProper pY₀))
  have hyfp : Space.IsFinitePresentation B integerBase hZ (yoneda.map yp) :=
    Space.isFinitePresentation_yoneda_map B integerBase hZ yp hfpY
  have hyd : Space.HasRelativeDimensionLE 1 B integerBase hZ (yoneda.map yp) := by
    have : LocallyOfFiniteType yp.left.hom := inferInstanceAs (LocallyOfFiniteType pY₀)
    refine Space.relativeDimensionLE_yoneda_of_fiberDimension_le B integerBase hZ yp 1
      fun y => ?_
    exact (topologicalKrullDim_fiber_le pY₀ y).trans (by exact_mod_cast hdimY)
  have hcP : yoneda.map h₀O ≫ yoneda.map yp = yoneda.map tX := by
    rw [← Functor.map_comp, hh₀O]
  obtain ⟨M, XM, YM, fM, gM, pM, qXM, qYM, cM, hXM, hYM, sqXM, hflM, hprM, hfpM, hdM, hcM,
      sqqXM, hqXMp, sqqYM, hcomp⟩ :=
    Space.exists_stage_family_hom Df hDf cf hcf τf hτf hX₁ hFa hYa f₁ hfp₁ (yoneda.map tX)
      (iX ≫ q₁) l sqPf (yoneda.map yp) hyfl hypr hyfp hyd (yoneda.map h₀O) hcP
  let κ₀ := (stagePrime A 𝔭 M.unop.1).ResidueField
  have hκ₀ : B.Contains (Spec (.of κ₀)) := hRf M.unop
  let φκ : κ₀ →+* K := ψ.toRingHom.comp (stageResidueToResidue A 𝔭 M.unop.1)
  let m : integerSiteObject B hZ hK ⟶ integerSiteObject B hZ hκ₀ := cf.π.app M
  have hmmap : (𝒯).map m = Spec.map (CommRingCat.ofHom φκ) := by
    change 𝟙 _ ≫ Spec.map ((stageResidueCocone A 𝔭 ψ N).ι.app M.unop) = _
    rw [Category.id_comp]
    rfl
  let := φκ.toAlgebra
  have hmfl : Flat ((𝒯).map m) := by
    rw [hmmap]
    exact Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Nonempty ((𝒯).obj (integerSiteObject B hZ hK)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum K))
  have : Subsingleton ((𝒯).obj (integerSiteObject B hZ hκ₀)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum κ₀))
  have hmsu : Surjective ((𝒯).map m) :=
    (AlgebraicGeometry.surjective_iff _).2 (Function.surjective_to_subsingleton _)
  have : IsAffine ((𝒯).obj (integerSiteObject B hZ hK)) := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine ((𝒯).obj (integerSiteObject B hZ hκ₀)) := inferInstanceAs (IsAffine (Spec _))
  have hm : Space.IsFpqcCovering B integerBase hZ (fun _ : Unit => yoneda.map m) :=
    Space.isFpqcCovering_of_isQuasiCompact_of_isFlat_of_isSurjective B integerBase hZ
      (X := schemeSpace (integerSiteObject B hZ hK))
      (Y := schemeSpace (integerSiteObject B hZ hκ₀))
      (ObjectProperty.homMk (yoneda.map m))
      (Space.isQuasiCompact_yoneda_map_of_isAffineHom B integerBase hZ m
        (_root_.AlgebraicGeometry.isAffineHom_of_isAffine _))
      (Space.isFlat_yoneda_map B integerBase hZ m hmfl)
      (Space.isSurjective_yoneda_map B integerBase hZ m hmsu)
  obtain ⟨hflXM, hprXM, hfpXM⟩ := Space.isFlat_isProper_isFinitePresentation_of_isPullback B
    integerBase hZ sqXM hX₁ hXM hflN hprN hfp₁
  have hR' : IsZero (firstDirectImageStructureSheaf ((𝒯).map h₀O)) :=
    (isZero_firstDirectImageStructureSheaf_iff h₀).2 hR1
  let R := M.unop.1.1
  have := hft M.unop.1
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have hG : IsGRing (Localization.AtPrime (stagePrime A 𝔭 M.unop.1)) :=
    isGRing_of_essFiniteType (R := ℤ) isGRing_basic_examples.{0, 0}.2.2.1
  let eM : op M.unop.1 ⟶ op N := (homOfLE M.unop.2).op
  have hX' := isAlgebraicSpace_pullback B integerBase hZ f₁ (yoneda.map (D.map eM)) hX₁ (hTa _)
    (hTa _)
  obtain ⟨hflX', hprX', hfpX'⟩ := Space.isFlat_isProper_isFinitePresentation_of_isPullback B
    integerBase hZ (IsPullback.of_hasPullback f₁ (yoneda.map (D.map eM))) hX₁ hX' hflN hprN hfp₁
  let k' : integerSiteObject B hZ hκ₀ ⟶ D.obj (op M.unop.1) :=
    integerSiteMap B hZ hκ₀ (hRd M.unop.1) (Spec.map (CommRingCat.ofHom
      ((RingEquiv.refl κ₀).toRingHom.comp (algebraMap R (stagePrime A 𝔭 M.unop.1).ResidueField))))
  have hτk : τf M = k' ≫ D.map eM := Over.OverMorphism.ext <| ObjectProperty.hom_ext _ <|
    (spec_map_comp_eq_of_comp_eq ((fgSubringDiagram A).map eM.unop)
      (CommRingCat.ofHom ((RingEquiv.refl κ₀).toRingHom.comp
        (algebraMap R (stagePrime A 𝔭 M.unop.1).ResidueField)))
      (CommRingCat.ofHom (ρN M.unop)) (CommRingCat.hom_ext (RingHom.ext fun _ => rfl))).symm
  have hτk' : yoneda.map (τf M) = yoneda.map k' ≫ yoneda.map (D.map eM) :=
    (congrArg yoneda.map hτk).trans (Functor.map_comp _ _ _)
  let ψXM : XM ⟶ pullback f₁ (yoneda.map (D.map eM)) :=
    pullback.lift pM (fM ≫ yoneda.map k')
      (sqXM.w.trans ((congrArg (fM ≫ ·) hτk').trans (Category.assoc _ _ _).symm))
  have sqXM' : IsPullback ψXM fM (pullback.snd f₁ (yoneda.map (D.map eM))) (yoneda.map k') := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback f₁ (yoneda.map (D.map eM)))
    rw [pullback.lift_fst]
    exact (congrArg (IsPullback pM fM f₁) hτk').mp sqXM
  obtain ⟨qq, sqX, hqq1, hqq2⟩ : ∃ qq : X ⟶ pullback f₁ (yoneda.map (D.map eM)),
      IsPullback qq f (pullback.snd f₁ (yoneda.map (D.map eM)))
        (yoneda.map (cn.π.app (op M.unop.1))) ∧ qq ≫ pullback.fst _ _ = q₁ ∧
        qq ≫ pullback.snd _ _ = f ≫ yoneda.map (cn.π.app (op M.unop.1)) :=
    ⟨_, Space.isPullback_lift_cone cn eM sq₁, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hkm : kK ≫ cn.π.app (op M.unop.1) = m ≫ k' := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom κR) ≫ 𝟙 _ ≫ Spec.map ((fgSubringCocone A).ι.app M.unop.1) =
      (𝟙 _ ≫ Spec.map ((stageResidueCocone A 𝔭 ψ N).ι.app M.unop)) ≫ Spec.map (CommRingCat.ofHom
        ((RingEquiv.refl κ₀).toRingHom.comp (algebraMap R (stagePrime A 𝔭 M.unop.1).ResidueField)))
    rw [Category.id_comp, Category.id_comp]
    refine (spec_map_comp_eq_of_comp_eq _ _ _ rfl).trans
      ((spec_map_comp_eq_of_comp_eq _ _ _ (CommRingCat.hom_ext (RingHom.ext fun x => ?_))).symm)
    exact congrArg ψ (stageResidueToResidue_algebraMap A 𝔭 M.unop.1 x)
  have hkm' : yoneda.map kK ≫ yoneda.map (cn.π.app (op M.unop.1)) =
      yoneda.map m ≫ yoneda.map k' :=
    (Functor.map_comp _ _ _).symm.trans ((congrArg yoneda.map hkm).trans (Functor.map_comp _ _ _))
  have hqq : iX ≫ qq = qXM ≫ ψXM := by
    apply pullback.hom_ext
    · rw [Category.assoc, hqq1, Category.assoc, pullback.lift_fst, hqXMp]
    · rw [Category.assoc, hqq2, Category.assoc, pullback.lift_snd, reassoc_of% hiX.w,
        reassoc_of% sqqXM.w, hkm']
      rfl
  exact hasEtaleLocalExtension_of_residueStage f hiX hdimF yp hyd h₀O hh₀O h0 hR' R (hRd M.unop.1)
    (stagePrime A 𝔭 M.unop.1) hG hκ₀ hX' _ hflX' hprX' hfpX' qq (cn.π.app (op M.unop.1)) sqX m hm
    hkm hXM hYM fM gM hflXM hprXM hfpXM hflM hprM hfpM cM hcM qXM qYM sqqXM sqqYM hcomp ψXM sqXM'
    hqq

end Affine

end AlgebraicGeometry.EtaleLocalContraction

end
