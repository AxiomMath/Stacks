module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AffineTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Module
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Hilbert families over an affine base in an affine scheme

Let `X ⟶ S` be a morphism of affine schemes and `T` an affine `S`-scheme. Then `X ×_S T` is
affine, and a degree-`d` Hilbert family in `X` over `T` is the same as an ideal `J` of the ring
`Γ(X ×_S T)` such that `Γ(X ×_S T) / J` is a finite locally free `Γ(T)`-module of rank `d`.
Under this dictionary base change along a morphism of affine `S`-schemes `T' ⟶ T` is extension
of ideals along `Γ(X ×_S T) ⟶ Γ(X ×_S T')`.

## Main results

* `Stacks.Hilbert.ker_inr_of_isPushout`: in a pushout square of commutative rings whose top
  arrow is surjective with kernel `K`, the bottom arrow has kernel the extension of `K`.
* `Stacks.Hilbert.comap_ideal_top`: pullback of ideal sheaves along a morphism of affine schemes
  is extension of ideals of global sections.
* `Stacks.Hilbert.isFiniteLocallyFreeOfRank_subschemeι_comp_iff`: finite local freeness of a
  closed subscheme of an affine scheme over an affine base, read on global sections.
* `Stacks.Hilbert.affineFamilyEquiv`: Hilbert families over an affine base in an affine scheme
  are ideals of global sections with finite locally free quotient.
* `Stacks.Hilbert.affineFamilyEquiv_baseChange`: base change is extension of ideals.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Hilbert

/-- **Kernels in a pushout square of rings.** If `a : R ⟶ S` is surjective and the square
`a, b, c, e` is a pushout, the kernel of `e : R' ⟶ P` is the extension along `b` of the kernel
of `a`. -/
theorem ker_inr_of_isPushout {R S R' P : CommRingCat.{u}} {a : R ⟶ S} {b : R ⟶ R'} {c : S ⟶ P}
    {e : R' ⟶ P} (h : IsPushout a b c e) (ha : Function.Surjective a) :
    RingHom.ker e.hom = Ideal.map b.hom (RingHom.ker a.hom) := by
  let J := Ideal.map b.hom (RingHom.ker a.hom)
  have hle : RingHom.ker a.hom ≤ RingHom.ker ((Ideal.Quotient.mk J).comp b.hom) := by
    intro x hx
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hx
  let σ : S →+* R' ⧸ J := RingHom.liftOfSurjective a.hom ha ⟨_, hle⟩
  have hσ : a ≫ CommRingCat.ofHom σ = b ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) := by
    ext x
    exact RingHom.liftOfSurjective_comp_apply a.hom ha ⟨_, hle⟩ x
  refine le_antisymm (fun x hx => ?_) ?_
  · have h1 := congrArg (fun φ => φ.hom x) (h.inr_desc _ _ hσ)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
    rw [RingHom.mem_ker.mp hx, map_zero] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1.symm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, ← CommRingCat.comp_apply, ← h.w, CommRingCat.comp_apply,
      RingHom.mem_ker.mp hx, map_zero]

/-- **Pullback of ideal sheaves between affine schemes is extension of ideals.** -/
theorem comap_ideal_top {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (I : Y.IdealSheafData)
    (f : X ⟶ Y) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      Ideal.map f.appTop.hom (I.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
  have : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι
  have hpush := isPushout_appTop_of_isPullback (IsPullback.of_hasPullback f I.subschemeι)
  have hker :=
    ker_inr_of_isPushout hpush.flip (I.subschemeι_app_surjective ⟨⊤, isAffineOpen_top Y⟩)
  have hI : RingHom.ker I.subschemeι.appTop.hom = I.ideal ⟨⊤, isAffineOpen_top Y⟩ :=
    I.ker_subschemeι_app ⟨⊤, isAffineOpen_top Y⟩
  rw [Scheme.IdealSheafData.comap, Scheme.ker_of_isAffine,
    Scheme.IdealSheafData.ofIdealTop_ideal, hker, hI]
  have : homOfLE (le_top : ((⟨⊤, isAffineOpen_top X⟩ : X.affineOpens) : X.Opens) ≤ ⊤) = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [this, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, Ideal.map_id]

/-- **Finite local freeness of a closed subscheme of an affine scheme over an affine base, read
on global sections.** -/
theorem isFiniteLocallyFreeOfRank_subschemeι_comp_iff {Y T : Scheme.{u}} [IsAffine Y] [IsAffine T]
    (π : Y ⟶ T) (I : Y.IdealSheafData) (d : ℕ) :
    letI : Algebra Γ(T, ⊤) Γ(Y, ⊤) := π.appTop.hom.toAlgebra
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (I.subschemeι ≫ π) d ↔
      Module.IsFiniteLocallyFreeOfRank Γ(T, ⊤) (Γ(Y, ⊤) ⧸ I.ideal ⟨⊤, isAffineOpen_top Y⟩) d := by
  let : Algebra Γ(T, ⊤) Γ(Y, ⊤) := π.appTop.hom.toAlgebra
  let : Algebra Γ(T, ⊤) Γ(I.subscheme, ⊤) := (I.subschemeι ≫ π).appTop.hom.toAlgebra
  rw [Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_module_of_isAffine (I.subschemeι ≫ π) d rfl]
  let U : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
  let e : Γ(I.subscheme, ⊤) ≃+* Γ(Y, ⊤) ⧸ I.ideal U :=
    (I.subschemeObjIso U).commRingCatIsoToRingEquiv
  have he : ∀ y : Γ(Y, ⊤), e (I.subschemeι.appTop y) = Ideal.Quotient.mk _ y := by
    intro y
    show e (I.subschemeι.app U y) = _
    rw [I.subschemeι_app U]
    show (I.subschemeObjIso U).hom ((I.subschemeObjIso U).inv _) = _
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
    rfl
  let e' : Γ(I.subscheme, ⊤) ≃ₗ[Γ(T, ⊤)] Γ(Y, ⊤) ⧸ I.ideal U :=
    { e with
      map_smul' := fun r x => by
        show e ((I.subschemeι ≫ π).appTop r * x) = algebraMap Γ(T, ⊤) _ r * e x
        rw [map_mul, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, he]
        rfl }
  exact ⟨fun h => h.of_linearEquiv e', fun h => h.of_linearEquiv e'.symm⟩

variable {S : Scheme.{u}} [IsAffine S] (X : Over S) [IsAffine X.left] (d : ℕ)

/-- If `X` and `T` are affine `S`-schemes, the fibre product `X ×_S T` is affine. -/
instance isAffine_pullback_left (T : Over S) [IsAffine T.left] :
    IsAffine ((Over.pullback T.hom).obj X).left :=
  inferInstanceAs (IsAffine (pullback X.hom T.hom))

/-- The structure of `Γ(T)`-algebra on the global sections of `X ×_S T`. -/
abbrev familyAlgebra (T : Over S) :
    Algebra Γ(T.left, ⊤) Γ(((Over.pullback T.hom).obj X).left, ⊤) :=
  (((Over.pullback T.hom).obj X).hom).appTop.hom.toAlgebra

/-- The predicate on ideals of `Γ(X ×_S T)` describing Hilbert families. -/
def IsFamilyIdeal (T : Over S) (J : Ideal Γ(((Over.pullback T.hom).obj X).left, ⊤)) : Prop :=
  letI := familyAlgebra X T
  Module.IsFiniteLocallyFreeOfRank Γ(T.left, ⊤) (Γ(((Over.pullback T.hom).obj X).left, ⊤) ⧸ J) d

/-- **Hilbert families over an affine base in an affine scheme are ideals of global sections
with finite locally free quotient of rank `d`.** -/
def affineFamilyEquiv (T : Over S) [IsAffine T.left] :
    HilbertFamily X T d ≃ {J : Ideal Γ(((Over.pullback T.hom).obj X).left, ⊤) //
      IsFamilyIdeal X d T J} where
  toFun Z := ⟨Z.ideal.ideal ⟨⊤, isAffineOpen_top _⟩,
    (isFiniteLocallyFreeOfRank_subschemeι_comp_iff _ Z.ideal d).mp Z.isFiniteLocallyFreeOfRank⟩
  invFun J := ⟨Scheme.IdealSheafData.equivOfIsAffine.symm J.1, by
    refine (isFiniteLocallyFreeOfRank_subschemeι_comp_iff _ _ d).mpr ?_
    have : (Scheme.IdealSheafData.equivOfIsAffine.symm J.1).ideal ⟨⊤, isAffineOpen_top _⟩ =
        J.1 := Scheme.IdealSheafData.equivOfIsAffine.apply_symm_apply J.1
    rw [this]
    exact J.2⟩
  left_inv Z := HilbertFamily.ext (Scheme.IdealSheafData.equivOfIsAffine.symm_apply_apply _)
  right_inv J := Subtype.ext (Scheme.IdealSheafData.equivOfIsAffine.apply_symm_apply J.1)

/-- The ideal attached by `affineFamilyEquiv` to a Hilbert family `Z` is the ideal of global
sections of the ideal sheaf of `Z`. -/
theorem affineFamilyEquiv_apply_coe (T : Over S) [IsAffine T.left] (Z : HilbertFamily X T d) :
    (affineFamilyEquiv X d T Z).1 = Z.ideal.ideal ⟨⊤, isAffineOpen_top _⟩ :=
  rfl

/-- **Base change of Hilbert families between affine bases is extension of ideals.** -/
theorem affineFamilyEquiv_baseChange {T' T : Over S} [IsAffine T.left] [IsAffine T'.left]
    (g : T' ⟶ T) (Z : HilbertFamily X T d) :
    (affineFamilyEquiv X d T' (baseChange X g Z)).1 =
      Ideal.map (familyBaseChangeMap X g).appTop.hom (affineFamilyEquiv X d T Z).1 := by
  rw [affineFamilyEquiv_apply_coe, affineFamilyEquiv_apply_coe, baseChange_ideal,
    comap_ideal_top]

end Stacks.Hilbert

end
