module

public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.Data.Int.Interval
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Flat.Basic
public import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.PseudoCoherent.Characterization
public import StacksFrontier.Homology.TorAmplitude.FlatRepresentative
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Permanence properties of perfect objects of the derived category of a ring

Let `R` be a ring and let `D(R)` be the derived category of `R`-modules. This module records the
permanence properties of the perfect objects of `D(R)`, in the sense of
`StacksDraft.Perfect.IsPerfect`: perfectness is invariant under isomorphism and shift, it is a
two-out-of-three property along a distinguished triangle, a bounded complex of perfect modules
represents a perfect object, and a bounded object all of whose cohomology modules are perfect is
itself perfect.

## Main definitions

* `StacksDraft.Perfect.HasFlatRepresentative`: finite Tor dimension in a prescribed interval,
  expressed by the existence of a bounded complex of flat modules representing the object.

## Main results

* `StacksDraft.Perfect.isPerfect_of_distinguished` ([stacks 066R]): if two of the three objects of
  a distinguished triangle in `D(R)` are perfect, so is the third.
* `StacksDraft.Perfect.isPerfect_of_bounded_of_isPerfectModule` ([stacks 066T]): a bounded complex
  of perfect modules represents a perfect object.
* `StacksDraft.Perfect.isPerfect_of_bounded_of_cohomology_isPerfect` ([stacks 066U]): a bounded
  object of `D(R)` whose cohomology modules are all perfect is perfect.
* `StacksDraft.Perfect.isPerfect_of_biproduct` ([stacks 066S]): both summands of a perfect binary
  biproduct in `D(R)` are perfect.
* `StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension` ([stacks 0658]): an
  object of `D(R)` is perfect exactly when it is pseudo-coherent and of finite Tor dimension, and a
  pseudo-coherent object of Tor amplitude in `[a, b]` has a finite-projective representative
  concentrated in those degrees.
* `StacksDraft.Perfect.cokernel_flat_of_hasFlatRepresentative`: a bounded above complex of flat
  modules with a flat representative supported in `[a, b]` has flat cokernel in degree `a`.

## Implementation notes

Finite Tor dimension is recorded by `HasFlatRepresentative`, the existence of a bounded flat
representative; by [stacks 0654] this is precisely Tor amplitude in the given interval, and unlike
the derived-tensor formulation it makes sense when the carrier universe of the modules is
independent of the universe of the ring.

A quasi-isomorphism is always represented by an isomorphism in the derived category, and since
`Iso` is data rather than a proposition the existential statements record `Nonempty` of it. The
two-out-of-three statement, whose source asserts three conclusions at once, is expressed as the
conjunction of its three directional implications.

For the summands of a perfect biproduct the two conclusions of the source are expressed as a
conjunction. When the carrier universe of the modules is independent of the universe of the ring,
the terms of a bounded finite-projective representative are supported on a quotient of the ring by
the annihilator of a single finite projective module, and that quotient is small enough to live in
the carrier universe; extension and restriction of coefficients along it reduce the statement to
the case where finite free complements fit in the carrier universe.

Both inductions on a cohomological window proceed by splitting off the top degree: for a complex
this is the stupid truncation triangle relating the complex, its top term placed in that degree,
and the truncation below it; for an object of `D(R)` it is the truncation triangle of the
canonical t-structure.

## References

* [Stacks Project, Tag 0658](https://stacks.math.columbia.edu/tag/0658)
* [Stacks Project, Tag 066R](https://stacks.math.columbia.edu/tag/066R)
* [Stacks Project, Tag 066S](https://stacks.math.columbia.edu/tag/066S)
* [Stacks Project, Tag 066T](https://stacks.math.columbia.edu/tag/066T)
* [Stacks Project, Tag 066U](https://stacks.math.columbia.edu/tag/066U)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

/-- A flat representative supported in `[a, b]`. By [stacks 0654] this is precisely Tor
amplitude in `[a, b]`; this form also applies when the module carrier has a universe
independent of the universe of the ring. -/
def HasFlatRepresentative {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (a b : ℤ) : Prop :=
  ∃ E : CochainComplex (ModuleCat.{max u v} R) ℤ,
    (∀ i : ℤ, Module.Flat R (E.X i)) ∧ E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧
      Nonempty (K ≅ DerivedCategory.Q.obj E)

/-! ### Invariance of perfectness under isomorphism and shift -/

/-- Perfectness is invariant under isomorphism in the derived category. -/
private lemma isPerfect_of_iso {R : Type u} [Ring R]
    {X Y : DerivedCategory (ModuleCat.{v} R)} (e : X ≅ Y) (h : IsPerfect Y) :
    IsPerfect X := by
  obtain ⟨P, a, b, ha, hb, hf, hp, ⟨e'⟩⟩ := h
  exact ⟨P, a, b, ha, hb, hf, hp, ⟨e ≪≫ e'⟩⟩

/-- Perfectness is invariant under shift: shift a bounded finite projective representative. -/
private lemma isPerfect_shift {R : Type u} [Ring R]
    (X : DerivedCategory (ModuleCat.{v} R)) (n : ℤ) (h : IsPerfect X) :
    IsPerfect (X⟦n⟧) := by
  obtain ⟨P, a, b, ha, hb, hf, hp, ⟨e⟩⟩ := h
  let P' := (shiftFunctor (CochainComplex (ModuleCat.{v} R) ℤ) n).obj P
  refine ⟨P', a - n, b - n, ?_, ?_, ?_, ?_, ?_⟩
  · exact P.isStrictlyGE_shift a n (a - n) (by omega)
  · exact P.isStrictlyLE_shift b n (b - n) (by omega)
  · intro i
    dsimp [P']
    exact hf _
  · intro i
    dsimp [P']
    exact hp _
  · exact ⟨(shiftFunctor (DerivedCategory (ModuleCat.{v} R)) n).mapIso e ≪≫
      (DerivedCategory.Q.commShiftIso n).symm.app P⟩

/-! ### Perfect complexes in distinguished triangles -/

/-- The mapping cone of a map of bounded complexes of finite projective modules is again a bounded
complex of finite projective modules, hence perfect. -/
private lemma cone_perfect {R : Type u} [Ring R]
    {P₁ P₂ : CochainComplex (ModuleCat.{v} R) ℤ} (f : P₁ ⟶ P₂)
    (a₁ b₁ a₂ b₂ : ℤ)
    (hge₁ : P₁.IsStrictlyGE a₁) (hle₁ : P₁.IsStrictlyLE b₁)
    (hge₂ : P₂.IsStrictlyGE a₂) (hle₂ : P₂.IsStrictlyLE b₂)
    (hf₁ : ∀ i, Module.Finite R (P₁.X i))
    (hp₁ : ∀ i, Module.Projective R (P₁.X i))
    (hf₂ : ∀ i, Module.Finite R (P₂.X i))
    (hp₂ : ∀ i, Module.Projective R (P₂.X i)) :
    IsPerfect (DerivedCategory.Q.obj (CochainComplex.mappingCone f)) := by
  let _ := hge₁
  let _ := hle₁
  let _ := hge₂
  let _ := hle₂
  let _ (i : ℤ) := hp₁ i
  let _ (i : ℤ) := hp₂ i
  refine ⟨_, min (a₁ - 1) a₂, max (b₁ - 1) b₂,
    CochainComplex.isStrictlyGE_mappingCone f a₁ a₂ _, ?_, ?_, ?_, ⟨Iso.refl _⟩⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨P₁.isZero_of_isStrictlyLE b₁ _ (by omega),
      P₂.isZero_of_isStrictlyLE b₂ _ (by omega)⟩
  · intro i
    let _ := hf₁ (i + 1)
    let _ := hf₂ i
    show Module.Finite R
      (HomologicalComplex.homotopyCofiber.X (C := ModuleCat.{v} R) f i)
    rw [Module.Finite.equiv_iff
      (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) (by simp)).toLinearEquiv]
    rw [Module.Finite.equiv_iff (ModuleCat.biprodIsoProd _ _).toLinearEquiv]
    infer_instance
  · intro i
    let _ : Module.Projective R (↑(P₁.X (i + 1)) × ↑(P₂.X i)) := inferInstance
    let _ : Module.Projective R ↑(P₁.X (i + 1) ⊞ P₂.X i) :=
      Module.Projective.of_equiv (ModuleCat.biprodIsoProd _ _).symm.toLinearEquiv
    show Module.Projective R
      (HomologicalComplex.homotopyCofiber.X (C := ModuleCat.{v} R) f i)
    exact Module.Projective.of_equiv
      (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) (by simp)).symm.toLinearEquiv

/-- If the first two objects of a distinguished triangle are perfect, so is the third: realize the
first morphism by a map of bounded complexes of finite projective modules, using that the chosen
representative of the first object is K-projective, and identify the third object with the mapping
cone of that map. -/
private lemma perfect_obj₃ {R : Type u} [Ring R]
    (T : Triangle (DerivedCategory (ModuleCat.{v} R)))
    (hT : T ∈ distinguishedTriangles)
    (h₁ : IsPerfect T.obj₁) (h₂ : IsPerfect T.obj₂) :
    IsPerfect T.obj₃ := by
  obtain ⟨P₁, a₁, b₁, hge₁, hle₁, hf₁, hp₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨P₂, a₂, b₂, hge₂, hle₂, hf₂, hp₂, ⟨e₂⟩⟩ := h₂
  let _ := hle₁
  let _ (i : ℤ) := hp₁ i
  let _ : P₁.IsKProjective := CochainComplex.isKProjective_of_projective P₁ b₁
  let q := HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)
  let qiso := DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)
  let g : DerivedCategory.Qh.obj (q.obj P₁) ⟶ DerivedCategory.Qh.obj (q.obj P₂) :=
    qiso.hom.app P₁ ≫ e₁.inv ≫ T.mor₁ ≫ e₂.hom ≫ qiso.inv.app P₂
  obtain ⟨g', hg'⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P₁ (q.obj P₂)).2 g
  obtain ⟨f, rfl⟩ := q.map_surjective g'
  have hf : DerivedCategory.Q.map f = e₁.inv ≫ T.mor₁ ≫ e₂.hom := by
    apply (cancel_epi (qiso.hom.app P₁)).1
    rw [← qiso.hom.naturality f]
    show DerivedCategory.Qh.map (q.map f) ≫ qiso.hom.app P₂ = _
    rw [hg']
    simp [g, Category.assoc]
  obtain ⟨C, a, b, hge, hle, hfin, hproj, ⟨ec⟩⟩ :=
    cone_perfect f a₁ b₁ a₂ b₂ hge₁ hle₁ hge₂ hle₂ hf₁ hp₁ hf₂ hp₂
  exact ⟨C, a, b, hge, hle, hfin, hproj, ⟨
    (Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T
      (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)) hT
      (DerivedCategory.mappingCone_triangle_distinguished f) e₁ e₂ (by
          show T.mor₁ ≫ e₂.hom = e₁.hom ≫ DerivedCategory.Q.map f
          rw [hf]
          simp))).trans ec⟩⟩

/-- **Stacks 066R.** In a distinguished triangle in `D(R)`, if two of the three objects are
perfect, then so is the third. -/
@[stacks 066R]
theorem isPerfect_of_distinguished
    {R : Type u} [Ring R]
    (T : Triangle (DerivedCategory (ModuleCat.{v} R)))
    (hT : T ∈ distinguishedTriangles) :
    (IsPerfect T.obj₁ → IsPerfect T.obj₂ → IsPerfect T.obj₃) ∧
    (IsPerfect T.obj₁ → IsPerfect T.obj₃ → IsPerfect T.obj₂) ∧
    (IsPerfect T.obj₂ → IsPerfect T.obj₃ → IsPerfect T.obj₁) := by
  refine ⟨perfect_obj₃ T hT, fun h₁ h₃ => ?_, fun h₂ h₃ => ?_⟩
  · exact perfect_obj₃ T.invRotate (inv_rot_of_distTriang T hT)
      (isPerfect_shift T.obj₃ (-1) h₃) h₁
  · exact isPerfect_of_iso (shiftShiftNeg T.obj₁ 1).symm (isPerfect_shift (T.obj₁⟦(1 : ℤ)⟧) (-1)
      (perfect_obj₃ T.rotate (rot_of_distTriang T hT) h₂ h₃))

/-! ### Bounded complexes of perfect modules -/

section BoundedPerfectModules

open ComplexShape HomologicalComplex

/-- A perfect module placed in any single degree gives a perfect object. -/
private lemma isPerfect_singleFunctor_obj {R : Type u} [CommRing R]
    (M : ModuleCat.{v} R) (hM : IsPerfectModule (R := R) M) (i : ℤ) :
    IsPerfect ((DerivedCategory.singleFunctor (ModuleCat.{v} R) i).obj M) := by
  apply isPerfect_of_iso
    (((DerivedCategory.singleFunctors (ModuleCat.{v} R)).shiftIso (-i) i 0
      (by omega)).app M).symm
  exact isPerfect_shift _ (-i) hM


/-- Induction on the width of the supporting window: a complex of perfect modules supported in
`[a, a + n]` is perfect, by splitting off its top term. -/
private lemma isPerfect_of_bounded {R : Type u} [CommRing R] (a : ℤ) (n : ℕ) :
    ∀ (b : ℤ), a + n = b → ∀ (L : CochainComplex (ModuleCat.{v} R) ℤ)
      [L.IsStrictlyGE a] [L.IsStrictlyLE b],
      (∀ i : ℤ, a ≤ i → i ≤ b → IsPerfectModule (R := R) (L.X i)) →
      IsPerfect (DerivedCategory.Q.obj L) := by
  induction n with
  | zero =>
      intro b hb L hge hle hL
      obtain rfl : a = b := by omega
      obtain ⟨M, ⟨e⟩⟩ := CochainComplex.exists_iso_single L a
      apply isPerfect_of_iso (DerivedCategory.Q.mapIso e ≪≫
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{v} R) a).app M).symm)
      exact isPerfect_singleFunctor_obj M
        (isPerfect_of_iso ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).mapIso
          ((HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.up ℤ) a).mapIso e ≪≫
            HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a M)).symm
          (hL a le_rfl le_rfl)) a
  | succ n ih =>
      intro b hb L hge hle hL
      obtain ⟨f, g, h, hT⟩ := DerivedCategory.exists_distTriang_singleFunctor_obj_X_stupidTrunc L b
      apply (isPerfect_of_distinguished (Triangle.mk f g h) hT).2.1
      · exact isPerfect_singleFunctor_obj _ (hL b (by omega) le_rfl) b
      · exact ih (b - 1) (by omega) _ (fun i hi hi' => by
          show IsPerfect
            ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj
              ((L.stupidTrunc (embeddingUpIntLE (b - 1))).X i))
          exact isPerfect_of_iso ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).mapIso
            (L.stupidTruncXIso _ (DerivedCategory.embeddingUpIntLE_f_toNat (b - 1) i hi')))
            (hL i hi (by omega)))

/-- **Stacks 066T.** A bounded complex of perfect modules over a ring represents a perfect object
of the derived category. -/
@[stacks 066T]
theorem isPerfect_of_bounded_of_isPerfectModule
    {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (hK : ∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b)
    (hP : ∀ i : ℤ, IsPerfectModule (R := R) (K.X i)) :
    IsPerfect (DerivedCategory.Q.obj K) := by
  obtain ⟨a, b, hge, hle⟩ := hK
  have : K.IsStrictlyLE (max a b) := K.isStrictlyLE_of_le b _ (le_max_right a b)
  exact isPerfect_of_bounded a (max a b - a).toNat (max a b) (by omega) K fun i _ _ => hP i

end BoundedPerfectModules

/-! ### Perfectness from perfect cohomology -/

/-- An object concentrated in a single degree with perfect cohomology there is perfect. -/
private lemma perfect_of_single_cohomology {R : Type u} [Ring R]
    (X : DerivedCategory (ModuleCat.{v} R)) (n : ℤ) [X.IsGE n] [X.IsLE n]
    (h : IsPerfectModule (R := R)
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj X)) :
    IsPerfect X := by
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  let eH : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj X ≅ Y :=
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} R) n).app Y
  exact isPerfect_of_iso
    (e ≪≫ (DerivedCategory.singleFunctor (ModuleCat.{v} R) n).mapIso eH.symm ≪≫
      ((DerivedCategory.singleFunctors (ModuleCat.{v} R)).shiftIso (-n) n 0 (by simp)).symm.app _)
    (isPerfect_shift _ (-n) h)

/-- If the third object of a distinguished triangle has vanishing cohomology in degrees `i` and
`i - 1`, then the first morphism is an isomorphism on cohomology in degree `i`. -/
private lemma isIso_homology_mor₁ {R : Type u} [Ring R]
    (T : Triangle (DerivedCategory (ModuleCat.{v} R))) (hT : T ∈ distinguishedTriangles)
    (i : ℤ)
    (h₀ : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj T.obj₃))
    (h₁ : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i - 1)).obj T.obj₃)) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map T.mor₁) := by
  have : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map T.mor₁) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).2 (h₀.eq_of_tgt _ _)
  have : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map T.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by omega)).2
      (h₁.eq_of_src _ _)
  exact isIso_of_mono_of_epi _

/-- If the first object of a distinguished triangle has vanishing cohomology in degrees `i` and
`i + 1`, then the second morphism is an isomorphism on cohomology in degree `i`. -/
private lemma isIso_homology_mor₂ {R : Type u} [Ring R]
    (T : Triangle (DerivedCategory (ModuleCat.{v} R))) (hT : T ∈ distinguishedTriangles)
    (i : ℤ)
    (h₀ : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj T.obj₁))
    (h₁ : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i + 1)).obj T.obj₁)) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map T.mor₂) := by
  have : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map T.mor₂) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT i).2 (h₀.eq_of_src _ _)
  have : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map T.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT i (i + 1) (by omega)).2
      (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- Induction on the width of the supporting window for the canonical t-structure: an object with
cohomology concentrated in `[a, a + n]` and perfect there is perfect, by cutting it with the
truncation triangle at the top of the window. -/
private lemma perfect_interval {R : Type u} [CommRing R] (a : ℤ) (n : ℕ)
    (K : DerivedCategory (ModuleCat.{v} R)) [K.IsGE a] [K.IsLE (a + n)]
    (hH : ∀ i : ℤ, a ≤ i → i ≤ a + n →
      IsPerfectModule (R := R)
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) :
    IsPerfect K := by
  induction n generalizing K with
  | zero =>
      have : K.IsLE a := DerivedCategory.TStructure.t.isLE_of_le K (a + (0 : ℕ)) a (by omega)
      exact perfect_of_single_cohomology K a (hH a le_rfl (by omega))
  | succ n ih =>
      let b : ℤ := a + (n + 1 : ℕ)
      let T := (DerivedCategory.TStructure.t.triangleLTGE b).obj K
      have hT : T ∈ distinguishedTriangles :=
        DerivedCategory.TStructure.t.triangleLTGE_distinguished b K
      have : K.IsLE b := by
        dsimp [b]
        assumption
      have : T.obj₁.IsGE a := by
        show DerivedCategory.TStructure.t.IsGE
          ((DerivedCategory.TStructure.t.truncLT b).obj K) a
        infer_instance
      have : T.obj₁.IsLE (a + n) := by
        show DerivedCategory.TStructure.t.IsLE
          ((DerivedCategory.TStructure.t.truncLT b).obj K) (a + n)
        exact DerivedCategory.TStructure.t.isLE_truncLT_obj K b (a + n) (by dsimp [b]; omega)
      have : T.obj₃.IsLE b := by
        show DerivedCategory.TStructure.t.IsLE
          ((DerivedCategory.TStructure.t.truncGE b).obj K) b
        infer_instance
      have hleft : IsPerfect T.obj₁ := by
        apply ih T.obj₁
        intro i hai hia
        have hzi : IsZero
            ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj T.obj₃) :=
          DerivedCategory.isZero_of_isGE T.obj₃ b i (by omega)
        have hzim : IsZero
            ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i - 1)).obj T.obj₃) :=
          DerivedCategory.isZero_of_isGE T.obj₃ b (i - 1) (by omega)
        have := isIso_homology_mor₁ T hT i hzi hzim
        exact isPerfect_of_iso ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).mapIso
          (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map T.mor₁)))
          (hH i hai (by omega))
      have hright : IsPerfect T.obj₃ := by
        have hz : IsZero
            ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) b).obj T.obj₁) :=
          DerivedCategory.isZero_of_isLE T.obj₁ (b - 1) b (by omega)
        have hz' : IsZero
            ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (b + 1)).obj T.obj₁) :=
          DerivedCategory.isZero_of_isLE T.obj₁ (b - 1) (b + 1) (by omega)
        have := isIso_homology_mor₂ T hT b hz hz'
        apply perfect_of_single_cohomology T.obj₃ b
        exact isPerfect_of_iso ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).mapIso
          (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) b).map T.mor₂)).symm)
          (hH b (by omega) (by omega))
      exact (isPerfect_of_distinguished T hT).2.1 hleft hright

/-- **Stacks 066U.** A bounded object of the derived category of modules whose cohomology modules
are all perfect is itself perfect. -/
@[stacks 066U, sga "6 I 4.15" "special case"]
theorem isPerfect_of_bounded_of_cohomology_isPerfect
    {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat.{v} R))
    (hK : (∃ a : ℤ, K.IsGE a) ∧ ∃ b : ℤ, K.IsLE b)
    (hH : ∀ i : ℤ,
      IsPerfectModule (R := R)
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) :
    IsPerfect K := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hK
  by_cases hab : a ≤ b
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
    exact perfect_interval a n K (fun i _ _ => hH i)
  · have : K.IsLE a := DerivedCategory.TStructure.t.isLE_of_le K b a (by omega)
    exact perfect_of_single_cohomology K a (hH a)

/-! ### Perfectness of the summands of a biproduct -/

section BiproductSummands

open scoped TensorProduct
open CategoryTheory.ShortComplex.ShortExact

-- Recognizing the coefficient-extension functor as exact, and its unit as an isomorphism, reads
-- instances through carrier-level identifications of tensor products; this needs the pre-4.x
-- defeq transparency behaviour.
set_option backward.isDefEq.respectTransparency false

/-- A complex supported in `[a, b]` has vanishing terms outside that window. -/
private lemma isZero_X_of_lt_or_lt {R : Type u} [Ring R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ) (a b i : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hi : i < a ∨ b < i) : IsZero (P.X i) := by
  rcases hi with hi | hi
  · exact P.isZero_of_isStrictlyGE a i hi
  · exact P.isZero_of_isStrictlyLE b i hi

/-- A complex with a vanishing term in degree `n` has vanishing cohomology there. -/
private lemma isZero_homology_Q_obj {R : Type u} [Ring R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ) (h : IsZero (P.X n)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj
      (DerivedCategory.Q.obj P)) :=
  (ShortComplex.isZero_homology_of_isZero_X₂ (P.sc n) h).of_iso
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) n).app P)

/-- The canonical truncation of a complex vanishing strictly above `b` again vanishes strictly
above `b`, since the truncation map is an epimorphism in every degree. -/
private lemma truncGE_isStrictlyLE_aux {R : Type u} [Ring R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ) (a b : ℤ) (hP : P.IsStrictlyLE b) :
    (P.truncGE a).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff] at hP ⊢
  intro i hi
  have : Epi ((P.πTruncGE a).f i) := by
    unfold CochainComplex.πTruncGE
    infer_instance
  exact IsZero.of_epi ((P.πTruncGE a).f i) (hP i hi)

private lemma isZero_of_retract {C : Type*} [Category C] [HasZeroMorphisms C] {X Y : C}
    (s : X ⟶ Y) (r : Y ⟶ X) (h : s ≫ r = 𝟙 X) (hY : IsZero Y) : IsZero X := by
  rw [IsZero.iff_id_eq_zero, ← h, hY.eq_zero_of_tgt s, zero_comp]

private lemma termwiseTorAmplitude_of_retract
    {R : Type u} [CommRing R]
    (Q P : CochainComplex (ModuleCat.{v} R) ℤ)
    (bQ bP a b : ℤ) (hQle : Q.IsStrictlyLE bQ) (hPle : P.IsStrictlyLE bP)
    (hQproj : ∀ n, Module.Projective R (Q.X n))
    (hPproj : ∀ n, Module.Projective R (P.X n))
    (s : DerivedCategory.Q.obj Q ⟶ DerivedCategory.Q.obj P)
    (r : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj Q)
    (hsr : s ≫ r = 𝟙 _)
    (hPamp : TorAmplitude.HasTorAmplitudeIn P a b) :
    TorAmplitude.HasTorAmplitudeIn Q a b := by
  let _ := hQle
  let _ := hPle
  let _ (n : ℤ) := hQproj n
  let _ (n : ℤ) := hPproj n
  let _ : Q.IsKProjective := CochainComplex.isKProjective_of_projective Q bQ
  let _ : P.IsKProjective := CochainComplex.isKProjective_of_projective P bP
  let q := HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)
  let qiso := DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)
  let s' : DerivedCategory.Qh.obj (q.obj Q) ⟶ DerivedCategory.Qh.obj (q.obj P) :=
    qiso.hom.app Q ≫ s ≫ qiso.inv.app P
  let r' : DerivedCategory.Qh.obj (q.obj P) ⟶ DerivedCategory.Qh.obj (q.obj Q) :=
    qiso.hom.app P ≫ r ≫ qiso.inv.app Q
  obtain ⟨S, hS⟩ := (CochainComplex.IsKProjective.Qh_map_bijective Q (q.obj P)).2 s'
  obtain ⟨T', hT'⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P (q.obj Q)).2 r'
  have hST : S ≫ T' = 𝟙 _ :=
    (CochainComplex.IsKProjective.Qh_map_bijective Q (q.obj Q)).1 (by
      rw [Functor.map_comp, hS, hT']
      calc
        s' ≫ r' = 𝟙 _ := by
          simp only [s', r', Category.assoc, Iso.inv_hom_id_app_assoc]
          rw [← Category.assoc s r, hsr]
          simp
          rfl
        _ = DerivedCategory.Qh.map (𝟙 _) := by rw [DerivedCategory.Qh.map_id])
  intro M n hn
  let TM := (TorAmplitude.tensorRightMixed M).mapHomotopyCategory (ComplexShape.up ℤ)
  let H := HomotopyCategory.homologyFunctor (ModuleCat.{max u v} R)
    (ComplexShape.up ℤ) n
  have hzero := hPamp M n hn
  have hzero' : IsZero (H.obj (TM.obj (q.obj P))) := hzero.of_iso
    (H.mapIso (((TorAmplitude.tensorRightMixed M).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).app P).symm ≪≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{max u v} R)
        (ComplexShape.up ℤ) n).app _)
  have hzeroQ : IsZero (H.obj (TM.obj (q.obj Q))) :=
    isZero_of_retract (H.map (TM.map S)) (H.map (TM.map T'))
      (by rw [← H.map_comp, ← TM.map_comp, hST, TM.map_id, H.map_id]) hzero'
  let eQ : (TorAmplitude.tensorComplex Q M).homology n ≅ H.obj (TM.obj (q.obj Q)) :=
    ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{max u v} R)
        (ComplexShape.up ℤ) n).app _).symm ≪≫
    H.mapIso (((TorAmplitude.tensorRightMixed M).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).app Q)
  exact hzeroQ.of_iso eQ

private lemma isGE_of_retract
    {R : Type u} [CommRing R]
    (Q P : CochainComplex (ModuleCat.{v} R) ℤ) (a : ℤ)
    (hPge : P.IsStrictlyGE a)
    (s : DerivedCategory.Q.obj Q ⟶ DerivedCategory.Q.obj P)
    (r : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj Q)
    (hsr : s ≫ r = 𝟙 _) : Q.IsGE a := by
  rw [CochainComplex.isGE_iff]
  intro n hn
  let H := DerivedCategory.homologyFunctor (ModuleCat.{v} R) n
  have hPzero : IsZero (H.obj (DerivedCategory.Q.obj P)) :=
    isZero_homology_Q_obj P n (P.isZero_of_isStrictlyGE a n hn)
  have hQzero : IsZero (H.obj (DerivedCategory.Q.obj Q)) :=
    isZero_of_retract (H.map s) (H.map r) (by rw [← H.map_comp, hsr, H.map_id]) hPzero
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact hQzero.of_iso
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) n).app Q).symm

/-- The canonical truncation `Q≥a` of a complex of finite projective modules whose cokernel in
degree `a` is flat again has finite projective terms. -/
private lemma finite_projective_truncGE_X {R : Type u} [CommRing R]
    (Q : CochainComplex (ModuleCat.{v} R) ℤ) (a : ℤ)
    (hfin : ∀ n, Module.Finite R (Q.X n)) (hproj : ∀ n, Module.Projective R (Q.X n))
    (hC : Module.Flat R (cokernel (Q.d (a - 1) a) : ModuleCat.{v} R)) (n : ℤ) :
    Module.Finite R ((Q.truncGE a).X n) ∧ Module.Projective R ((Q.truncGE a).X n) := by
  rcases lt_trichotomy n a with hn | hn | hn
  · have := ModuleCat.isZero_iff_subsingleton.mp ((Q.truncGE a).isZero_of_isStrictlyGE a n hn)
    exact ⟨inferInstance, inferInstance⟩
  · subst n
    let e : (Q.truncGE a).X a ≅ cokernel (Q.d (a - 1) a) := Q.truncGEXIsoOpcycles a ≪≫
      IsColimit.coconePointUniqueUpToIso (Q.opcyclesIsCokernel (a - 1) a (by simp))
        (colimit.isColimit _)
    let _ := hfin (a - 1)
    let _ := hfin a
    let _ := hproj a
    let _ : Module.FinitePresentation R (Q.X a) :=
      Module.finitePresentation_of_projective R (Q.X a)
    have hfpQ : Module.FinitePresentation R
        (Q.X a ⧸ LinearMap.range (Q.d (a - 1) a).hom) :=
      Module.finitePresentation_of_surjective
        (LinearMap.range (Q.d (a - 1) a).hom).mkQ
        (Submodule.mkQ_surjective _)
        (by rw [Submodule.ker_mkQ]; exact Submodule.fg_range _)
    have hfpC : Module.FinitePresentation R
        (cokernel (Q.d (a - 1) a) : ModuleCat.{v} R) :=
      Module.FinitePresentation.of_equiv
        (ModuleCat.cokernelIsoRangeQuotient (Q.d (a - 1) a)).toLinearEquiv.symm
    have hfp : Module.FinitePresentation R ((Q.truncGE a).X a) :=
      Module.FinitePresentation.of_equiv e.toLinearEquiv.symm
    have hf : Module.Flat R ((Q.truncGE a).X a) := Module.Flat.of_linearEquiv e.toLinearEquiv
    exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩
  · let e : (Q.truncGE a).X n ≅ Q.X n := Q.truncGEXIso a n hn
    exact ⟨Module.Finite.equiv e.toLinearEquiv.symm,
      Module.Projective.of_equiv e.toLinearEquiv.symm⟩

private lemma perfect_of_boundedAbove_finiteProjective_of_amplitude
    {R : Type u} [CommRing R]
    (Q : CochainComplex (ModuleCat.{v} R) ℤ) (a bQ b : ℤ)
    (hQle : Q.IsStrictlyLE bQ)
    (hQfin : ∀ n, Module.Finite R (Q.X n))
    (hQproj : ∀ n, Module.Projective R (Q.X n))
    (hQge : Q.IsGE a)
    (hQamp : TorAmplitude.HasTorAmplitudeIn Q a b) :
    IsPerfect (DerivedCategory.Q.obj Q) := by
  let _ := hQge
  have hflat : TorAmplitude.IsComplexOfFlats Q := fun n => by
    let _ : Module.Projective R (Q.X n) := hQproj n
    exact Module.Flat.of_projective
  have hCflat : Module.Flat R (cokernel (Q.d (a - 1) a) : ModuleCat.{v} R) :=
    TorAmplitude.cokernel_flat_of_termwise_torAmplitude Q a b hflat hQamp
  let T := Q.truncGE a
  have hTfinproj := finite_projective_truncGE_X Q a hQfin hQproj hCflat
  refine ⟨T, a, bQ, inferInstance, truncGE_isStrictlyLE_aux Q a bQ hQle, fun n => (hTfinproj n).1,
    fun n => (hTfinproj n).2, ⟨?_⟩⟩
  exact asIso (DerivedCategory.Q.map (Q.πTruncGE a))

private lemma isPerfect_of_retract
    {R : Type u} [CommRing R]
    {X Y : DerivedCategory (ModuleCat.{v} R)}
    (i : X ⟶ Y) (p : Y ⟶ X) (hip : i ≫ p = 𝟙 X)
    (hXpseudo : StacksDraft.PseudoCoherence.IsPseudoCoherent X)
    (hY : IsPerfect Y) : IsPerfect X := by
  obtain ⟨P, a, b, hPge, hPle, hPfin, hPproj, ⟨eP⟩⟩ := hY
  obtain ⟨Q, ⟨bQ, hQle⟩, hQfinproj, ⟨eQ⟩⟩ :=
    StacksDraft.PseudoCoherence.finiteProjectiveRepresentative_of_pseudoCoherent hXpseudo
  let s : DerivedCategory.Q.obj Q ⟶ DerivedCategory.Q.obj P :=
    eQ.hom ≫ i ≫ eP.hom
  let r : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj Q :=
    eP.inv ≫ p ≫ eQ.inv
  have hsr : s ≫ r = 𝟙 _ := by simp [s, r, reassoc_of% hip]
  have hPamp : TorAmplitude.HasTorAmplitudeIn P a b := by
    intro M n hn
    exact ShortComplex.isZero_homology_of_isZero_X₂ _
      ((TorAmplitude.tensorRightMixed M).map_isZero (isZero_X_of_lt_or_lt P a b n hn))
  have hQamp := termwiseTorAmplitude_of_retract Q P bQ b a b hQle hPle
    (fun n => (hQfinproj n).2) hPproj s r hsr hPamp
  have hQge := isGE_of_retract Q P a hPge s r hsr
  obtain ⟨T, c, d, hTge, hTle, hTfin, hTproj, ⟨eT⟩⟩ :=
    perfect_of_boundedAbove_finiteProjective_of_amplitude Q a bQ b hQle
      (fun n => (hQfinproj n).1) (fun n => (hQfinproj n).2) hQge hQamp
  exact ⟨T, c, d, hTge, hTle, hTfin, hTproj, ⟨eQ.symm ≪≫ eT⟩⟩

open CategoryTheory.ShortComplex.ShortExact
open scoped BigOperators TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- The trace ideal of a finite projective module has an idempotent acting as its identity.
Nakayama supplies this element without requiring a finite-free module in the carrier universe. -/
private lemma support_idempotent {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    ∃ e : R, IsIdempotentElem e ∧ (∀ m : M, e • m = m) ∧
      (∀ r : R, (∀ m : M, r • m = 0) → r * e = 0) := by
  classical
  obtain ⟨g, hg⟩ := (inferInstance : Module.Projective R M)
  let I : Ideal R := Ideal.span (Set.range (fun p : M × M => g p.1 p.2))
  have hI : (⊤ : Submodule R M) ≤ I • ⊤ := by
    intro m _
    rw [← hg m, Finsupp.linearCombination_apply]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul
      (Ideal.subset_span (Set.mem_range_self (m, i))) Submodule.mem_top
  obtain ⟨r, hr, hrM⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I
      (⊤ : Submodule R M) Module.Finite.fg_top hI
  let e := 1 - r
  have heI : e ∈ I := by simpa [e, neg_sub] using I.neg_mem hr
  have heM (m : M) : e • m = m := by
    simp [e, sub_smul, hrM m (Submodule.mem_top)]
  have hann (a : R) (ha : ∀ m : M, a • m = 0) (t : R) (ht : t ∈ I) : a * t = 0 := by
    induction ht using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨m, i⟩, rfl⟩ := hx
      have h := congrArg (fun z : M →₀ R => z i) (g.map_smul a m)
      simpa [ha m] using h.symm
    | zero => simp
    | add x y hx hy ihx ihy => simp [mul_add, ihx, ihy]
    | smul b x hx ih => simpa [smul_eq_mul, mul_left_comm a b] using congrArg (b * ·) ih
  refine ⟨e, ?_, heM, fun a ha => hann a ha e heI⟩
  have h := hann (1 - e) (fun m => by simp [sub_smul, heM m]) e heI
  show e * e = e
  rw [sub_mul, one_mul, sub_eq_zero] at h
  exact h.symm

/-- The faithful coefficient quotient embeds in the endomorphisms of the small module.
Its supporting idempotent also splits the quotient map as an `R`-linear map. -/
private lemma small_projective_quotient {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    Small.{v} (R ⧸ Module.annihilator R M) ∧
      Module.Projective R (R ⧸ Module.annihilator R M) := by
  classical
  let I := Module.annihilator R M
  let := Module.quotientAnnihilator (R := R) (M := M)
  have : FaithfulSMul (R ⧸ I) M := by
    constructor
    intro a b hab
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    apply Ideal.Quotient.eq.mpr
    apply Module.mem_annihilator.mpr
    intro m
    change ∀ m : M, a • m = b • m at hab
    simpa [sub_smul] using sub_eq_zero.mpr (hab m)
  refine ⟨small_of_injective (smul_left_injective' (M := R ⧸ I) (α := M)), ?_⟩
  obtain ⟨e, he, heM, heann⟩ := support_idempotent (R := R) M
  let l : R →ₗ[R] R := LinearMap.mulRight R e
  have hIl : I ≤ l.ker := fun a ha => heann a (Module.mem_annihilator.mp ha)
  let i : (R ⧸ I) →ₗ[R] R := I.liftQ l hIl
  have hfi : I.mkQ.comp i = LinearMap.id := by
    apply LinearMap.ext
    intro x
    obtain ⟨a, rfl⟩ := I.mkQ_surjective x
    show Ideal.Quotient.mk I (a * e) = Ideal.Quotient.mk I a
    apply Ideal.Quotient.eq.mpr
    apply Module.mem_annihilator.mpr
    intro m
    simp [sub_smul, mul_smul, heM]
  exact Module.Projective.of_split i I.mkQ hfi

/-- Shrink the faithful quotient while retaining its finite projectivity and linear section. -/
private lemma exists_small_coefficient_ring {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    ∃ (S : Type v) (_ : CommRing S) (_ : Algebra R S),
      Module.Finite R S ∧ Module.Projective R S ∧
      ∃ i : S →ₗ[R] R, (∀ s, algebraMap R S (i s) = s) ∧
        (∀ m : M, (i 1) • m = m) := by
  classical
  let I := Module.annihilator R M
  obtain ⟨hsmall, hproj⟩ := small_projective_quotient (R := R) M
  let := hsmall
  let := hproj
  let S := Shrink.{v} (R ⧸ I)
  let e := Shrink.algEquiv R (R ⧸ I)
  have : Module.Finite R S := Module.Finite.equiv e.toLinearEquiv.symm
  have : Module.Projective R S := Module.Projective.of_equiv e.toLinearEquiv.symm
  have hsurj : Function.Surjective (algebraMap R S) := by
    intro s
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e s)
    exact ⟨r, e.injective ((e.commutes r).trans hr)⟩
  obtain ⟨i, hi⟩ := (Algebra.linearMap R S).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj)
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, i,
    fun s => LinearMap.congr_fun hi s, ?_⟩
  intro m
  have h : i 1 - 1 ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    show algebraMap R (R ⧸ I) (i 1 - 1) = 0
    have h1 := LinearMap.congr_fun hi 1
    change algebraMap R S (i 1) = 1 at h1
    have h2 : algebraMap R (R ⧸ I) (i 1) = 1 :=
      (e.commutes (i 1)).symm.trans ((congrArg e h1).trans e.map_one)
    simpa only [map_sub, map_one] using sub_eq_zero.mpr h2
  have h := Module.mem_annihilator.mp h m
  simpa [sub_smul, sub_eq_zero] using h

private noncomputable def coefficientExtension {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] : ModuleCat.{v} R ⥤ ModuleCat.{v} S where
  obj M := ModuleCat.of S (S ⊗[R] M)
  map f := ModuleCat.ofHom (f.hom.baseChange S)

private instance coefficientExtension_additive {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] :
    (coefficientExtension (R := R) (S := S)).Additive where
  map_add := by
    intros
    apply ModuleCat.hom_ext
    change LinearMap.baseChange S _ = _
    ext s
    simp [coefficientExtension]

private lemma coefficientExtension_exact {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S] :
    PreservesFiniteLimits (coefficientExtension (R := R) (S := S)) ∧
      PreservesFiniteColimits (coefficientExtension (R := R) (S := S)) := by
  apply ((Functor.exact_tfae (coefficientExtension (R := R) (S := S))).out 2 4).mp
  intro C hC
  rw [moduleCat_exact_iff_function_exact] at hC ⊢
  exact Module.Flat.lTensor_exact S hC

private noncomputable def coefficientUnit {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] :
    𝟭 (ModuleCat.{v} R) ⟶ coefficientExtension (R := R) (S := S) ⋙
      ModuleCat.restrictScalars (algebraMap R S) where
  app M := by
    change M ⟶ (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S (S ⊗[R] M))
    refine ConcreteCategory.ofHom (C := ModuleCat R) ?_
    exact {
    toFun := fun m => (1 : S) ⊗ₜ[R] m
    map_add' := fun _ _ => TensorProduct.tmul_add _ _ _
    map_smul' := fun r m => by
      change (1 : S) ⊗ₜ[R] (r • m) = (algebraMap R S r) • ((1 : S) ⊗ₜ[R] m)
      simp only [TensorProduct.tmul_smul, algebraMap_smul] }

private lemma coefficientExtension_unit_isIso {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    (i : S →ₗ[R] R) (hi : ∀ s, algebraMap R S (i s) = s)
    (M : ModuleCat.{v} R) (hM : ∀ m : M, (i 1) • m = m) :
    IsIso ((coefficientUnit (R := R) (S := S)).app M) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  let j : S ⊗[R] M →ₗ[R] M := (TensorProduct.lid R M).toLinearMap.comp (i.rTensor M)
  have hj (m : M) : j (1 ⊗ₜ[R] m) = m := by simp [j, hM]
  refine ⟨fun x y h => (hj x).symm.trans ((congrArg j h).trans (hj y)), fun z => ?_⟩
  show ∃ m : M, (1 : S) ⊗ₜ[R] m = z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul s m =>
    refine ⟨i s • m, ?_⟩
    have hs : (i s) • (1 : S) = s := by
      simpa only [Algebra.smul_def, mul_one] using hi s
    exact (TensorProduct.tmul_smul (i s) (1 : S) m).trans
      (congrArg (fun x : S => x ⊗ₜ[R] m) hs)
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, TensorProduct.tmul_add _ _ _⟩

attribute [local instance] HasDerivedCategory.standard

private instance coefficientExtension_preservesFiniteLimits {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S] :
    PreservesFiniteLimits (coefficientExtension (R := R) (S := S)) :=
  (coefficientExtension_exact (R := R) (S := S)).1
private instance coefficientExtension_preservesFiniteColimits {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S] :
    PreservesFiniteColimits (coefficientExtension (R := R) (S := S)) :=
  (coefficientExtension_exact (R := R) (S := S)).2

private noncomputable def coefficientUnitComplex {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] :
    𝟭 (CochainComplex (ModuleCat.{v} R) ℤ) ⟶
      (coefficientExtension (R := R) (S := S)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex (ComplexShape.up ℤ) where
  app P := {
    f := fun n => (coefficientUnit (R := R) (S := S)).app (P.X n)
    comm' := fun a b _ => (coefficientUnit (R := R) (S := S)).naturality (P.d a b) }
  naturality := by
    intro P Q f
    apply HomologicalComplex.hom_ext
    intro n
    exact (coefficientUnit (R := R) (S := S)).naturality (f.f n)

private noncomputable def coefficientUnitDerived {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S] :
    𝟭 (DerivedCategory (ModuleCat.{v} R)) ⟶
      (coefficientExtension (R := R) (S := S)).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars (algebraMap R S)).mapDerivedCategory := by
  let F := coefficientExtension (R := R) (S := S)
  let G : ModuleCat.{v} S ⥤ ModuleCat.{v} R := ModuleCat.restrictScalars (algebraMap R S)
  let FC := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let GC := G.mapHomologicalComplex (ComplexShape.up ℤ)
  exact Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ 𝟭 _) (DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ G.mapDerivedCategory))
    (𝟭 _) (F.mapDerivedCategory ⋙ G.mapDerivedCategory)
    ((Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
      Functor.whiskerRight (coefficientUnitComplex (R := R) (S := S)) DerivedCategory.Q ≫
      (Functor.associator FC GC DerivedCategory.Q).hom ≫
      Functor.whiskerLeft FC G.mapDerivedCategoryFactors.inv ≫
      (Functor.associator FC DerivedCategory.Q G.mapDerivedCategory).inv ≫
      Functor.whiskerRight F.mapDerivedCategoryFactors.inv G.mapDerivedCategory ≫
      (Functor.associator DerivedCategory.Q F.mapDerivedCategory G.mapDerivedCategory).hom)

private lemma coefficientUnitDerived_isIso {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : ∀ n, IsIso ((coefficientUnit (R := R) (S := S)).app (P.X n))) :
    IsIso ((coefficientUnitDerived (R := R) (S := S)).app (DerivedCategory.Q.obj P)) := by
  have (n : ℤ) : IsIso (((coefficientUnitComplex (R := R) (S := S)).app P).f n) := hP n
  have := HomologicalComplex.Hom.isIso_of_components
    ((coefficientUnitComplex (R := R) (S := S)).app P)
  unfold coefficientUnitDerived
  rw [Localization.liftNatTrans_app]
  dsimp
  infer_instance

private lemma isIso_app_of_retract {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (η : F ⟶ G) {X Y : C} (i : X ⟶ Y) (p : Y ⟶ X)
    (hip : i ≫ p = 𝟙 X) [IsIso (η.app Y)] : IsIso (η.app X) := by
  refine ⟨⟨G.map i ≫ inv (η.app Y) ≫ F.map p, ?_, ?_⟩⟩
  · rw [← Category.assoc, ← η.naturality i, Category.assoc, IsIso.hom_inv_id_assoc,
      ← F.map_comp, hip, F.map_id]
  · rw [Category.assoc, Category.assoc, η.naturality p, IsIso.inv_hom_id_assoc,
      ← G.map_comp, hip, G.map_id]

private lemma perfect_map {R : Type u} {S : Type*} [CommRing R] [CommRing S]
    (F : ModuleCat.{v} R ⥤ ModuleCat S) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : ∀ M : ModuleCat.{v} R, Module.Finite R M → Module.Projective R M →
      Module.Finite S (F.obj M) ∧ Module.Projective S (F.obj M))
    {K : DerivedCategory (ModuleCat.{v} R)} (hK : IsPerfect K) :
    IsPerfect (F.mapDerivedCategory.obj K) := by
  obtain ⟨P, a, b, hPa, hPb, hPf, hPp, ⟨e⟩⟩ := hK
  have := hPa
  have := hPb
  exact ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P, a, b,
    inferInstance, inferInstance, fun n => (hF (P.X n) (hPf n) (hPp n)).1,
    fun n => (hF (P.X n) (hPf n) (hPp n)).2,
    ⟨F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app P⟩⟩

private lemma coefficientRestriction_finiteProjective {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S] [Module.Projective R S]
    (M : ModuleCat.{v} S) [Module.Finite S M] [Module.Projective S M] :
    Module.Finite R ((ModuleCat.restrictScalars (algebraMap R S)).obj M) ∧
      Module.Projective R ((ModuleCat.restrictScalars (algebraMap R S)).obj M) := by
  let N := (ModuleCat.restrictScalars (algebraMap R S)).obj M
  let : Module S N := M.isModule
  have : IsScalarTower R S N := ⟨fun r s m => by
    rw [Algebra.smul_def]
    show (algebraMap R S r * s) • m = (algebraMap R S r) • s • m
    exact mul_smul _ _ _⟩
  have : Module.Finite S N := inferInstanceAs (Module.Finite S M)
  have : Module.Projective S N := inferInstanceAs (Module.Projective S M)
  have : Module.Finite R N := Module.Finite.trans S N
  refine ⟨inferInstance, ?_⟩
  obtain ⟨n, f, g, hf, hg, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective S N
  have : Module.Projective R (Fin n → S) :=
    Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R := R) (M := fun _ : Fin n => S))
  exact Module.Projective.of_split (g.restrictScalars R) (f.restrictScalars R)
    (by ext m; exact LinearMap.congr_fun hfg m)

/-- Perfectness passes from a binary biproduct to both summands. -/
private theorem isPerfect_of_biproduct_common
    {R : Type u} [CommRing R] (K L : DerivedCategory (ModuleCat.{u} R))
    (h : IsPerfect (K ⊞ L)) :
    IsPerfect K ∧ IsPerfect L := by
  obtain ⟨P, -, b, -, hPle, hPfin, hPproj, ⟨eP⟩⟩ := id h
  have hpseudo : StacksDraft.PseudoCoherence.IsPseudoCoherent (K ⊞ L) :=
    (StacksDraft.PseudoCoherence.pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective
      (K ⊞ L) 0).2.1.mpr
      ⟨P, ⟨b, hPle⟩, fun n => ⟨hPfin n, hPproj n⟩, ⟨eP.symm⟩⟩
  have hKL :=
    (_root_.PseudoCoherence.isPseudoCoherentFrom_and_pseudoCoherent_of_biproduct K L 0).2 hpseudo
  exact ⟨isPerfect_of_retract biprod.inl biprod.fst biprod.inl_fst hKL.1 h,
    isPerfect_of_retract biprod.inr biprod.snd biprod.inr_snd hKL.2 h⟩

/-- **Stacks 066S.** If a binary biproduct of objects of `D(R)` is perfect, then both summands are
perfect. Perfectness passes to the summands at arbitrary carrier universes: a small projective
coefficient quotient supporting the given bounded complex supplies the internal descent. -/
@[stacks 066S]
theorem isPerfect_of_biproduct
    {R : Type u} [CommRing R] (K L : DerivedCategory (ModuleCat.{v} R))
    (h : IsPerfect (K ⊞ L)) :
    IsPerfect K ∧ IsPerfect L := by
  classical
  obtain ⟨P, a, b, hPa, hPb, hPf, hPp, ⟨eP⟩⟩ := id h
  let T := {n : ℤ // n ∈ Finset.Icc a b}
  let M := ∀ n : T, P.X n.val
  let (n : T) : Module.Finite R (P.X n.val) := hPf n.val
  let (n : T) : Module.Projective R (P.X n.val) := hPp n.val
  have : Module.Projective R M :=
    Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype
      (R := R) (M := fun n : T => P.X n.val))
  obtain ⟨S, hS, hRS, hSf, hSp, i, hi, hiM⟩ := exists_small_coefficient_ring (R := R) M
  let := hS
  let := hRS
  let := hSf
  let := hSp
  let : Module.Flat R S := Module.Flat.of_projective
  have hiP (n : ℤ) (m : P.X n) : (i 1) • m = m := by
    by_cases hn : n ∈ Finset.Icc a b
    · let t : T := ⟨n, hn⟩
      have ht := congrFun (hiM (Pi.single t m)) t
      simpa [M, t] using ht
    · simp only [Finset.mem_Icc, not_and_or, not_le] at hn
      have := ModuleCat.isZero_iff_subsingleton.mp (isZero_X_of_lt_or_lt P a b n hn)
      exact Subsingleton.elim _ _
  let F := coefficientExtension (R := R) (S := S)
  let G : ModuleCat.{v} S ⥤ ModuleCat.{v} R := ModuleCat.restrictScalars (algebraMap R S)
  let η := coefficientUnitDerived (R := R) (S := S)
  have : IsIso (η.app (DerivedCategory.Q.obj P)) :=
    coefficientUnitDerived_isIso P (fun n => coefficientExtension_unit_isIso i hi (P.X n) (hiP n))
  have : IsIso (η.app (K ⊞ L)) := isIso_app_of_retract η eP.hom eP.inv eP.hom_inv_id
  have : IsIso (η.app K) :=
    isIso_app_of_retract η (Y := K ⊞ L) biprod.inl biprod.fst biprod.inl_fst
  have : IsIso (η.app L) :=
    isIso_app_of_retract η (Y := K ⊞ L) biprod.inr biprod.snd biprod.inr_snd
  have hFsum : IsPerfect (F.mapDerivedCategory.obj (K ⊞ L)) :=
    perfect_map F (fun N _ _ => by
      show Module.Finite S (S ⊗[R] N) ∧ Module.Projective S (S ⊗[R] N)
      exact ⟨inferInstance, inferInstance⟩) h
  have : F.mapDerivedCategory.Additive := inferInstance
  have : PreservesBinaryBiproducts F.mapDerivedCategory :=
    preservesBinaryBiproducts_of_preservesBinaryProducts F.mapDerivedCategory
  have hFL := isPerfect_of_biproduct_common (F.mapDerivedCategory.obj K)
    (F.mapDerivedCategory.obj L)
    (isPerfect_of_iso (F.mapDerivedCategory.mapBiprod K L).symm hFsum)
  exact ⟨isPerfect_of_iso (asIso (η.app K))
      (perfect_map G (fun N _ _ => coefficientRestriction_finiteProjective N) hFL.1),
    isPerfect_of_iso (asIso (η.app L))
      (perfect_map G (fun N _ _ => coefficientRestriction_finiteProjective N) hFL.2)⟩

end BiproductSummands

/-! ### Perfectness as pseudo-coherence together with finite Tor dimension -/

section PseudoCoherenceAndTorDimension

/-- **Flatness of the cokernel at the bottom of the window.** Let `P` be a bounded above complex
of flat `R`-modules whose image in `D(R)` admits a flat representative supported in `[a, b]`. Then
the cokernel of the differential `P^{a-1} → P^a` is a flat `R`-module. This is [stacks 0653] for
`P`, read through the flat-representative formulation of Tor amplitude, and it holds with the
carrier universe of the modules independent of the universe of the ring. -/
theorem cokernel_flat_of_hasFlatRepresentative
    {R : Type u} [CommRing R] (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (a b : ℤ) (hbounded : TorAmplitude.BoundedAbove P)
    (hflat : TorAmplitude.IsComplexOfFlats P)
    (hamp : HasFlatRepresentative (DerivedCategory.Q.obj P) a b) :
    Module.Flat R (cokernel (P.d (a - 1) a) : ModuleCat.{max u v} R) := by
  obtain ⟨E, hEflat, hGE, hLE, ⟨e⟩⟩ := hamp
  have : Small.{max u v} R := small_max R
  exact TorAmplitude.cokernel_flat_of_flat_representative P E a b
    hbounded hflat hEflat hGE hLE e

/-- An object with a flat representative supported in `[a, b]` has vanishing cohomology outside
`[a, b]`: the representative itself has vanishing terms in those degrees. -/
lemma homology_isZero_of_hasFlatRepresentative
    {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat.{max u v} R))
    (a b i : ℤ) (hK : HasFlatRepresentative K a b) (hi : i < a ∨ b < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K) := by
  obtain ⟨E, -, hGE, hLE, ⟨e⟩⟩ := hK
  exact (isZero_homology_Q_obj E i (isZero_X_of_lt_or_lt E a b i hi)).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).mapIso e)

/-- The canonical truncation of a complex vanishing strictly above `b` again vanishes strictly
above `b`, since the truncation map is an epimorphism in every degree. -/
lemma truncGE_isStrictlyLE
    {R : Type u} [CommRing R] (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (a b : ℤ) (hP : P.IsStrictlyLE b) : (P.truncGE a).IsStrictlyLE b :=
  truncGE_isStrictlyLE_aux P a b hP

/-- **The finite-projective representative in a prescribed Tor window.** A pseudo-coherent object
with a flat representative supported in `[a, b]` is represented by a complex of finite projective
modules concentrated in `[a, b]`. Pseudo-coherence supplies a finite free representative `F`
vanishing strictly above `b`; the flat representative makes the cokernel of `F^{a-1} → F^a` flat,
and it is finitely presented, hence finite projective, so the canonical truncation `F≥a` has the
required terms. -/
private theorem finiteProjectiveRepresentative
    {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat.{max u v} R))
    (a b : ℤ) (hpseudo : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hamp : HasFlatRepresentative K a b) :
    ∃ E : CochainComplex (ModuleCat.{max u v} R) ℤ,
      (∀ i : ℤ, Module.Finite R (E.X i) ∧ Module.Projective R (E.X i)) ∧
        E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧ Nonempty (K ≅ DerivedCategory.Q.obj E) := by
  obtain ⟨F, α, hFfree, hFLE, hα⟩ :=
    (StacksDraft.PseudoCoherence.pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective
      K b).2.2 hpseudo fun i hi =>
        homology_isZero_of_hasFlatRepresentative K a b i hamp (Or.inr hi)
  have hFflat : TorAmplitude.IsComplexOfFlats F := fun i => by
    let : Module.Free R (F.X i) := hFfree i |>.2
    infer_instance
  obtain ⟨A, hAflat, hAGE, hALE, ⟨eA⟩⟩ := hamp
  have hEaflat : Module.Flat R (cokernel (F.d (a - 1) a) : ModuleCat.{max u v} R) :=
    cokernel_flat_of_hasFlatRepresentative F a b
      ⟨b, (CochainComplex.isStrictlyLE_iff F b).mp hFLE⟩ hFflat
      ⟨A, hAflat, hAGE, hALE, ⟨(asIso α) ≪≫ eA⟩⟩
  have hFGE : F.IsGE a := by
    rw [CochainComplex.isGE_iff]
    intro i hi
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (homology_isZero_of_hasFlatRepresentative K a b i
      ⟨A, hAflat, hAGE, hALE, ⟨eA⟩⟩ (Or.inl hi)).of_iso
      (((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) i).app F).symm ≪≫
        (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).mapIso (asIso α))
  exact ⟨F.truncGE a, finite_projective_truncGE_X F a (fun i => (hFfree i).1)
    (fun i => have := (hFfree i).2; inferInstance) hEaflat, inferInstance,
    truncGE_isStrictlyLE F a b hFLE,
    ⟨(asIso α).symm ≪≫ asIso (DerivedCategory.Q.map (F.πTruncGE a))⟩⟩

/-- **Stacks 0658.** An object of `D(R)` is perfect if and only if it is pseudo-coherent and has
finite Tor dimension, the latter being recorded by the existence of a bounded flat representative.
Moreover a pseudo-coherent object whose Tor amplitude lies in `[a, b]` is represented by a complex
of finite projective modules concentrated in the degrees `[a, b]`. -/
@[stacks 0658,
  sga "5 VIII 8.1" "commutative rings only",
  sga "6 I 5.8.1" "module over a ring",
  sga "6 I 5.8" "special case"]
theorem isPerfect_iff_pseudoCoherent_and_finiteTorDimension
    {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat.{max u v} R)) :
    (IsPerfect K ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherent K ∧
        ∃ a b : ℤ, HasFlatRepresentative K a b) ∧
      ∀ a b : ℤ, StacksDraft.PseudoCoherence.IsPseudoCoherent K →
        HasFlatRepresentative K a b →
        ∃ E : CochainComplex (ModuleCat.{max u v} R) ℤ,
          (∀ i : ℤ, Module.Finite R (E.X i) ∧ Module.Projective R (E.X i)) ∧
            E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧
              Nonempty (K ≅ DerivedCategory.Q.obj E) := by
  refine ⟨⟨fun ⟨P, a, b, hGE, hLE, hfinite, hprojective, e⟩ => ?_,
    fun ⟨hpseudo, a, b, hamp⟩ => ?_⟩, finiteProjectiveRepresentative K⟩
  · refine ⟨?_, a, b, P, fun i => ?_, hGE, hLE, e⟩
    · exact
        (StacksDraft.PseudoCoherence.pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective
          K b).2.1.mpr ⟨P, ⟨b, hLE⟩, fun i => ⟨hfinite i, hprojective i⟩, e.map Iso.symm⟩
    · have := hprojective i
      infer_instance
  · obtain ⟨E, hfp, hGE, hLE, e⟩ := finiteProjectiveRepresentative K a b hpseudo hamp
    exact ⟨E, a, b, hGE, hLE, fun i => (hfp i).1, fun i => (hfp i).2, e⟩

end PseudoCoherenceAndTorDimension

end StacksDraft.Perfect
