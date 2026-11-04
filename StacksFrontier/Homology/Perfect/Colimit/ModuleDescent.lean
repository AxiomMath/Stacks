module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Homology.KFlat.BaseChange
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksCore.Tactic.StacksAttribute
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.RingTheory.Finiteness.Projective

/-!
# Perfect complexes over filtered colimits of rings: finite projective modules

This file sets up the data used for [stacks 0BC7] and descends finite projective modules and
finite systems of matrices along a filtered colimit `c` of commutative rings `R : I ⥤ CommRingCat`.

## Main definitions

* `StacksDraft.Perfect.DerivedExtendScalars`: a choice of total derived extension of scalars for
  every homomorphism of commutative rings in a fixed universe.
* `StacksDraft.Perfect.extensionOfScalarsComplexComp`: the canonical scalar-tower isomorphism for
  termwise extension of scalars on complexes, followed by localization to the derived category.
* `StacksDraft.Perfect.derivedExtensionScalarsCongr`: transport of derived extension of scalars
  along an equality of ring homomorphisms.

## Implementation notes

Tag 064H characterizes total derived extension of scalars `- ⊗ᴸ_R A` by its comparison to
termwise extension of scalars rather than constructing it, and
`CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars` packages that
characterization as data, with
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` as the canonical choice.
Tag 0BC7 speaks of derived extension of scalars along every transition map of the filtered system
at once, so its proof consumes a whole family `E : DerivedExtendScalars` of such data.

All three K-flat ingredients of the proof are imported and none is assumed. Every object of the
derived category has a K-flat representative ([stacks 06Y4],
`CochainComplex.KFlat.exists_kFlat_resolution`); extension of scalars preserves K-flatness
([stacks 06Y1], `kFlat_baseChange`); and K-flat complexes compute derived extension of scalars
([stacks 06Y5]), which is the field
`CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.comparison_isIso_of_kFlat`
of the datum itself, so `ComputesKFlat` below is a theorem about every datum rather than a
hypothesis on one. That field is stated for the large-universe K-flatness predicate, which at a
module universe equal to the ring's is `CochainComplex.KFlat` itself.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

open scoped TensorProduct

open scoped Matrix

universe uI uR uM uA

namespace StacksDraft.Perfect

attribute [local instance] HasDerivedCategory.standard

/-- A choice of total derived extension of scalars for every homomorphism of commutative rings
in `Type uR`, acting on complexes of modules in the same universe.

Tag 064H characterizes `- ⊗ᴸ_R A` by a comparison to termwise extension of scalars rather than
constructing it, and `CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars`
packages that characterization as data; a family of such data is what the proof of [stacks 0BC7]
consumes, since the tag speaks of derived extension of scalars along every transition map of a
filtered system of rings at once. The canonical family is
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`. -/
public abbrev DerivedExtendScalars :=
  ∀ {A B : Type uR} [CommRing A] [CommRing B] (f : A →+* B),
    TotalDerivedExtensionScalars.{uR, uR, uR} f

/-- A K-flat complex computes total derived extension of scalars: the comparison of the datum
`E f` with termwise extension of scalars is an isomorphism at every K-flat complex.

This is [stacks 06Y5]. It holds for every datum, by `computesKFlat` below, and is recorded here
only to name the property that the proof of the Hom-colimit half of [stacks 0BC7] consumes. -/
def ComputesKFlat (E : DerivedExtendScalars.{uR}) : Prop :=
  ∀ {A B : Type uR} [CommRing A] [CommRing B] (f : A →+* B)
    (P : CochainComplex (ModuleCat.{uR} A) ℤ), P.KFlat → IsIso ((E f).comparison.app P)

/-- Every total derived extension-of-scalars datum is computed by K-flat complexes: this is one
of the fields of `CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars`, stated
there for the large-universe K-flatness predicate, which at a module universe equal to the ring's
is `CochainComplex.KFlat` itself ([stacks 06Y5]). -/
theorem computesKFlat (E : DerivedExtendScalars.{uR}) : ComputesKFlat E :=
  fun _ P hP => (E _).comparison_isIso_of_kFlat P
    hP

/-- The canonical scalar-tower isomorphism for termwise extension of scalars, followed by the
localization functor to the derived category. -/
public def extensionOfScalarsComplexComp
    {A B C : Type uR} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    extensionOfScalarsComplex.{uR, uR, uR} (g.comp f) ≅
      (ModuleCat.extendScalars.{uR, uR, uR} f).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        extensionOfScalarsComplex.{uR, uR, uR} g :=
  Functor.isoWhiskerRight
    (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp f g) (ComplexShape.up ℤ))
    DerivedCategory.Q

/-- Derived extension of scalars is invariant under equality of its ring homomorphism. -/
public def derivedExtensionScalarsCongr (E : DerivedExtendScalars.{uR})
    {A B : Type uR} [CommRing A] [CommRing B] {f g : A →+* B} (h : f = g) :
    (E f).functor ≅ (E g).functor :=
  eqToIso (congrArg (fun q ↦ (E q).functor) h)


/-- A finite projective module is the image of an idempotent on finite free coordinates. -/
theorem finite_projective_retract
    {A : Type uR} [CommRing A]
    (P : Type (max uM uR)) [AddCommGroup P] [Module A P]
    [Module.Finite A P] [Module.Projective A P] :
    ∃ (n : ℕ) (f : (Fin n → A) →ₗ[A] P) (g : P →ₗ[A] (Fin n → A)),
      f.comp g = LinearMap.id ∧
        (g.comp f).comp (g.comp f) = g.comp f := by
  obtain ⟨n, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A P
  refine ⟨n, f, g, hfg, ?_⟩
  apply LinearMap.ext
  intro x
  show g (f (g (f x))) = g (f x)
  rw [← LinearMap.comp_apply f g (f x), hfg]
  rfl

/-- An idempotent endomorphism fixes every element of its range. -/
private theorem idempotent_apply_of_mem_range
    {A : Type uR} [CommRing A] {M : Type uM} [AddCommGroup M] [Module A M]
    (e : M →ₗ[A] M) (he : e.comp e = e) (x : e.range) : e x.1 = x.1 := by
  obtain ⟨y, hy⟩ := x.2
  rw [← hy, ← LinearMap.comp_apply, he]

/-- A finite projective module has an explicit idempotent image model. -/
private theorem finite_projective_idempotent_model
    {A : Type uR} [CommRing A]
    (P : Type (max uM uR)) [AddCommGroup P] [Module A P]
    [Module.Finite A P] [Module.Projective A P] :
    ∃ (n : ℕ) (e : (Fin n → A) →ₗ[A] (Fin n → A)),
      e.comp e = e ∧ Nonempty (P ≃ₗ[A] e.range) := by
  obtain ⟨n, f, g, hfg, he⟩ := finite_projective_retract (A := A) P
  let e := g.comp f
  let h : P →ₗ[A] e.range := g.codRestrict e.range (fun x => by
    refine ⟨g x, ?_⟩
    show g (f (g x)) = g x
    rw [← LinearMap.comp_apply f g x, hfg]
    rfl)
  let k : e.range →ₗ[A] P := f.comp e.range.subtype
  have hkh : k.comp h = LinearMap.id := by
    apply LinearMap.ext
    intro x
    show f (g x) = x
    rw [← LinearMap.comp_apply f g x, hfg]
    rfl
  have hhk : h.comp k = LinearMap.id := by
    exact LinearMap.ext fun x => Subtype.ext (idempotent_apply_of_mem_range e he x)
  exact ⟨n, e, he, ⟨LinearEquiv.ofLinearMap h k hhk hkh⟩⟩

/-- The image of an idempotent endomorphism of a finite free module is finite projective. -/
theorem idempotent_range_finite_projective
    {A : Type uR} [CommRing A] (n : ℕ)
    (e : (Fin n → A) →ₗ[A] (Fin n → A)) (he : e.comp e = e) :
    Module.Finite A e.range ∧ Module.Projective A e.range := by
  let i : e.range →ₗ[A] (Fin n → A) := e.range.subtype
  let p : (Fin n → A) →ₗ[A] e.range := e.rangeRestrict
  have hp : p.comp i = LinearMap.id := by
    exact LinearMap.ext fun x => Subtype.ext (idempotent_apply_of_mem_range e he x)
  exact ⟨Module.Finite.of_surjective p e.surjective_rangeRestrict,
    Module.Projective.of_split i p hp⟩

/-- Scalar extension preserves the injectivity of a split inclusion. -/
private theorem split_baseChange_injective
    {A B : Type uR} [CommRing A] [CommRing B] [Algebra A B]
    {P : Type uM} {M : Type uA} [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M]
    (i : P →ₗ[A] M) (r : M →ₗ[A] P) (h : r.comp i = LinearMap.id) :
    Function.Injective (i.baseChange B) := by
  have h' : (r.baseChange B).comp (i.baseChange B) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, h, LinearMap.baseChange_id]
  exact LinearMap.injective_of_comp_eq_id _ _ h'

/-- A split inclusion identifies its source with the image of the associated idempotent. -/
noncomputable def split_range_equiv
    {A : Type uR} [CommRing A]
    {P : Type uM} {M : Type uA} [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M]
    (i : P →ₗ[A] M) (r : M →ₗ[A] P) (h : r.comp i = LinearMap.id) :
    P ≃ₗ[A] (i.comp r).range := by
  let e := i.comp r
  have he : e.comp e = e := by
    apply LinearMap.ext
    intro x
    change i (r (i (r x))) = i (r x)
    rw [← LinearMap.comp_apply r i (r x), h]
    rfl
  let u : P →ₗ[A] e.range := i.codRestrict e.range (fun x => by
    refine ⟨i x, ?_⟩
    change i (r (i x)) = i x
    rw [← LinearMap.comp_apply r i x, h]
    rfl)
  let v : e.range →ₗ[A] P := r.comp e.range.subtype
  apply LinearEquiv.ofLinearMap u v
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    change e x.1 = x.1
    obtain ⟨y, hy⟩ := x.2
    rw [← hy, ← LinearMap.comp_apply, he]
  · apply LinearMap.ext
    intro x
    change r (i x) = x
    rw [← LinearMap.comp_apply r i x, h]
    rfl

/-- After scalar extension, a split summand is again the image of its extended idempotent. -/
private noncomputable def split_baseChange_range_equiv
    {A B : Type uR} [CommRing A] [CommRing B] [Algebra A B]
    {P : Type uM} {M : Type uA} [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M]
    (i : P →ₗ[A] M) (r : M →ₗ[A] P) (h : r.comp i = LinearMap.id) :
    (B ⊗[A] P) ≃ₗ[B] ((i.comp r).baseChange B).range := by
  have h' : (r.baseChange B).comp (i.baseChange B) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, h, LinearMap.baseChange_id]
  rw [LinearMap.baseChange_comp]
  exact split_range_equiv (i.baseChange B) (r.baseChange B) h'

/-- Scalar extension of finite free coordinates is the coordinate module over the target ring. -/
noncomputable def finite_free_baseChange_equiv
    {A B : Type uR} [CommRing A] [CommRing B]
    (f : A →+* B) (n : ℕ) :
    letI : Algebra A B := f.toAlgebra
    (B ⊗[A] (Fin n → A)) ≃ₗ[B] (Fin n → B) := by
  letI : Algebra A B := f.toAlgebra
  exact TensorProduct.piScalarRight A B B (Fin n)

/-- The finite free scalar-extension equivalence carries an endomorphism to the
entrywise extended matrix. -/
theorem finite_free_baseChange_matrix_commutes
    {A B : Type uR} [CommRing A] [CommRing B]
    (f : A →+* B) (n : ℕ) (M : Matrix (Fin n) (Fin n) A) :
    letI : Algebra A B := f.toAlgebra
    (finite_free_baseChange_equiv f n).toLinearMap.comp
        ((Matrix.toLin' M).baseChange B) =
      (Matrix.toLin' (M.map f)).comp (finite_free_baseChange_equiv f n).toLinearMap := by
  let : Algebra A B := f.toAlgebra
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b v =>
      ext j
      simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul,
        finite_free_baseChange_equiv, Matrix.toLin'_apply]
      show ((M *ᵥ v) j) • b = (M.map f *ᵥ (fun k => (v k) • b)) j
      have hv : (fun k : Fin n => (v k) • b) = b • (f ∘ v) := by
        ext k
        simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]
      rw [hv]
      rw [Matrix.mulVec_smul]
      simp only [Pi.smul_apply]
      rw [← RingHom.map_mulVec]
      simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]
  | add x y hx hy => simp [map_add, hx, hy]

/-- Conjugate endomorphisms have linearly equivalent images. -/
noncomputable def range_equiv_of_conjugate
    {A : Type uR} [CommRing A]
    {M N : Type uM} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (u : M ≃ₗ[A] N) (e : M →ₗ[A] M) (e' : N →ₗ[A] N)
    (h : u.toLinearMap.comp e = e'.comp u.toLinearMap) :
    e.range ≃ₗ[A] e'.range := by
  have hrange : e.range.map u.toLinearMap = e'.range := by
    calc
      e.range.map u.toLinearMap = (u.toLinearMap.comp e).range :=
        (LinearMap.range_comp e u.toLinearMap).symm
      _ = (e'.comp u.toLinearMap).range := by rw [h]
      _ = e'.range := LinearMap.range_comp_of_range_eq_top e' (LinearEquiv.range u)
  exact u.submoduleMap e.range ≪≫ₗ LinearEquiv.ofEq _ _ hrange

/-- The image of an idempotent on finite free coordinates commutes with scalar extension. -/
noncomputable def idempotent_range_baseChange_equiv
    {A B : Type uR} [CommRing A] [CommRing B]
    (f : A →+* B) (n : ℕ)
    (e : (Fin n → A) →ₗ[A] (Fin n → A)) (he : e.comp e = e) :
    letI : Algebra A B := f.toAlgebra
    (B ⊗[A] e.range) ≃ₗ[B]
      (Matrix.toLin' ((LinearMap.toMatrix' e).map f)).range := by
  letI : Algebra A B := f.toAlgebra
  let i : e.range →ₗ[A] (Fin n → A) := e.range.subtype
  let r : (Fin n → A) →ₗ[A] e.range := e.rangeRestrict
  have hir : i.comp r = e := e.subtype_comp_rangeRestrict
  have hri : r.comp i = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change e x.1 = x.1
    obtain ⟨y, hy⟩ := x.2
    rw [← hy, ← LinearMap.comp_apply, he]
  have hri' : (r.baseChange B).comp (i.baseChange B) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hri, LinearMap.baseChange_id]
  have hcomm := finite_free_baseChange_matrix_commutes f n (LinearMap.toMatrix' e)
  simp only [Matrix.toLin'_toMatrix'] at hcomm
  have hcomm' : (finite_free_baseChange_equiv f n).toLinearMap.comp
      ((i.baseChange B).comp (r.baseChange B)) =
      (Matrix.toLin' ((LinearMap.toMatrix' e).map f)).comp
        (finite_free_baseChange_equiv f n).toLinearMap := by
    rw [← LinearMap.baseChange_comp, hir]
    exact hcomm
  exact split_range_equiv (i.baseChange B) (r.baseChange B) hri' ≪≫ₗ
    range_equiv_of_conjugate (finite_free_baseChange_equiv f n)
      ((i.baseChange B).comp (r.baseChange B))
      (Matrix.toLin' ((LinearMap.toMatrix' e).map f)) hcomm'

/-- The derived Hom set out of a bounded complex of projectives is computed by
homotopy classes of maps of complexes. -/
theorem bounded_projective_Qh_map_bijective
    {A : Type uR} [CommRing A]
    (P L : CochainComplex (ModuleCat.{max uM uR} A) ℤ) (b : ℤ)
    (hP : P.IsStrictlyLE b)
    (hproj : ∀ i : ℤ, Module.Projective A (P.X i)) :
    Function.Bijective (DerivedCategory.Qh.map :
      ((HomotopyCategory.quotient _ _).obj P ⟶
        (HomotopyCategory.quotient _ _).obj L) → _) := by
  let : P.IsStrictlyLE b := hP
  let (i : ℤ) : Module.Projective A (P.X i) := hproj i
  let (i : ℤ) : Projective (P.X i) := inferInstance
  let : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  exact CochainComplex.IsKProjective.Qh_map_bijective P _

/-- Equality of two elements from one stage is witnessed at a later stage. -/
private theorem stage_eq_iff
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat)]
    (c : Cocone R) (hc : IsColimit c)
    (i : I) (x y : R.obj i) :
    (c.ι.app i).hom x = (c.ι.app i).hom y ↔
      ∃ (j : I) (f : i ⟶ j), (R.map f).hom x = (R.map f).hom y :=
  Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (forget CommRingCat) hc) x y

/-- A finite tuple of elements of the colimit can be represented at one common stage. -/
@[sga "4 I 2.8.1" "3, special case"]
theorem finite_stage_exists
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat)]
    (c : Cocone R) (hc : IsColimit c)
    {α : Type uA} [Fintype α] (x : α → c.pt) :
    ∃ (j : I) (y : α → R.obj j), ∀ a, (c.ι.app j).hom (y a) = x a := by
  classical
  choose i z hz using fun a => Concrete.isColimit_exists_rep R hc (x a)
  obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (Finset.univ.image i)
  let f (a : α) : i a ⟶ j :=
    Classical.choice (hj (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩))
  refine ⟨j, fun a => (R.map (f a)).hom (z a), ?_⟩
  intro a
  have hw := congrArg (fun q : R.obj (i a) ⟶ c.pt => q.hom (z a)) (c.w (f a))
  exact hw.trans (hz a)

/-- Finitely many equalities in a filtered colimit hold at one later stage. -/
theorem finite_stage_eq
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat)]
    (c : Cocone R) (hc : IsColimit c)
    {α : Type uA} [Fintype α] (i : I) (x y : α → R.obj i)
    (h : ∀ a, (c.ι.app i).hom (x a) = (c.ι.app i).hom (y a)) :
    ∃ (j : I) (f : i ⟶ j), ∀ a,
      (R.map f).hom (x a) = (R.map f).hom (y a) := by
  classical
  suffices aux : ∀ (s : Finset α) (i : I) (x y : α → R.obj i),
      (∀ a ∈ s, (c.ι.app i).hom (x a) = (c.ι.app i).hom (y a)) →
      ∃ (j : I) (f : i ⟶ j), ∀ a ∈ s,
        (R.map f).hom (x a) = (R.map f).hom (y a) by
    simpa using aux Finset.univ i x y (by simpa using h)
  intro s
  induction s using Finset.induction with
  | empty =>
      intro i x y _
      exact ⟨i, 𝟙 i, by simp⟩
  | @insert a s ha ih =>
      intro i x y h
      obtain ⟨j, f, hf⟩ := ih i x y (by
        intro b hb
        exact h b (Finset.mem_insert_of_mem hb))
      have heq : (c.ι.app j).hom ((R.map f).hom (x a)) =
          (c.ι.app j).hom ((R.map f).hom (y a)) := by
        calc
          _ = (c.ι.app i).hom (x a) :=
            congrArg (fun q : R.obj i ⟶ c.pt => q.hom (x a)) (c.w f)
          _ = (c.ι.app i).hom (y a) := h a (Finset.mem_insert_self a s)
          _ = _ :=
            (congrArg (fun q : R.obj i ⟶ c.pt => q.hom (y a)) (c.w f)).symm
      obtain ⟨k, g, hg⟩ := (stage_eq_iff R c hc j _ _).mp heq
      refine ⟨k, f ≫ g, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · simpa only [Functor.map_comp, CommRingCat.comp_apply] using hg
      · simpa only [Functor.map_comp, CommRingCat.comp_apply] using
          congrArg (R.map g).hom (hf b hb)

/-- A rectangular matrix over the colimit comes from one stage. -/
private theorem rectangular_matrix_stage_exists
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat)]
    (c : Cocone R) (hc : IsColimit c)
    {m n : Type uA} [Fintype m] [Fintype n] (M : Matrix m n c.pt) :
    ∃ (j : I) (N : Matrix m n (R.obj j)), N.map (c.ι.app j).hom = M := by
  classical
  obtain ⟨j, y, hy⟩ := finite_stage_exists R c hc
    (fun p : m × n => M p.1 p.2)
  refine ⟨j, fun p q => y (p, q), ?_⟩
  ext p q
  exact hy (p, q)

/-- Equality of rectangular matrices at the colimit is witnessed at a later stage. -/
private theorem rectangular_matrix_eventually_eq
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat)]
    (c : Cocone R) (hc : IsColimit c)
    {m n : Type uA} [Fintype m] [Fintype n] (i : I)
    (A B : Matrix m n (R.obj i))
    (h : A.map (c.ι.app i).hom = B.map (c.ι.app i).hom) :
    ∃ (j : I) (f : i ⟶ j), A.map (R.map f).hom = B.map (R.map f).hom := by
  classical
  have heq (p : m × n) :
      (c.ι.app i).hom (A p.1 p.2) = (c.ι.app i).hom (B p.1 p.2) :=
    congrArg (fun M : Matrix m n c.pt => M p.1 p.2) h
  obtain ⟨j, f, hf⟩ := finite_stage_eq R c hc i
    (fun p : m × n => A p.1 p.2) (fun p : m × n => B p.1 p.2) heq
  refine ⟨j, f, ?_⟩
  ext p q
  exact hf (p, q)

/-- A map between finite free modules over the colimit has matrix coefficients at a stage. -/
private theorem finite_free_map_stage_exists
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat)]
    (c : Cocone R) (hc : IsColimit c) (m n : ℕ)
    (u : (Fin n → c.pt) →ₗ[c.pt] (Fin m → c.pt)) :
    ∃ (j : I) (v : (Fin n → R.obj j) →ₗ[R.obj j] (Fin m → R.obj j)),
      (LinearMap.toMatrix' v).map (c.ι.app j).hom = LinearMap.toMatrix' u := by
  obtain ⟨j, N, hN⟩ := rectangular_matrix_stage_exists R c hc (LinearMap.toMatrix' u)
  exact ⟨j, Matrix.toLin' N, by simpa only [LinearMap.toMatrix'_toLin'] using hN⟩

/-- Equality of maps between finite free modules after scalar extension is detected at a
later ring stage through their matrices. -/
private theorem finite_free_map_eventually_eq
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat)]
    (c : Cocone R) (hc : IsColimit c) (m n : ℕ) (i : I)
    (u v : (Fin n → R.obj i) →ₗ[R.obj i] (Fin m → R.obj i))
    (h : (LinearMap.toMatrix' u).map (c.ι.app i).hom =
      (LinearMap.toMatrix' v).map (c.ι.app i).hom) :
    ∃ (j : I) (f : i ⟶ j),
      (LinearMap.toMatrix' u).map (R.map f).hom =
        (LinearMap.toMatrix' v).map (R.map f).hom :=
  rectangular_matrix_eventually_eq R c hc i _ _ h

/-- A finite system of differentials between finite free modules with square zero descends
to one ring stage. The indexing map plays the role of shifting one degree. -/
private theorem finite_free_differentials_stage_exists
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat)]
    (c : Cocone R) (hc : IsColimit c)
    {α : Type uA} [Fintype α] (d : α → Type uA) [∀ a, Fintype (d a)]
    (next : α → α) (M : ∀ a, Matrix (d (next a)) (d a) c.pt)
    (h : ∀ a, M (next a) * M a = 0) :
    ∃ (j : I) (N : ∀ a, Matrix (d (next a)) (d a) (R.obj j)),
      (∀ a, N (next a) * N a = 0) ∧
      (∀ a, (N a).map (c.ι.app j).hom = M a) := by
  classical
  obtain ⟨j, y, hy⟩ := finite_stage_exists R c hc
    (fun t : (a : α) × d (next a) × d a => M t.1 t.2.1 t.2.2)
  let N : ∀ a, Matrix (d (next a)) (d a) (R.obj j) :=
    fun a p q => y ⟨a, p, q⟩
  have hN (a : α) : (N a).map (c.ι.app j).hom = M a := by
    ext p q
    exact hy ⟨a, p, q⟩
  have heq (t : (a : α) × d (next (next a)) × d a) :
      (c.ι.app j).hom ((N (next t.1) * N t.1) t.2.1 t.2.2) =
        (c.ι.app j).hom 0 := by
    have h' : (N (next t.1) * N t.1).map (c.ι.app j).hom = 0 := by
      rw [Matrix.map_mul, hN, hN, h]
    simpa using congrArg (fun X : Matrix (d (next (next t.1))) (d t.1) c.pt =>
      X t.2.1 t.2.2) h'
  obtain ⟨k, f, hf⟩ := finite_stage_eq R c hc j
    (fun t : (a : α) × d (next (next a)) × d a =>
      (N (next t.1) * N t.1) t.2.1 t.2.2)
    (fun _ => (0 : R.obj j)) heq
  refine ⟨k, fun a => (N a).map (R.map f).hom, ?_, ?_⟩
  · intro a
    rw [← Matrix.map_mul]
    ext p q
    simpa using hf ⟨a, p, q⟩
  · intro a
    ext p q
    calc
      (c.ι.app k).hom ((R.map f).hom (N a p q)) =
          (c.ι.app j).hom (N a p q) :=
        congrArg (fun t : R.obj j ⟶ c.pt => t.hom (N a p q)) (c.w f)
      _ = M a p q := congrArg (fun X : Matrix (d (next a)) (d a) c.pt => X p q) (hN a)

/-- Matrix entries respect the cocone compatibility equation. -/
theorem matrix_map_cocone
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) (c : Cocone R)
    {m n : Type uA} {j k : I} (f : j ⟶ k)
    (N : Matrix m n (R.obj j)) :
    (N.map (R.map f).hom).map (c.ι.app k).hom =
      N.map (c.ι.app j).hom := by
  ext p q
  exact congrArg (fun t : R.obj j ⟶ c.pt => t.hom (N p q)) (c.w f)

/-- An idempotent matrix over the colimit lifts to an idempotent matrix at a stage. -/
private theorem idempotent_matrix_stage_exists
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat)]
    (c : Cocone R) (hc : IsColimit c)
    {n : Type uA} [Fintype n] [DecidableEq n]
    (M : Matrix n n c.pt) (hM : M * M = M) :
    ∃ (j : I) (N : Matrix n n (R.obj j)),
      N * N = N ∧ N.map (c.ι.app j).hom = M := by
  obtain ⟨j, N, hN⟩ := rectangular_matrix_stage_exists R c hc M
  obtain ⟨k, f, hf⟩ := rectangular_matrix_eventually_eq R c hc j (N * N) N
    (by rw [Matrix.map_mul, hN, hM])
  refine ⟨k, N.map (R.map f).hom, ?_, ?_⟩
  · rw [← Matrix.map_mul]
    exact hf
  · exact (matrix_map_cocone R c f N).trans hN

/-- An idempotent endomorphism of finite free coordinates descends to an idempotent
endomorphism at one stage, with the same matrix after scalar extension. -/
private theorem idempotent_linear_stage_exists
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat)]
    (c : Cocone R) (hc : IsColimit c) (n : ℕ)
    (e : (Fin n → c.pt) →ₗ[c.pt] (Fin n → c.pt))
    (he : e.comp e = e) :
    ∃ (j : I) (e' : (Fin n → R.obj j) →ₗ[R.obj j] (Fin n → R.obj j)),
      e'.comp e' = e' ∧
        (LinearMap.toMatrix' e').map (c.ι.app j).hom = LinearMap.toMatrix' e := by
  classical
  have hM : LinearMap.toMatrix' e * LinearMap.toMatrix' e =
      LinearMap.toMatrix' e := by
    rw [← LinearMap.toMatrix'_comp, he]
  obtain ⟨j, N, hN, hmap⟩ := idempotent_matrix_stage_exists R c hc
    (LinearMap.toMatrix' e) hM
  refine ⟨j, Matrix.toLin' N, ?_, ?_⟩
  · rw [← Matrix.toLin'_mul, hN]
  · simpa only [LinearMap.toMatrix'_toLin'] using hmap

/-- The idempotent model of a finite projective module can be chosen at a stage.
The stage image is again finite projective. -/
private theorem finite_projective_stage_idempotent_model
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat)]
    (c : Cocone R) (hc : IsColimit c)
    (P : Type (max uM uR)) [AddCommGroup P] [Module c.pt P]
    [Module.Finite c.pt P] [Module.Projective c.pt P] :
    ∃ (n : ℕ) (j : I)
      (e' : (Fin n → R.obj j) →ₗ[R.obj j] (Fin n → R.obj j))
      (e : (Fin n → c.pt) →ₗ[c.pt] (Fin n → c.pt)),
      e'.comp e' = e' ∧
        Module.Finite (R.obj j) e'.range ∧ Module.Projective (R.obj j) e'.range ∧
        (LinearMap.toMatrix' e').map (c.ι.app j).hom = LinearMap.toMatrix' e ∧
        Nonempty (P ≃ₗ[c.pt] e.range) := by
  obtain ⟨n, e, he, hmodel⟩ := finite_projective_idempotent_model (A := c.pt) P
  obtain ⟨j, e', he', hmap⟩ := idempotent_linear_stage_exists R c hc n e he
  obtain ⟨hfin, hproj⟩ := idempotent_range_finite_projective n e' he'
  exact ⟨n, j, e', e, he', hfin, hproj, hmap, hmodel⟩

/-- Finite projective modules descend across a filtered colimit of commutative rings.
The descended module is the image of an idempotent on a finite free module. -/
private theorem finite_projective_module_descends
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat)]
    (c : Cocone R) (hc : IsColimit c)
    (P : Type (max uM uR)) [AddCommGroup P] [Module c.pt P]
    [Module.Finite c.pt P] [Module.Projective c.pt P] :
    ∃ (n : ℕ) (j : I)
      (e' : (Fin n → R.obj j) →ₗ[R.obj j] (Fin n → R.obj j)),
      e'.comp e' = e' ∧
        Module.Finite (R.obj j) e'.range ∧ Module.Projective (R.obj j) e'.range ∧
        (letI : Algebra (R.obj j) c.pt := (c.ι.app j).hom.toAlgebra
         Nonempty (P ≃ₗ[c.pt] (c.pt ⊗[R.obj j] e'.range))) := by
  obtain ⟨n, j, e', e, he', hfin, hproj, hmap, ⟨hmodel⟩⟩ :=
    finite_projective_stage_idempotent_model R c hc P
  refine ⟨n, j, e', he', hfin, hproj, ?_⟩
  let : Algebra (R.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  have hbase := idempotent_range_baseChange_equiv (c.ι.app j).hom n e' he'
  have heq : Matrix.toLin' ((LinearMap.toMatrix' e').map (c.ι.app j).hom) = e := by
    rw [hmap, Matrix.toLin'_toMatrix']
  rw [heq] at hbase
  exact ⟨hmodel.trans hbase.symm⟩

/-- The module descent theorem in the universe and categorical form used by the perfect
complex statement. -/
private theorem finite_projective_module_descends_category
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat)]
    (c : Cocone R) (hc : IsColimit c)
    (P : ModuleCat.{max uM uR} c.pt)
    [Module.Finite c.pt P] [Module.Projective c.pt P] :
    ∃ (j : I) (Q : ModuleCat.{max uM uR} (R.obj j)),
      Module.Finite (R.obj j) Q ∧ Module.Projective (R.obj j) Q ∧
        Nonempty (P ≅ (ModuleCat.extendScalars.{uR, uR, max uM uR}
          (c.ι.app j).hom).obj Q) := by
  obtain ⟨n, j, e', he', hfin, hproj, ⟨hbase⟩⟩ :=
    finite_projective_module_descends R c hc P
  let : Module.Finite (R.obj j) e'.range := hfin
  let : Module.Projective (R.obj j) e'.range := hproj
  let Q : ModuleCat.{max uM uR} (R.obj j) :=
    ModuleCat.of (R.obj j) (ULift.{uM} e'.range)
  refine ⟨j, Q, inferInstance, inferInstance, ?_⟩
  let : Algebra (R.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  let u : e'.range ≃ₗ[R.obj j] ULift.{uM} e'.range := ULift.moduleEquiv.symm
  have h : P ≃ₗ[c.pt] (c.pt ⊗[R.obj j] ULift.{uM} e'.range) :=
    hbase.trans (LinearEquiv.baseChange (R.obj j) c.pt e'.range
      (ULift.{uM} e'.range) u)
  exact ⟨h.toModuleIso⟩

/-- A finite matrix multiplication equation over the colimit holds at one stage. -/
private theorem matrix_mul_stage_exists
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat)]
    (c : Cocone R) (hc : IsColimit c)
    {m n p : Type uA} [Fintype m] [Fintype n] [Fintype p] [DecidableEq n]
    (A : Matrix m n c.pt) (B : Matrix n p c.pt) (C : Matrix m p c.pt)
    (h : A * B = C) :
    ∃ (j : I) (A' : Matrix m n (R.obj j)) (B' : Matrix n p (R.obj j))
      (C' : Matrix m p (R.obj j)),
      A' * B' = C' ∧
      A'.map (c.ι.app j).hom = A ∧
      B'.map (c.ι.app j).hom = B ∧
      C'.map (c.ι.app j).hom = C := by
  classical
  let data : Sum (m × n) (Sum (n × p) (m × p)) → c.pt
    | .inl ij => A ij.1 ij.2
    | .inr (.inl ij) => B ij.1 ij.2
    | .inr (.inr ij) => C ij.1 ij.2
  obtain ⟨j, y, hy⟩ := finite_stage_exists R c hc data
  let A' : Matrix m n (R.obj j) := fun a b => y (.inl (a, b))
  let B' : Matrix n p (R.obj j) := fun a b => y (.inr (.inl (a, b)))
  let C' : Matrix m p (R.obj j) := fun a b => y (.inr (.inr (a, b)))
  have hA : A'.map (c.ι.app j).hom = A := by
    ext a b
    exact hy (.inl (a, b))
  have hB : B'.map (c.ι.app j).hom = B := by
    ext a b
    exact hy (.inr (.inl (a, b)))
  have hC : C'.map (c.ι.app j).hom = C := by
    ext a b
    exact hy (.inr (.inr (a, b)))
  obtain ⟨k, f, hf⟩ := rectangular_matrix_eventually_eq R c hc j (A' * B') C'
    (by rw [Matrix.map_mul, hA, hB, hC, h])
  refine ⟨k, A'.map (R.map f).hom, B'.map (R.map f).hom,
    C'.map (R.map f).hom, ?_, ?_, ?_, ?_⟩
  · rw [← Matrix.map_mul]
    exact hf
  · exact (matrix_map_cocone R c f A').trans hA
  · exact (matrix_map_cocone R c f B').trans hB
  · exact (matrix_map_cocone R c f C').trans hC

/-- Finitely many square matrices and finitely many multiplication relations between them
descend together. This packages the relations needed for finite diagrams of summands of free
modules, including idempotents and composites of differentials. -/
private theorem matrix_family_mul_stage_exists
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat)]
    (c : Cocone R) (hc : IsColimit c)
    {n α β : Type uA} [Fintype n] [DecidableEq n] [Fintype α] [Fintype β]
    (M : α → Matrix n n c.pt) (lhs rhs out : β → α)
    (h : ∀ b, M (lhs b) * M (rhs b) = M (out b)) :
    ∃ (j : I) (N : α → Matrix n n (R.obj j)),
      (∀ b, N (lhs b) * N (rhs b) = N (out b)) ∧
      (∀ a, (N a).map (c.ι.app j).hom = M a) := by
  classical
  obtain ⟨j, y, hy⟩ := finite_stage_exists R c hc
    (fun t : α × n × n => M t.1 t.2.1 t.2.2)
  let N : α → Matrix n n (R.obj j) := fun a p q => y (a, p, q)
  have hN (a : α) : (N a).map (c.ι.app j).hom = M a := by
    ext p q
    exact hy (a, p, q)
  have heq (t : β × n × n) :
      (c.ι.app j).hom ((N (lhs t.1) * N (rhs t.1)) t.2.1 t.2.2) =
        (c.ι.app j).hom ((N (out t.1)) t.2.1 t.2.2) := by
    have h' : (N (lhs t.1) * N (rhs t.1)).map (c.ι.app j).hom =
        (N (out t.1)).map (c.ι.app j).hom := by
      rw [Matrix.map_mul, hN, hN, hN, h]
    exact congrArg (fun X : Matrix n n c.pt => X t.2.1 t.2.2) h'
  obtain ⟨k, f, hf⟩ := finite_stage_eq R c hc j
    (fun t : β × n × n => (N (lhs t.1) * N (rhs t.1)) t.2.1 t.2.2)
    (fun t : β × n × n => (N (out t.1)) t.2.1 t.2.2) heq
  refine ⟨k, fun a => (N a).map (R.map f).hom, ?_, ?_⟩
  · intro b
    rw [← Matrix.map_mul]
    ext p q
    exact hf (b, p, q)
  · intro a
    exact (matrix_map_cocone R c f (N a)).trans (hN a)

end StacksDraft.Perfect

end
