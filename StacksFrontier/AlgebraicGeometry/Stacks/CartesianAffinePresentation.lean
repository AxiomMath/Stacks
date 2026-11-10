module

public import StacksFrontier.AlgebraicGeometry.Stacks.CoherenceConditionsCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentCokernelLocallyNoetherian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PresentationOfSections

/-!
# A module cartesian between affine objects is presented over an affine object

Let `𝒳` be a category fibred in groupoids over the big fppf site and `M` an `𝒪_𝒳`-module whose
sections are cartesian between objects lying over affine schemes (which every quasi-coherent
module is, `AlgebraicGeometry.Stack.isCartesianBetweenAffines_of_isQuasicoherentOnSite`). Over an
object `z` lying over an affine scheme, `M|_{𝒳/z}` is the cokernel of `⊕_K O ⟶ ⊕_I O` where `I`
is the set of sections `M(z)` and `K` the set of relations among them; both are sets in the
universe of the schemes, so this is a global presentation at the universe of the sections
(Stacks 03DE (6)), the form in which `g_!` acts on it. For a finitely presented `M(z)` this is
`AlgebraicGeometry.Stack.hasFiniteGlobalPresentation_over_of_finitePresentation`.

## Main results

* `Module.BaseChange.exists_finsupp_of_bijective_liftBaseChange` and
  `Module.BaseChange.exists_finsupp_relations_of_bijective_liftBaseChange`: the two algebraic
  steps, for a bijective base change comparison.
* `AlgebraicGeometry.Stack.isPresentedByGlobalSections_over_of_isCartesianBetweenAffines`.

## References

* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 0H0E](https://stacks.math.columbia.edu/tag/0H0E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Module.BaseChange

variable {A Bc NT NW : Type*} [CommRing A] [CommRing Bc] [Algebra A Bc]
  [AddCommGroup NT] [Module A NT] [AddCommGroup NW] [Module A NW] [Module Bc NW]
  [IsScalarTower A Bc NW] (rN : NT →ₗ[A] NW)

/-- If the base change comparison of `rN` is surjective, every element of the target is a finite
combination of images. -/
theorem exists_finsupp_of_surjective_liftBaseChange
    (h : Function.Surjective (rN.liftBaseChange Bc)) (m : NW) :
    ∃ c : NT →₀ Bc, (c.sum fun i r ↦ r • rN i) = m := by
  classical
  obtain ⟨ζ, rfl⟩ := h m
  induction ζ using TensorProduct.inductionOn with
  | tmul b n =>
    refine ⟨Finsupp.single n b, ?_⟩
    rw [Finsupp.sum_single_index (h := fun i r ↦ r • rN i) (zero_smul _ _),
      LinearMap.liftBaseChange_tmul]
  | add ζ₁ ζ₂ h₁ h₂ =>
    obtain ⟨c₁, hc₁⟩ := h₁
    obtain ⟨c₂, hc₂⟩ := h₂
    refine ⟨c₁ + c₂, ?_⟩
    rw [Finsupp.sum_add_index' (h := fun i r ↦ r • rN i) (fun _ ↦ zero_smul _ _)
      (fun _ _ _ ↦ add_smul _ _ _), hc₁, hc₂, map_add]

/-- The relations among all elements of an `A`-module. -/
abbrev Relations (A NT : Type*) [CommRing A] [AddCommGroup NT] [Module A NT] :=
  {c : NT →₀ A // (c.sum fun i r ↦ r • i) = 0}

/-- **Right exactness of the base change of a presentation by all elements.** If the base change
comparison of `rN` is bijective, every relation among the images of the elements of `NT` is a
combination of the images of the relations among the elements of `NT`. -/
theorem exists_finsupp_relations_of_bijective_liftBaseChange
    (h : Function.Bijective (rN.liftBaseChange Bc)) (c : NT →₀ Bc)
    (hc : (c.sum fun i r ↦ r • rN i) = 0) :
    ∃ d : Relations A NT →₀ Bc,
      c = d.sum fun k r ↦ r • k.1.mapRange (algebraMap A Bc) (map_zero _) := by
  classical
  let bT : (NT →₀ A) →ₗ[A] NT := Finsupp.linearCombination A id
  let bW : (NT →₀ Bc) →ₗ[Bc] NW := Finsupp.linearCombination Bc rN
  let rP : (NT →₀ A) →ₗ[A] (NT →₀ Bc) := Finsupp.mapRange.linearMap (Algebra.linearMap A Bc)
  have hsqb : ∀ q, rN (bT q) = bW (rP q) := by
    intro q
    simp only [bT, bW, rP, Finsupp.linearCombination_apply, Finsupp.mapRange.linearMap_apply,
      id, map_finsuppSum, map_smul]
    rw [Finsupp.sum_mapRange_index (h := fun i a ↦ a • rN i) (fun _ ↦ zero_smul _ _)]
    exact Finset.sum_congr rfl fun i _ ↦ (algebraMap_smul Bc (q i) (rN i)).symm
  have hP : Function.Surjective (rP.liftBaseChange Bc) :=
    (Module.BaseChange.bijective_liftBaseChange_of_basis (Finsupp.basisSingleOne)
      (Finsupp.basisSingleOne) rP fun i ↦ by
        simp [rP, Finsupp.mapRange_single]).2
  have hbT : Function.Surjective bT := fun n ↦ ⟨Finsupp.single n 1, by simp [bT]⟩
  have hmem := Module.BaseChange.mem_span_image_ker_of_liftBaseChange bT bW rP rN hsqb hP h.1 hbT
    (z := c) (by simpa [bW, Finsupp.linearCombination_apply] using hc)
  have himg : rP '' (LinearMap.ker bT : Set (NT →₀ A)) =
      Set.range fun k : Relations A NT ↦ rP k.1 := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, by simpa [bT, Finsupp.linearCombination_apply] using hq⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k.1, by simpa [bT, Finsupp.linearCombination_apply] using k.2, rfl⟩
  rw [himg, Finsupp.mem_span_range_iff_exists_finsupp] at hmem
  exact hmem.imp fun _ h ↦ h.symm

end Module.BaseChange

/-- A ring homomorphism applied coefficientwise to a finite combination of finitely supported
functions. -/
theorem Finsupp.mapRange_sum_smul {K I A A' : Type*} [Semiring A] [Semiring A'] (f : A →+* A')
    (d : K →₀ A) (v : K → I →₀ A) :
    (d.sum fun k r ↦ r • v k).mapRange f (map_zero f) =
      (d.mapRange f (map_zero f)).sum fun k r ↦ r • (v k).mapRange f (map_zero f) := by
  classical
  rw [Finsupp.sum_mapRange_index (h := fun k r ↦ r • (v k).mapRange f (map_zero f))
    (fun _ ↦ zero_smul _ _)]
  change Finsupp.mapRange.addMonoidHom f.toAddMonoidHom (d.sum fun k r ↦ r • v k) = _
  rw [map_finsuppSum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  ext i
  simp

/-- `Over.mk (𝟙 z)` is terminal in `Over z`, with the structure morphisms as the maps to it. -/
def CategoryTheory.Over.isTerminalMkId {C : Type*} [Category C] (z : C) :
    IsTerminal (Over.mk (𝟙 z)) :=
  IsTerminal.ofUniqueHom (fun W ↦ Over.homMk W.hom (by simp))
    (fun W m ↦ Over.OverMorphism.ext (by simpa using Over.w m))

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  [EssentiallySmall.{u} 𝒳]

/-- **A module cartesian between affine objects has a global presentation over each affine
object, at the universe of the sections**: over `z`, generators all of `M(z)` and relations all
the relations among them. -/
theorem isPresentedByGlobalSections_over_of_isCartesianBetweenAffines
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
    (hM : IsCartesianBetweenAffines hp M) {z : 𝒳}
    (hz : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj z)) :
    (M.over z).IsPresentedByGlobalSections := by
  classical
  let := fibredSectionsModule hp M z
  have hloc : ∀ {y : 𝒳} (h : y ⟶ z), IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj y) →
      letI := fibredSectionsModule hp M y
      (∀ m : M.val.obj (op y), ∃ c : M.val.obj (op z) →₀ fibredSectionRing B S hS p y,
        (c.sum fun i r ↦ r • (show M.val.obj (op y) from M.val.map h.op i)) = m) ∧
      ∀ c : M.val.obj (op z) →₀ fibredSectionRing B S hS p y,
        (c.sum fun i r ↦ r • (show M.val.obj (op y) from M.val.map h.op i)) = 0 →
          ∃ d : Module.BaseChange.Relations (fibredSectionRing B S hS p z) (M.val.obj (op z)) →₀
              fibredSectionRing B S hS p y,
            c = d.sum fun k r ↦ r • k.1.mapRange (fibredSectionRestrict h) (map_zero _) := by
    intro y h hy
    let := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := p) h
    let := fibredSectionsModule hp M y
    let := fibredSectionsModuleOver hp M h
    have : IsScalarTower (fibredSectionRing B S hS p z) (fibredSectionRing B S hS p y)
        (M.val.obj (op y)) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    have hb : Function.Bijective ((fibredSectionsRestrict hp M h).liftBaseChange
        (fibredSectionRing B S hS p y)) := hM h hz hy
    exact ⟨Module.BaseChange.exists_finsupp_of_surjective_liftBaseChange
      (fibredSectionsRestrict hp M h) hb.2,
      Module.BaseChange.exists_finsupp_relations_of_bijective_liftBaseChange
        (fibredSectionsRestrict hp M h) hb⟩
  refine (Stacks.SheafOfModules.FreeSheafification.isPresentedByGlobalSections_of_terminal
    (Over.mk (𝟙 z)) (Over.isTerminalMkId z) (M.over z) (M.val.obj (op z))
    (Module.BaseChange.Relations (fibredSectionRing B S hS p z) (M.val.obj (op z)))
    (fun i ↦ i) (fun k ↦ k.1) (fun k ↦ k.2) ?_ ?_).1
  · intro V x
    obtain ⟨ι, y, φ, hyaff, hcov, -⟩ := FibredSite.exists_affine_fppf_ofArrows B S hS p hp V.left
    refine ⟨(Sieve.overEquiv V).symm (Sieve.ofArrows y φ),
      GrothendieckTopology.overEquiv_symm_mem_over _ V _ hcov, fun W g hg ↦ ?_⟩
    obtain ⟨j, e, he⟩ := (Sieve.mem_ofArrows_iff y φ g.left).1 (by simpa using hg)
    obtain ⟨c, hc⟩ := (hloc (φ j ≫ V.hom) (hyaff j)).1 (M.val.map (φ j).op x)
    let := fibredSectionsModule hp M W.left
    change ∃ c' : M.val.obj (op z) →₀ fibredSectionRing B S hS p W.left,
      (c'.sum fun i r ↦ r • (show M.val.obj (op W.left) from M.val.map W.hom.op i)) =
        M.val.map g.left.op x
    have hx : M.val.map g.left.op x = M.val.map e.op (M.val.map (φ j).op x) :=
      (M.val.congr_map_apply (congrArg Quiver.Hom.op he) x).trans
        (M.val.map_comp_apply (φ j).op e.op x)
    refine ⟨c.mapRange (fibredSectionRestrict e) (map_zero _),
      Eq.trans ?_ ((congrArg (fun m ↦ M.val.map e.op m) hc).trans hx.symm)⟩
    refine Eq.trans ?_ (Stacks.SheafOfModules.FreeSheafification.map_finsupp_sum_smul M.val e.op
      c (fun i ↦ M.val.map (φ j ≫ V.hom).op i)).symm
    refine Finset.sum_congr rfl fun i _ ↦ congrArg (_ • ·) ?_
    exact (M.val.congr_map_apply (show W.hom.op = (φ j ≫ V.hom).op ≫ e.op by
      rw [← op_comp, ← Category.assoc, ← he, Over.w g]) i).trans (M.val.map_comp_apply _ _ i)
  · intro V c hc0
    let := fibredSectionsModule hp M V.left
    change (c.sum fun i r ↦ (show fibredSectionRing B S hS p V.left from r) •
      (show M.val.obj (op V.left) from M.val.map V.hom.op i)) = 0 at hc0
    obtain ⟨ι, y, φ, hyaff, hcov, -⟩ := FibredSite.exists_affine_fppf_ofArrows B S hS p hp V.left
    refine ⟨(Sieve.overEquiv V).symm (Sieve.ofArrows y φ),
      GrothendieckTopology.overEquiv_symm_mem_over _ V _ hcov, fun W g hg ↦ ?_⟩
    obtain ⟨j, e, he⟩ := (Sieve.mem_ofArrows_iff y φ g.left).1 (by simpa using hg)
    let := fibredSectionsModule hp M (y j)
    let cj : M.val.obj (op z) →₀ fibredSectionRing B S hS p (y j) :=
      c.mapRange (fibredSectionRestrict (φ j)) (map_zero _)
    obtain ⟨d, hd⟩ := (hloc (φ j ≫ V.hom) (hyaff j)).2 cj (by
      have h0 := (Stacks.SheafOfModules.FreeSheafification.map_finsupp_sum_smul M.val (φ j).op c
        (fun i ↦ (show M.val.obj (op V.left) from M.val.map V.hom.op i))).symm.trans
        ((congrArg (fun m ↦ M.val.map (φ j).op m) hc0).trans (map_zero _))
      refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) h0
      exact congrArg (cj i • ·) (M.val.map_comp_apply V.hom.op (φ j).op i))
    change ∃ d' : Module.BaseChange.Relations (fibredSectionRing B S hS p z) (M.val.obj (op z)) →₀
        fibredSectionRing B S hS p W.left,
      c.mapRange (fibredSectionRestrict g.left) (map_zero _) =
        d'.sum fun k r ↦ r • k.1.mapRange (fibredSectionRestrict W.hom) (map_zero _)
    refine ⟨d.mapRange (fibredSectionRestrict e) (map_zero _), ?_⟩
    have hcomp : c.mapRange (fibredSectionRestrict g.left) (map_zero _) =
        cj.mapRange (fibredSectionRestrict e) (map_zero _) := by
      ext i
      simp only [cj, Finsupp.mapRange_apply, he]
      exact fibredSectionRestrict_comp (φ j) e (c i)
    rw [hcomp, hd, Finsupp.mapRange_sum_smul (fibredSectionRestrict e)]
    refine Finset.sum_congr rfl fun k _ ↦ congrArg (_ • ·) ?_
    ext i
    simp only [Finsupp.mapRange_apply]
    show fibredSectionRestrict e (fibredSectionRestrict (φ j ≫ V.hom) (k.1 i)) =
      fibredSectionRestrict W.hom (k.1 i)
    rw [← fibredSectionRestrict_comp, ← Category.assoc, ← he, Over.w g]

end AlgebraicGeometry.Stack
