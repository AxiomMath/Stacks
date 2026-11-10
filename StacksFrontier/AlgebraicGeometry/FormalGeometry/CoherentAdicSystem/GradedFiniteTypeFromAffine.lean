module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedFiniteType
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.ReesToAssociatedGraded
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Local
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteFromGeneratingSections

/-!
# The graded module of Tag 087Z is of finite type over the Rees algebra

Let `X` be a Noetherian scheme, `ℐ` a quasi-coherent sheaf of ideals and `(F_n)` an object of
`Coh(X, ℐ)`. [Stacks, Tag 087Z] (`Stacks.Coherent.finiteTypeAssociatedGradedData`) exhibits
`⨁ₙ Ker(F_{n+1} ⟶ F_n)` as a graded module over `⨁ₙ ℐⁿ/ℐⁿ⁺¹`, recorded as a
`Stacks.Coherent.AssociatedGradedData`. This file shows that, read over the Rees algebra
`⨁ₙ ℐⁿ` through `Stacks.Coherent.reesTransitionGradedModule`, it is of finite type in the
sheaf-theoretic sense of `SheafOfModules.GradedModule.IsFiniteType`, which is what the base
change of [Stacks, Tag 0897] to `Spec_X(⨁ₙ ℐⁿ)` consumes.

The proof is the source's: the module is generated in degree zero, and its degree-zero piece is
the coherent module `F_1`. Generation in degree zero is read off the public fields of
`Stacks.Coherent.AssociatedGradedData` alone — over an affine open `U` the degree-`k` piece is
`ℐ(U)ᵏ M / ℐ(U)ᵏ⁺¹ M` for the inverse limit `M` of the sections of the system
(`moduleAffinePiece`), the action is the associated graded action (`moduleAffineAction`), and
`ℐ(U)ᵏ M / ℐ(U)ᵏ⁺¹ M` is spanned by the classes of the products `a • m` with `a ∈ ℐ(U)ᵏ`. No
further field is asked of the datum, and no private declaration of the file constructing it is
used.

## Main results

* `Stacks.Coherent.associatedGraded_piece_mem_closure_smul`: the degree-`n` piece of the
  associated graded module of an ideal is additively spanned by the classes of the products
  `a • m` with `a ∈ Iⁿ`.
* `Stacks.Coherent.mem_closure_smul_modulePieceZero`: over an affine open, every homogeneous
  section of the graded module of [Stacks, Tag 087Z] is a sum of degree-zero sections scaled by
  the associated graded algebra.
* `Stacks.Coherent.exists_generates_of_isCoherent`: a coherent module is generated over every
  affine open by finitely many of its sections there.
* `Stacks.Coherent.isFiniteType_reesTransitionGradedModule`: the graded module of
  [Stacks, Tag 087Z] is of finite type over the Rees algebra.

## References

* [Stacks Project, Tag 087Z](https://stacks.math.columbia.edu/tag/087Z)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Coherent

/-! ### The associated graded module is generated in degree zero -/

/-- An element of `Iⁿ` scales any module element into `Iⁿ M`.

The file constructing `Stacks.Coherent.AssociatedGradedData` has this as a private lemma
(`associatedGraded_smul_mem_power_self`), so it is stated here for the public statements below. -/
theorem associatedGraded_smul_mem_power {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (n : ℕ) {a : A} (ha : a ∈ AssociatedGraded.power (M := A) I n) (m : M) :
    a • m ∈ AssociatedGraded.power (M := M) I n := by
  rw [AssociatedGraded.ring_power_eq] at ha
  exact Submodule.smul_mem_smul ha Submodule.mem_top

/-- **The degree-`n` piece `Iⁿ M / Iⁿ⁺¹ M` of the associated graded module is additively spanned by
the classes of the products `a • m` with `a ∈ Iⁿ` and `m ∈ M`.** An element of `Iⁿ M = Iⁿ • ⊤` is
a finite sum of such products, and taking classes is additive. -/
theorem associatedGraded_piece_mem_closure_smul {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (I : Ideal A) (n : ℕ) (x : AssociatedGraded.piece (M := M) I n) :
    x ∈ AddSubgroup.closure
      {z : AssociatedGraded.piece (M := M) I n |
        ∃ (a : AssociatedGraded.power (M := A) I n) (m : M),
          z = AssociatedGraded.mk I n
            ⟨(a : A) • m, associatedGraded_smul_mem_power I n a.property m⟩} := by
  set H := AddSubgroup.closure
      {z : AssociatedGraded.piece (M := M) I n |
        ∃ (a : AssociatedGraded.power (M := A) I n) (m : M),
          z = AssociatedGraded.mk I n
            ⟨(a : A) • m, associatedGraded_smul_mem_power I n a.property m⟩} with hH
  induction x using Quotient.inductionOn with
  | _ y =>
    have hy : (y : M) ∈ I ^ n • (⊤ : Submodule A M) := y.property
    have hPy : ∀ hz : (y : M) ∈ AssociatedGraded.power (M := M) I n,
        AssociatedGraded.mk I n ⟨(y : M), hz⟩ ∈ H := by
      refine Submodule.smul_induction_on' hy ?_ ?_
      · intro a ha m _ hmem
        have ha' : a ∈ AssociatedGraded.power (M := A) I n := by simpa using ha
        exact AddSubgroup.subset_closure ⟨⟨a, ha'⟩, m, rfl⟩
      · intro z hz w hw ihz ihw _
        change Submodule.Quotient.mk
          ((⟨z, hz⟩ : AssociatedGraded.power (M := M) I n) + ⟨w, hw⟩) ∈ H
        rw [Submodule.Quotient.mk_add]
        exact AddSubgroup.add_mem H (ihz hz) (ihw hw)
    exact hPy y.property

/-- Transport along a family of equivalences indexed by equal indices. -/
private lemma equiv_symm_heq_of_heq {ι : Type*} {P Q : ι → Type*}
    (e : ∀ i, P i ≃ Q i) {i j : ι} (h : i = j) (x : P i) (y : Q j)
    (hxy : HEq (e i x) y) : HEq ((e j).symm y) x := by
  subst j
  exact heq_of_eq ((e i).symm_apply_eq.mpr (eq_of_heq hxy).symm)

/-- `Iᵏ · I⁰ M` lands in degree `k + 0`, which is degree `k` on the nose. -/
private lemma homogeneousSMul_mk_zero_heq {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (I : Ideal A) (k : ℕ) (a : AssociatedGraded.power (M := A) I k) (m : M)
    (hm : m ∈ AssociatedGraded.power (M := M) I 0) :
    HEq (AssociatedGraded.homogeneousSMul I (AssociatedGraded.mk I k a)
        (AssociatedGraded.mk I 0 ⟨m, hm⟩))
      (AssociatedGraded.mk I k
        ⟨(a : A) • m, associatedGraded_smul_mem_power I k a.property m⟩) := HEq.refl _

/-- **Over an affine open, every homogeneous section of the graded module of [Stacks, Tag 087Z]
is a sum of degree-zero sections scaled by the associated graded algebra.**

Under the affine identification `moduleAffinePiece` the degree-`k` piece is `ℐ(U)ᵏ M / ℐ(U)ᵏ⁺¹ M`
for the inverse limit `M` of the sections of the system, which is spanned by the classes of
products `a • m` (`associatedGraded_piece_mem_closure_smul`); each such class is the associated
graded action of the class of `a` on the class of `m`, which `moduleAffineAction` identifies with
the action of the algebra on a degree-zero section. -/
theorem mem_closure_smul_modulePieceZero {X : Scheme.{u}} {I : X.IdealSheafData}
    {F : CoherentAdicSystems I} (D : AssociatedGradedData I F) (U : X.affineOpens) (k : ℕ)
    (t : (D.module.piece (k : ℤ)).val.obj (op U.1)) :
    t ∈ AddSubgroup.closure
      { s : (D.module.piece (k : ℤ)).val.obj (op U.1) |
        ∃ (y : (D.module.piece 0).val.obj (op U.1))
          (a : (D.algebra.piece (k : ℤ)).val.obj (op U.1))
          (h : (0 : ℤ) + (k : ℤ) = (k : ℤ)),
          s = h ▸ D.module.smul 0 (k : ℤ) (op U.1) y a } := by
  set H := AddSubgroup.closure
      { s : (D.module.piece (k : ℤ)).val.obj (op U.1) |
        ∃ (y : (D.module.piece 0).val.obj (op U.1))
          (a : (D.algebra.piece (k : ℤ)).val.obj (op U.1))
          (h : (0 : ℤ) + (k : ℤ) = (k : ℤ)),
          s = h ▸ D.module.smul 0 (k : ℤ) (op U.1) y a } with hH
  let e := D.moduleAffinePiece k U
  have hle : AddSubgroup.closure
      {z : AssociatedGraded.piece (M := sectionsLimit F U.1) (I.ideal U) k |
        ∃ (a : AssociatedGraded.power (M := Γ(X, U.1)) (I.ideal U) k) (m : sectionsLimit F U.1),
          z = AssociatedGraded.mk (I.ideal U) k
            ⟨(a : Γ(X, U.1)) • m, associatedGraded_smul_mem_power (I.ideal U) k a.property m⟩} ≤
      H.comap e.symm.toAddMonoidHom := by
    apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨a, m, rfl⟩
    apply AddSubgroup.subset_closure
    have hm0 : m ∈ AssociatedGraded.power (M := sectionsLimit F U.1) (I.ideal U) 0 := by simp
    have hh := D.moduleAffineAction 0 k U
      ((D.moduleAffinePiece 0 U).symm (AssociatedGraded.mk (I.ideal U) 0 ⟨m, hm0⟩))
      ((D.algebraPiece k U).symm (AssociatedGraded.mk (I.ideal U) k a))
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at hh
    exact ⟨_, _, zero_add _, eq_of_heq (heq_eqRec_iff.mpr (equiv_symm_heq_of_heq
      (fun j => (D.moduleAffinePiece j U).toEquiv) (Nat.zero_add k) _ _
      (hh.trans (homogeneousSMul_mk_zero_heq (I.ideal U) k a m hm0))))⟩
  have hx := hle (associatedGraded_piece_mem_closure_smul (I.ideal U) k (e t))
  change e.symm (e t) ∈ H at hx
  rwa [AddEquiv.symm_apply_apply] at hx

/-! ### Local generation of a coherent module over an affine open -/

/-- **A coherent module is generated over every affine open by finitely many of its sections
there**, in the sectionwise sense of `PresheafOfModules.Generates`. -/
theorem exists_generates_of_isCoherent {X : Scheme.{u}} (N : X.Modules)
    [_root_.SheafOfModules.IsCoherent N] (U : X.affineOpens) :
    ∃ (n : ℕ) (s : Fin n → N.val.obj (op U.1)),
      PresheafOfModules.Generates (Opens.grothendieckTopology X) N.val s := by
  have : N.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent N
  have : _root_.SheafOfModules.IsFiniteType.{u, u, u} N :=
    _root_.SheafOfModules.IsCoherent.isFiniteType
  obtain ⟨σ, hσ⟩ :=
    Stacks.AlgebraicGeometry.CoherentFinite.exists_finite_generatingSections_restrict N U.2
  refine Stacks.SheafOfModules.exists_generates_of_hasFiniteGlobalGenerators_over N U.1 ?_
  refine Stacks.SheafOfModules.hasFiniteGlobalGenerators_of_generatingSections _
    (Stacks.AlgebraicGeometry.CoherentTFAE.generatingSectionsOver U.1 N σ) ⟨?_⟩
  rw [Stacks.AlgebraicGeometry.CoherentTFAE.generatingSectionsOver_I]
  exact hσ

/-! ### Finite type of the transition-kernel graded module -/

open Stacks.Blowup (reesGradedAlgebra)

section FiniteType

variable {X : Scheme.{u}} [AlgebraicGeometry.IsNoetherian X] {I : X.IdealSheafData}
  {F : CoherentAdicSystems I} (D : AssociatedGradedData I F)

omit [AlgebraicGeometry.IsNoetherian X] in
/-- The degree-zero piece of the graded module of [Stacks, Tag 087Z] is coherent: it is the
zeroth term of the coherent adic system. -/
theorem isCoherent_modulePieceZero : (D.module.piece 0).IsCoherent :=
  have : _root_.SheafOfModules.IsCoherent.{u} (F.obj.obj (op 0)) := F.property.1 0
  Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso D.modulePieceZero

omit [AlgebraicGeometry.IsNoetherian X] in
/-- Transport of sections along an equality of degrees agrees with the dependent rewrite. -/
private theorem castHom_eq_eqRec {M : ℤ → SheafOfModules.{u} X.ringCatSheaf} {m k : ℤ}
    (h : m = k) (U : X.Opensᵒᵖ) (z : (M m).val.obj U) :
    _root_.SheafOfModules.castHom M h U z = h ▸ z := by
  subst h; rfl


omit [AlgebraicGeometry.IsNoetherian X] in
/-- **Over an affine open every homogeneous section of the transition-kernel module is a finite
sum of degree-zero sections scaled by the Rees algebra.** This is
`Stacks.Coherent.mem_closure_smul_modulePieceZero` with the coefficients lifted from the
associated graded algebra to the Rees algebra, which is possible because the lift is surjective
on affine charts (`Stacks.Coherent.exists_reesToAssociatedGraded_app_eq`). -/
theorem exists_sum_smulSection (k : ℤ) (W : X.affineOpens)
    (t : ((reesTransitionGradedModule D).piece k).val.obj (op W.1)) :
    ∃ (q : ℕ) (y : Fin q → ((reesTransitionGradedModule D).piece 0).val.obj (op W.1))
      (b : Fin q → ((reesGradedAlgebra I).piece (k - 0)).val.obj (op W.1)),
      ∑ j, (reesTransitionGradedModule D).smulSection k (y j) (b j) = t := by
  classical
  -- in negative degrees the piece vanishes, so the empty sum does it
  by_cases hk : k < 0
  · refine ⟨0, fun j => j.elim0, fun j => j.elim0, ?_⟩
    rw [Fin.sum_univ_zero]
    exact (sections_eq_zero_of_isZero _ (D.moduleNegative k hk) (op W.1) t).symm
  lift k to ℕ using le_of_not_gt hk
  set S := { s : (D.module.piece (k : ℤ)).val.obj (op W.1) |
      ∃ (y : (D.module.piece 0).val.obj (op W.1))
        (a : (D.algebra.piece (k : ℤ)).val.obj (op W.1))
        (h : (0 : ℤ) + (k : ℤ) = (k : ℤ)),
        s = h ▸ D.module.smul 0 (k : ℤ) (op W.1) y a } with hS
  have hmem : t ∈ AddSubgroup.closure S := mem_closure_smul_modulePieceZero D W k t
  set P : ((reesTransitionGradedModule D).piece (k : ℤ)).val.obj (op W.1) → Prop := fun s =>
    ∃ (q : ℕ) (y : Fin q → ((reesTransitionGradedModule D).piece 0).val.obj (op W.1))
      (b : Fin q → ((reesGradedAlgebra I).piece ((k : ℤ) - 0)).val.obj (op W.1)),
      ∑ j, (reesTransitionGradedModule D).smulSection (k : ℤ) (y j) (b j) = s with hPdef
  have hzero : P 0 := ⟨0, fun j => j.elim0, fun j => j.elim0, Fin.sum_univ_zero _⟩
  have hadd : ∀ s₁ s₂, P s₁ → P s₂ → P (s₁ + s₂) := by
    rintro s₁ s₂ ⟨q₁, y₁, b₁, h₁⟩ ⟨q₂, y₂, b₂, h₂⟩
    refine ⟨q₁ + q₂, Fin.append y₁ y₂, Fin.append b₁ b₂, ?_⟩
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [h₁, h₂]
  have hneg : ∀ s, P s → P (-s) := by
    rintro s ⟨q, y, b, h⟩
    refine ⟨q, fun j => -(y j), b, ?_⟩
    have hn : ∀ j, (reesTransitionGradedModule D).smulSection (k : ℤ) (-(y j)) (b j) =
        -((reesTransitionGradedModule D).smulSection (k : ℤ) (y j) (b j)) := by
      intro j
      rw [← SheafOfModules.GradedModule.smulSectionFlip_apply,
        ← SheafOfModules.GradedModule.smulSectionFlip_apply, map_neg]
    simp only [hn]
    rw [Finset.sum_neg_distrib, h]
  have hgen : ∀ s ∈ S, P s := by
    rintro s ⟨y, a, hdeg, rfl⟩
    obtain ⟨b, hb⟩ := exists_reesToAssociatedGraded_app_eq D.toAssociatedGradedAlgebraData W k a
    refine ⟨1, fun _ => y, fun _ => b, ?_⟩
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul, ← hb]
    exact castHom_eq_eqRec (M := D.module.piece) hdeg (op W.1) _
  exact AddSubgroup.closure_induction (p := fun s _ => P s) hgen hzero
    (fun s₁ s₂ _ _ => hadd s₁ s₂) (fun s _ => hneg s) hmem

/-- The sieve on an open consisting of the opens contained in some affine open contained in
it. The members of a covering sieve of this shape are exactly where the degree-zero generation
established above can be used, since it is stated over affine opens. -/
private def affineSubSieve (V : X.Opens) : Sieve V where
  arrows Z _ := ∃ W : X.affineOpens, Z ≤ W.1 ∧ W.1 ≤ V
  downward_closed := by
    rintro Y Z f ⟨W, hYW, hWV⟩ g
    exact ⟨W, le_trans g.le hYW, hWV⟩

omit [AlgebraicGeometry.IsNoetherian X] in
private theorem affineSubSieve_mem (V : X.Opens) :
    affineSubSieve (X := X) V ∈ Opens.grothendieckTopology X V := by
  rw [Opens.mem_grothendieckTopology]
  intro y hy
  obtain ⟨W, hW, hyW, hWV⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hy
  exact ⟨W, homOfLE hWV, ⟨⟨W, hW⟩, le_rfl, hWV⟩, hyW⟩

omit [AlgebraicGeometry.IsNoetherian X] in
/-- **The transition-kernel module of [Stacks, Tag 087Z] is of finite type over the Rees
algebra of `ℐ`**, in the sheaf-theoretic sense of
`SheafOfModules.GradedModule.IsFiniteType`.

The covering family is the affine opens. On one of them the degree-zero piece is coherent, so
finitely many of its sections generate it (`Stacks.Coherent.exists_generates_of_isCoherent`),
and every homogeneous section is locally a sum of degree-zero sections scaled by the Rees
algebra (`Stacks.Coherent.exists_sum_smulSection`); those are the two hypotheses of
`SheafOfModules.GradedModule.generates_of_degreeZero`. -/
theorem isFiniteType_reesTransitionGradedModule :
    (reesTransitionGradedModule D).IsFiniteType := by
  have := isCoherent_modulePieceZero D
  refine ⟨⟨X.affineOpens, fun V => V.1, ?_, fun V => ?_⟩⟩
  · refine (Opens.coversTop_iff X _).2 (TopologicalSpace.IsOpenCover.mk ?_)
    exact AlgebraicGeometry.iSup_affineOpens_eq_top X
  · obtain ⟨n, s, hs⟩ := exists_generates_of_isCoherent (D.module.piece 0) V
    refine ⟨n, fun _ => 0, s, SheafOfModules.GradedModule.generates_of_degreeZero
      (reesTransitionGradedModule D) s hs ?_⟩
    intro k V' x
    refine ⟨affineSubSieve V', affineSubSieve_mem V', ?_⟩
    rintro Z g ⟨W, hZW, hWV⟩
    obtain ⟨q, y, b, hsum⟩ := exists_sum_smulSection D k W
      (((reesTransitionGradedModule D).piece k).val.restrictₛₗ (homOfLE hWV).op x)
    refine ⟨q, fun j => ((reesTransitionGradedModule D).piece 0).val.restrictₛₗ
        (homOfLE hZW).op (y j),
      fun j => ((reesGradedAlgebra I).piece (k - 0)).val.restrictₛₗ (homOfLE hZW).op (b j), ?_⟩
    have hres : ∀ j, (reesTransitionGradedModule D).smulSection k
        (((reesTransitionGradedModule D).piece 0).val.restrictₛₗ (homOfLE hZW).op (y j))
        (((reesGradedAlgebra I).piece (k - 0)).val.restrictₛₗ (homOfLE hZW).op (b j)) =
        ((reesTransitionGradedModule D).piece k).val.restrictₛₗ (homOfLE hZW).op
          ((reesTransitionGradedModule D).smulSection k (y j) (b j)) := fun j =>
      (SheafOfModules.GradedModule.smulSection_restrictₛₗ _ k (homOfLE hZW).op (y j) (b j)).symm
    simp only [hres]
    rw [← map_sum, hsum]
    exact SheafOfModules.GradedModule.restrictₛₗ_restrictₛₗ _ (homOfLE hWV) (homOfLE hZW) x

end FiniteType

end Stacks.Coherent

end
