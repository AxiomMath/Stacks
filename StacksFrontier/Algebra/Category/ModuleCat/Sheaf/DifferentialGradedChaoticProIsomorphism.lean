module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticRefinement
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticSystemHom
public import StacksFrontier.Algebra.DifferentialGraded.AlgebraSystemProIso
public import Mathlib.Order.Interval.Finset.Defs

/-!
# Pro-isomorphic inverse systems of differential graded algebras

Let `R` be a ring, let `ι` carry the chaotic topology and the constant sheaf of rings with value
`R`, and let `(A_n)` and `(B_n)` be inverse systems of differential graded `R`-algebras indexed by
`ι`, realized as sheaves of differential graded algebras `𝒜` and `ℬ` on `ι`. A morphism of
pro-objects `φ : (A_n) → (B_n)` is represented by a monotone reindexing `m : ι → ι` and
homomorphisms `φ_n : A_{m(n)} → B_n` compatible with the transition maps (Categories,
Example 4.22.6); it induces the derived pullback `QC(𝒜) ⥤ QC(ℬ)` of Tag 0GZC along the morphism of
chaotic sites given by `m`. Lemma 24.35.1 (Tag 0GZH) says that if `φ` is an isomorphism of
pro-objects, this functor is an equivalence.

## Main definitions

* `DifferentialGradedAlgebra.SystemProHom`: a representative of a morphism of pro-objects.
* `DifferentialGradedAlgebra.SystemProHom.IsInverse`: two representatives define mutually
  inverse morphisms of pro-objects: each composite agrees with the transition maps after
  restriction to a further stage.
* `DifferentialGradedAlgebra.SystemProHom.qcPullback`: **the functor `QC(𝒜) ⥤ QC(ℬ)` induced by a
  representative of a morphism of pro-objects.**
* `DifferentialGradedAlgebra.SystemProIso.qcEquivalence`: the equivalence `QC(𝒜) ≌ QC(ℬ)`
  attached to representatives whose composites are transition maps on the nose.

## Main results

* `DifferentialGradedAlgebra.SystemProHom.isEquivalence_qcPullback`: **Tag 0GZH.**

## Implementation notes

The source's index category is `ℕ`. The statements are made for a linearly ordered type
`ι : Type u` whose lower sets `{j ≤ i}` are finite, of which `ℕ` (for `u = 0`) and
`ULift.{u} ℕ` are instances; this keeps the site in the universe of the ring,
which is where the derived category and the derived pullback live. The finiteness is what lets a
reindexing be enlarged to a monotone one dominating finitely many given values at each stage,
the step "after possibly increasing the values of the functions `n(·)` and `m(·)`" of the
source's proof.

The proof is the source's. First the reindexing `m` of the representative of `φ` is replaced by
`m' = max(m, id)`, which defines the same morphism of pro-objects and an isomorphic functor
(`SheafOfModules.DifferentialGradedModule.chaoticQCPullbackRefineIso`). Then the reindexing `n`
of a representative of the inverse is enlarged so that both composites `A_{m'(n(i))} → A_i` and
`B_{n(m'(i))} → B_i` are transition maps, and the two derived pullbacks are mutually
quasi-inverse on quasi-coherent objects
(`SheafOfModules.DifferentialGradedModule.chaoticQCEquivalence`).

## References

* [Stacks Project, Section 24.35 (Tag 0GZG)](https://stacks.math.columbia.edu/tag/0GZG)
* [Stacks Project, Lemma 24.35.1 (Tag 0GZH)](https://stacks.math.columbia.edu/tag/0GZH)
* [Stacks Project, Example 4.22.6 (Tag 05PY)](https://stacks.math.columbia.edu/tag/05PY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf Opposite

universe m u

/-! ### Composites of homomorphisms of section algebras -/

namespace SheafOfModules.DifferentialGradedAlgebra.InverseImageHom

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra

variable {C : Type*} [Category C] {C' : Type*} [Category C']
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  {Osharp' : Sheaf (⊥ : GrothendieckTopology C') CommRingCat.{u}}
  {A : DifferentialGradedAlgebra.{u, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
  {A' : DifferentialGradedAlgebra.{u, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp')}

/-- The composite of the homomorphisms of section algebras of two maps along functors of chaotic
sites is the restriction homomorphism along `η_U` as soon as it is so degreewise on sections. -/
theorem sectionHom_comp_eq_of_app {F₁ : C' ⥤ C} {F₂ : C ⥤ C'}
    {σ₁ : F₁.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf Osharp').obj}
    {σ₂ : F₂.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf Osharp').obj ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj}
    (φ₁ : InverseImageHom F₁ σ₁ A A') (φ₂ : InverseImageHom F₂ σ₂ A' A) (U : Cᵒᵖ)
    (a : F₁.op.obj (F₂.op.obj U) ⟶ U)
    (h : ∀ (n : ℤ) (x : (A.complex.X n).val.obj (F₁.op.obj (F₂.op.obj U))),
      φ₂.app n U (φ₁.app n (F₂.op.obj U) x) = (A.complex.X n).val.map a x)
    (b : (A.sectionAlgebra (F₁.op.obj (F₂.op.obj U))).A) :
    (φ₂.sectionHom U).toAlgebraHom ((φ₁.sectionHom (F₂.op.obj U)).toAlgebraHom b) =
      (A.sectionRestriction a).toAlgebraHom b := by
  have key : (φ₂.sectionRing U).comp (φ₁.sectionRing (F₂.op.obj U)) =
      A.sectionRestrictRing a := by
    refine DirectSum.ringHom_ext fun n p => ?_
    simp only [RingHom.coe_comp, Function.comp_apply, sectionRestrictRing_of, sectionRing_of]
    exact congrArg (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) n) (h n p)
  exact DFunLike.congr_fun key b

/-- A map along a functor of chaotic sites precomposed with restriction along `τ_{U'}` has the
homomorphism of section algebras of the composite as soon as it is so degreewise on sections. -/
theorem sectionHom_restriction_eq_of_app {F F' : C' ⥤ C}
    {σ : F.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf Osharp').obj}
    {σ' : F'.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf Osharp').obj}
    (φ : InverseImageHom F σ A A') (φ' : InverseImageHom F' σ' A A') (U' : C'ᵒᵖ)
    (a : F'.op.obj U' ⟶ F.op.obj U')
    (h : ∀ (n : ℤ) (x : (A.complex.X n).val.obj (F'.op.obj U')),
      φ.app n U' ((A.complex.X n).val.map a x) = φ'.app n U' x)
    (b : (A.sectionAlgebra (F'.op.obj U')).A) :
    (φ.sectionHom U').toAlgebraHom ((A.sectionRestriction a).toAlgebraHom b) =
      (φ'.sectionHom U').toAlgebraHom b := by
  have key : (φ.sectionRing U').comp (A.sectionRestrictRing a) = φ'.sectionRing U' := by
    refine DirectSum.ringHom_ext fun n p => ?_
    simp only [RingHom.coe_comp, Function.comp_apply, sectionRestrictRing_of, sectionRing_of]
    exact congrArg (DirectSum.of (A'.toGradedAlgebra.sectionsPiece U') n) (h n p)
  exact DFunLike.congr_fun key b

end SheafOfModules.DifferentialGradedAlgebra.InverseImageHom

namespace DifferentialGradedAlgebra

open SheafOfModules.DifferentialGradedModule Stacks.ChaoticSite

variable {R : Type u} [CommRing R]

/-! ### Pro-isomorphisms with on-the-nose composites -/

section Preorder

variable {ι : Type u} [Preorder ι]

/-- **The sheaf of differential graded algebras of an inverse system** `(A_i)` on the chaotic site
`ι` with the constant sheaf of rings `R`: `Stacks.ChaoticSite.systemAlgebra`, its sheaf of rings
written as the sheaf of rings underlying the constant sheaf of commutative rings, which is the form
the derived pullback of a functor of chaotic sites is stated over. -/
abbrev systemSheaf (A : ιᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} R) :
    SheafOfModules.DifferentialGradedAlgebra.{u, u}
      (toRingCat (⊥ : GrothendieckTopology ι) (Stacks.PresheafOfModules.constCommRingSheaf R)) :=
  systemAlgebra A

namespace SystemProIso

variable {A B : ιᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} R}

/-- The transition morphisms `F₁ F₂ i ⟶ i` of `ιᵒᵖ` of the round trip of `(A_i)`. -/
def transition₁ (e : SystemProIso A B) : e.F₂.op ⋙ e.F₁.op ⟶ 𝟭 ιᵒᵖ where
  app U := (homOfLE (e.le₁ U.unop)).op
  naturality _ _ _ := Subsingleton.elim _ _

/-- The transition morphisms `F₂ F₁ i ⟶ i` of `ιᵒᵖ` of the round trip of `(B_i)`. -/
def transition₂ (e : SystemProIso A B) : e.F₁.op ⋙ e.F₂.op ⟶ 𝟭 ιᵒᵖ where
  app U := (homOfLE (e.le₂ U.unop)).op
  naturality _ _ _ := Subsingleton.elim _ _

/-- The round trip `A_{F₁ F₂ i} → B_{F₂ i} → A_i` of section algebras is the restriction
homomorphism. -/
theorem sectionHom_inv_sectionHom_hom (e : SystemProIso A B) (U : ιᵒᵖ)
    (b : ((systemSheaf A).sectionAlgebra (e.F₁.op.obj (e.F₂.op.obj U))).A) :
    ((systemInverseImageHom e.F₂ e.inv).sectionHom U).toAlgebraHom
        (((systemInverseImageHom e.F₁ e.hom).sectionHom (e.F₂.op.obj U)).toAlgebraHom b) =
      ((systemSheaf A).sectionRestriction (e.transition₁.app U)).toAlgebraHom b :=
  SheafOfModules.DifferentialGradedAlgebra.InverseImageHom.sectionHom_comp_eq_of_app _ _ U _
    (fun n (x : ((systemComplex A).X n).val.obj (e.F₁.op.obj (e.F₂.op.obj U))) => Subtype.ext
      (congrArg (fun g : DifferentialGradedAlgebra.Hom _ _ => g.toAlgebraHom x.val)
        (e.hom_inv U.unop))) b

/-- The round trip `B_{F₂ F₁ i} → A_{F₁ i} → B_i` of section algebras is the restriction
homomorphism. -/
theorem sectionHom_hom_sectionHom_inv (e : SystemProIso A B) (U : ιᵒᵖ)
    (b : ((systemSheaf B).sectionAlgebra (e.F₂.op.obj (e.F₁.op.obj U))).A) :
    ((systemInverseImageHom e.F₁ e.hom).sectionHom U).toAlgebraHom
        (((systemInverseImageHom e.F₂ e.inv).sectionHom (e.F₁.op.obj U)).toAlgebraHom b) =
      ((systemSheaf B).sectionRestriction (e.transition₂.app U)).toAlgebraHom b :=
  SheafOfModules.DifferentialGradedAlgebra.InverseImageHom.sectionHom_comp_eq_of_app _ _ U _
    (fun n (x : ((systemComplex B).X n).val.obj (e.F₂.op.obj (e.F₁.op.obj U))) => Subtype.ext
      (congrArg (fun g : DifferentialGradedAlgebra.Hom _ _ => g.toAlgebraHom x.val)
        (e.inv_hom U.unop))) b

/-- **The equivalence `QC(𝒜) ≌ QC(ℬ)` of a pro-isomorphism with on-the-nose composites**: its
functor is the derived pullback along the representative `A_{F₁ i} → B_i`, its quasi-inverse the
derived pullback along the representative `B_{F₂ i} → A_i`. -/
def qcEquivalence (e : SystemProIso A B) :
    Chaotic.QCFullSubcategory (systemSheaf A) ≌ Chaotic.QCFullSubcategory (systemSheaf B) :=
  chaoticQCEquivalence.{u, u} (systemInverseImageHom e.F₁ e.hom) (systemInverseImageHom e.F₂ e.inv)
    e.transition₁ e.sectionHom_inv_sectionHom_hom e.transition₂ e.sectionHom_hom_sectionHom_inv

/-- The functor of `qcEquivalence` is the derived pullback along the representative
`A_{F₁ i} → B_i`. -/
theorem qcEquivalence_functor (e : SystemProIso A B) :
    e.qcEquivalence.functor = chaoticQCPullback.{u, u} (systemInverseImageHom e.F₁ e.hom) :=
  rfl

end SystemProIso

/-! ### Representatives of morphisms of pro-objects -/

/-- **A representative of a morphism of pro-objects** `(A_i) → (B_i)` of inverse systems of
differential graded algebras indexed by `ι` (Categories, Example 4.22.6): a monotone reindexing
`F : ι ⥤ ι` together with homomorphisms `A_{F i} → B_i` compatible with the transition maps. -/
structure SystemProHom (A B : ιᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} R) where
  /-- The reindexing `i ↦ m(i)`. -/
  F : ι ⥤ ι
  /-- The homomorphisms `A_{m(i)} → B_i`. -/
  hom : F.op ⋙ A ⟶ B

namespace SystemProHom

variable {A B : ιᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} R}

/-- **Two representatives define mutually inverse morphisms of pro-objects**: each of the two
composites `A_{m(n(i))} → B_{n(i)} → A_i` and `B_{n(m(i))} → A_{m(i)} → B_i` defines the identity
morphism of pro-objects, that is, agrees with the transition map after restriction to a further
stage (Categories, Example 4.22.6). -/
structure IsInverse (φ : SystemProHom A B) (ψ : SystemProHom B A) : Prop where
  /-- The composite `A_{m(n(i))} → B_{n(i)} → A_i` agrees with the transition map after
  restriction to a further stage. -/
  hom_inv (i : ι) : ∃ (k : ι) (h₁ : φ.F.obj (ψ.F.obj i) ≤ k) (h₂ : i ≤ k),
    A.map (homOfLE h₁).op ≫ φ.hom.app (op (ψ.F.obj i)) ≫ ψ.hom.app (op i) =
      A.map (homOfLE h₂).op
  /-- The composite `B_{n(m(i))} → A_{m(i)} → B_i` agrees with the transition map after
  restriction to a further stage. -/
  inv_hom (i : ι) : ∃ (k : ι) (h₁ : ψ.F.obj (φ.F.obj i) ≤ k) (h₂ : i ≤ k),
    B.map (homOfLE h₁).op ≫ ψ.hom.app (op (φ.F.obj i)) ≫ φ.hom.app (op i) =
      B.map (homOfLE h₂).op

/-- **The morphism of pro-objects represented by `φ` is an isomorphism**: some representative of a
morphism of pro-objects in the other direction is inverse to it. -/
def IsProIso (φ : SystemProHom A B) : Prop :=
  ∃ ψ : SystemProHom B A, φ.IsInverse ψ

/-- **The functor `QC(𝒜) ⥤ QC(ℬ)` induced by a representative of a morphism of pro-objects**:
the derived pullback (Tag 0GZC) along the morphism of chaotic sites given by the reindexing and
the homomorphisms `A_{m(i)} → B_i`. On a good module `(M_n)` it is
`(M_{m(n)} ⊗_{A_{m(n)}} B_n)`. -/
def qcPullback (φ : SystemProHom A B) :
    Chaotic.QCFullSubcategory (systemSheaf A) ⥤ Chaotic.QCFullSubcategory (systemSheaf B) :=
  chaoticQCPullback.{u, u} (systemInverseImageHom φ.F φ.hom)

/-- The representative `A_{m'(i)} → A_{m(i)} → B_i` obtained by enlarging the reindexing along
`τ : m ≤ m'`. -/
def refine (φ : SystemProHom A B) (F' : ι ⥤ ι) (τ : F'.op ⟶ φ.F.op) : SystemProHom A B where
  F := F'
  hom := Functor.whiskerRight τ A ≫ φ.hom

/-- **Enlarging the reindexing of a representative does not change the functor
`QC(𝒜) ⥤ QC(ℬ)`**, up to isomorphism. -/
def refineQCPullbackIso (φ : SystemProHom A B) (F' : ι ⥤ ι) (τ : F'.op ⟶ φ.F.op) :
    (φ.refine F' τ).qcPullback ≅ φ.qcPullback :=
  chaoticQCPullbackRefineIso.{u, u} (systemInverseImageHom φ.F φ.hom)
    (systemInverseImageHom F' (Functor.whiskerRight τ A ≫ φ.hom)) τ
    (fun U' => SheafOfModules.DifferentialGradedAlgebra.InverseImageHom.sectionHom_restriction_eq_of_app
      (systemInverseImageHom φ.F φ.hom) (systemInverseImageHom F' (Functor.whiskerRight τ A ≫ φ.hom))
      U' (τ.app U') (fun n (x : ((systemComplex A).X n).val.obj (F'.op.obj U')) => rfl))

end SystemProHom

end Preorder

/-! ### Enlarging reindexings -/

/-- A lift of a linear order with finite lower sets to a higher universe has finite lower sets:
in particular `ULift.{u} ℕ`, the natural numbers in the universe of a ring `R : Type u`, is an
index site to which `SystemProHom.isEquivalence_qcPullback` applies. -/
instance _root_.ULift.instLocallyFiniteOrderBot {α : Type*} [LinearOrder α]
    [LocallyFiniteOrderBot α] : LocallyFiniteOrderBot (ULift.{u} α) :=
  LocallyFiniteOrderBot.ofIic' _ (fun a => (Finset.Iic a.down).map Equiv.ulift.symm.toEmbedding)
    fun a x => by
      simp only [Finset.mem_map, Finset.mem_Iic, Equiv.coe_toEmbedding]
      exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ hy, fun h => ⟨x.down, h, rfl⟩⟩

section Envelope

variable {ι : Type u} [LinearOrder ι] [LocallyFiniteOrderBot ι]

/-- The least monotone function above `h` on a linear order with finite lower sets:
`j ↦ max {h(i) : i ≤ j}`. -/
def monotoneEnvelope (h : ι → ι) (j : ι) : ι :=
  (Finset.Iic j).sup' ⟨j, Finset.mem_Iic.2 le_rfl⟩ h

/-- The function `h` is bounded above by its monotone envelope. -/
theorem le_monotoneEnvelope (h : ι → ι) (j : ι) : h j ≤ monotoneEnvelope h j :=
  Finset.le_sup' h (Finset.mem_Iic.2 le_rfl)

/-- The monotone envelope of `h` is monotone. -/
theorem monotone_monotoneEnvelope (h : ι → ι) : Monotone (monotoneEnvelope h) :=
  fun _ _ hij => Finset.sup'_mono h (Finset.Iic_subset_Iic.2 hij) _

end Envelope

namespace SystemProHom

variable {ι : Type u} [LinearOrder ι] [LocallyFiniteOrderBot ι]
  {A B : ιᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} R}

/-- The reindexing `i ↦ max(m(i), i)`. -/
def maxIdFunctor (F : ι ⥤ ι) : ι ⥤ ι :=
  Monotone.functor (f := fun i => max (F.obj i) i)
    fun _ _ h => max_le_max (leOfHom (F.map (homOfLE h))) h

/-- The inequality `m ≤ max(m, id)`, as a transformation of `ιᵒᵖ`. -/
def maxIdTransition (F : ι ⥤ ι) : (maxIdFunctor F).op ⟶ F.op where
  app U := (homOfLE (le_max_left (F.obj U.unop) U.unop)).op
  naturality _ _ _ := Subsingleton.elim _ _

/-- Every index is bounded above by its image under `maxIdFunctor F`. -/
theorem le_maxIdFunctor_obj (F : ι ⥤ ι) (i : ι) : i ≤ (maxIdFunctor F).obj i :=
  le_max_right _ _

/-- Two composable maps of an inverse system indexed by `ι` compose to the transition map. -/
theorem map_comp_map_eq {D : Type*} [Category D] (A : ιᵒᵖ ⥤ D) {a b c : ιᵒᵖ} (f : a ⟶ b)
    (g : b ⟶ c) (f' : a ⟶ c) : A.map f ≫ A.map g = A.map f' := by
  rw [← A.map_comp]
  exact congrArg A.map (Subsingleton.elim _ _)

section Inverse

variable (φ : SystemProHom A B) (ψ : SystemProHom B A) (h : φ.IsInverse ψ)

/-- The stage at which the composite `A_{m(n(i))} → A_i` agrees with the transition map. -/
def stage₁ (i : ι) : ι := (h.hom_inv i).choose

/-- The stage at which the composite `B_{n(m(i))} → B_i` agrees with the transition map. -/
def stage₂ (i : ι) : ι := (h.inv_hom i).choose

/-- The enlarged reindexing of the inverse: a monotone function dominating `n` and the two
families of stages. -/
def invFunctor : ι ⥤ ι :=
  Monotone.functor (monotone_monotoneEnvelope
    fun j => max (ψ.F.obj j) (max (stage₁ φ ψ h j) (stage₂ φ ψ h j)))

/-- The enlarged reindexing `invFunctor` dominates `n` and the stages `stage₁` and `stage₂`. -/
theorem le_invFunctor_obj (j : ι) :
    max (ψ.F.obj j) (max (stage₁ φ ψ h j) (stage₂ φ ψ h j)) ≤ (invFunctor φ ψ h).obj j :=
  le_monotoneEnvelope (fun j => max (ψ.F.obj j) (max (stage₁ φ ψ h j) (stage₂ φ ψ h j))) j

/-- The stage `stage₁` is bounded above by the enlarged reindexing `invFunctor`. -/
theorem stage₁_le (i : ι) : stage₁ φ ψ h i ≤ (invFunctor φ ψ h).obj i :=
  ((le_max_left _ _).trans (le_max_right _ _)).trans (le_invFunctor_obj φ ψ h i)

/-- The stage `stage₂` is bounded above by the enlarged reindexing `invFunctor`. -/
theorem stage₂_le (i : ι) : stage₂ φ ψ h i ≤ (invFunctor φ ψ h).obj i :=
  ((le_max_right _ _).trans (le_max_right _ _)).trans (le_invFunctor_obj φ ψ h i)

/-- The inequality `n ≤ n'`, as a transformation of `ιᵒᵖ`. -/
def invTransition : (invFunctor φ ψ h).op ⟶ ψ.F.op where
  app U := (homOfLE ((le_max_left _ _).trans (le_invFunctor_obj φ ψ h U.unop))).op
  naturality _ _ _ := Subsingleton.elim _ _

/-- Two composable pairs of maps of an inverse system indexed by `ι` with the same ends have the
same composite. -/
theorem map_comp_map_eq_map_comp_map {D : Type*} [Category D] (A : ιᵒᵖ ⥤ D) {a b b' c : ιᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ c) (f' : a ⟶ b') (g' : b' ⟶ c) :
    A.map f ≫ A.map g = A.map f' ≫ A.map g' := by
  rw [← A.map_comp, ← A.map_comp]
  exact congrArg A.map (Subsingleton.elim _ _)

/-- **A pro-isomorphism with on-the-nose composites** attached to two mutually inverse
representatives: the reindexing of `φ` is enlarged to `max(m, id)`, and that of `ψ` to a monotone
function dominating the stages at which the two composites agree with the transition maps. -/
def toSystemProIso : SystemProIso A B where
  F₁ := maxIdFunctor φ.F
  F₂ := invFunctor φ ψ h
  hom := (φ.refine (maxIdFunctor φ.F) (maxIdTransition φ.F)).hom
  inv := (ψ.refine (invFunctor φ ψ h) (invTransition φ ψ h)).hom
  le₁ i := (h.hom_inv i).choose_spec.choose_spec.choose.trans
    ((stage₁_le φ ψ h i).trans (le_maxIdFunctor_obj _ _))
  le₂ i := (h.inv_hom i).choose_spec.choose_spec.choose.trans
    ((stage₂_le φ ψ h i).trans
      (leOfHom ((invFunctor φ ψ h).map (homOfLE (le_maxIdFunctor_obj φ.F i)))))
  hom_inv i := by
    obtain ⟨h₁, h₂, he⟩ := (h.hom_inv i).choose_spec
    have hn := φ.hom.naturality ((invTransition φ ψ h).app (op i))
    dsimp only [Functor.comp_map, Functor.op_obj] at hn
    show A.map ((maxIdTransition φ.F).app (op ((invFunctor φ ψ h).obj i))) ≫
        φ.hom.app (op ((invFunctor φ ψ h).obj i)) ≫
          B.map ((invTransition φ ψ h).app (op i)) ≫ ψ.hom.app (op i) = _
    rw [← Category.assoc (φ.hom.app _), ← hn, Category.assoc, ← Category.assoc (A.map _),
      map_comp_map_eq_map_comp_map A _ _
        (homOfLE ((stage₁_le φ ψ h i).trans (le_maxIdFunctor_obj _ _))).op (homOfLE h₁).op,
      Category.assoc]
    exact (congrArg (A.map _ ≫ ·) he).trans (map_comp_map_eq A _ _ _)
  inv_hom i := by
    obtain ⟨h₁, h₂, he⟩ := (h.inv_hom i).choose_spec
    have hn := ψ.hom.naturality ((maxIdTransition φ.F).app (op i))
    dsimp only [Functor.comp_map, Functor.op_obj] at hn
    show B.map ((invTransition φ ψ h).app (op ((maxIdFunctor φ.F).obj i))) ≫
        ψ.hom.app (op ((maxIdFunctor φ.F).obj i)) ≫
          A.map ((maxIdTransition φ.F).app (op i)) ≫ φ.hom.app (op i) = _
    rw [← Category.assoc (ψ.hom.app _), ← hn, Category.assoc, ← Category.assoc (B.map _),
      map_comp_map_eq_map_comp_map B _ _ (homOfLE ((stage₂_le φ ψ h i).trans
        (leOfHom ((invFunctor φ ψ h).map (homOfLE (le_maxIdFunctor_obj φ.F i)))))).op
          (homOfLE h₁).op, Category.assoc]
    exact (congrArg (B.map _ ≫ ·) he).trans (map_comp_map_eq B _ _ _)

end Inverse

/-- **Stacks 0GZH.** **Let `(A_n)` and `(B_n)` be inverse systems of differential graded
`R`-algebras, and let `φ : (A_n) → (B_n)` be a morphism of pro-objects, given by a representative
`(m(·), A_{m(n)} → B_n)`. If `φ` is an isomorphism of pro-objects, then the functor
`QC(𝒜) ⥤ QC(ℬ)` it induces is an equivalence.**

Here the index category is a linearly ordered type `ι` with finite lower sets, the source's `ℕ`
being an instance, `𝒜` and `ℬ` are the sheaves of differential graded algebras on the chaotic site
`ι` with the constant sheaf of rings `R` attached to the two systems, and the functor is the
derived pullback of Tag 0GZC along the morphism of chaotic sites given by the representative,
restricted to the quasi-coherent objects of Definition 24.33.1. That `φ` is an isomorphism of
pro-objects is `IsProIso`: a representative of a morphism of pro-objects in the other direction
whose composites with `φ` agree with the transition maps after restriction to a further stage. -/
@[stacks 0GZH]
theorem isEquivalence_qcPullback (φ : SystemProHom A B) (hφ : φ.IsProIso) :
    φ.qcPullback.IsEquivalence := by
  obtain ⟨ψ, h⟩ := hφ
  haveI : (φ.refine (maxIdFunctor φ.F) (maxIdTransition φ.F)).qcPullback.IsEquivalence :=
    (toSystemProIso φ ψ h).qcEquivalence.isEquivalence_functor
  exact Functor.isEquivalence_of_iso (φ.refineQCPullbackIso (maxIdFunctor φ.F) (maxIdTransition φ.F))

end SystemProHom

end DifferentialGradedAlgebra
