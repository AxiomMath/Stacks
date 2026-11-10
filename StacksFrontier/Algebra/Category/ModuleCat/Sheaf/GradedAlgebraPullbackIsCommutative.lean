module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationModule
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Transport

/-!
# Commutativity in every pair of degrees is inherited by a pullback

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and let `B` be a sheaf
of graded `O_D`-algebras which is commutative in *every* pair of degrees, that is
`SheafOfModules.GradedAlgebra.IsCommutative`. Then so is the pullback `f^*B`.

This is the hypothesis Situation 0849 asks of a sheaf of graded algebras: not commutation of two
degree-one generators but `HEq ((B.mul i j).app U a b) ((B.mul j i).app U b a)` for all `i j : ℤ`,
heterogeneous because the two sides are sections of the pieces of degrees `i + j` and `j + i`,
which are propositionally but not definitionally equal.

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullbackCommutative` proves the
degree-`(1,1)` statement from the degree-`(1,1)` hypothesis, which is what the universal property
of the symmetric algebra constrains; that is a different implication, not a special case of this
one, because its hypothesis is weaker. Neither file subsumes the other.

The pullback is the inverse image followed by extension of scalars, and extension of scalars is
the sectionwise tensor product followed by sheafification, so commutativity has to be carried
through three constructions, in each case by the argument already used there for associativity
and the unit laws — the laws of a graded algebra are heterogeneous equalities too, so the
plumbing for an equality across two propositionally equal degrees is in place in all three
places.

* **Inverse image.** Every operation of the inverse image is the image, under a
  finite-product-preserving functor to types, of a morphism of sheaves of sets on the target
  site. Commutativity becomes a *heterogeneous* equality of two such morphisms, which
  `Stacks.Sheaves.GradedAlgebraInverseImage.heq_sheafHom_of_sections` reduces to sections over
  the target site and `heq_map_of_heq_hom` carries along the functor.
* **Sectionwise tensor product.** The sections are a tensor product, so this is two applications
  of `TensorProduct.inductionOn` reduced to pure tensors, where the formula
  `(a ⊗ x)(c ⊗ y) = ac ⊗ xy` is symmetric because the ring of sections is commutative. The
  heterogeneous equality is transported through a sum and a pure tensor by
  `Stacks.Sheaves.GradedAlgebraExtendScalars.heq_cof_add` and `heq_cof_tmul`.
* **Sheafification.** `Stacks.GradedAlgebra.heq_sheafify_mul_comm` already transfers
  commutativity in every pair of degrees along the sheafification units. Nothing new is needed.

## Main results

* `Stacks.Sheaves.GradedAlgebraExtendScalars.heq_cofApp_comm` and
  `isCommutative_changeOfRingsGradedAlgebra`: base change of a commutative graded algebra of
  presheaves of modules is commutative.
* `Stacks.Sheaves.GradedAlgebraInverseImage.heq_mulSheafHom_comm`,
  `heq_transportMulApp_comm`, `isCommutative_transportGradedAlgebra` and
  `isCommutative_inverseImageGradedAlgebra`: the same for a transport along a
  finite-product-preserving functor of sheaves of sets, and in particular for the inverse image
  along a morphism of topoi.
* `Stacks.Sheaves.GradedAlgebraExtendScalars.isCommutative_extendScalarsGradedAlgebra` and
  `Stacks.Sheaves.GradedAlgebraPullback.isCommutative_toposPullbackGradedAlgebra`: the statements
  for extension of scalars and for the pullback itself.

## Implementation notes

Each step is a named top-level lemma with an explicit type signature, and every equality of
degrees is carried as a hypothesis of a helper which substitutes it internally rather than
rewritten under an `eqToHom`: the heterogeneous equalities are not manipulable by `rw` where the
degrees are not local variables.

`SheafOfModules.GradedAlgebra.IsCommutative` welds the ring universe to the module-sections
universe, because `SheafOfModules.GradedAlgebra.{w, w}` is the form it is stated at and the form
the pullback is stated at. The two heterogeneous-equality lemmas below, which are where the work
is, do not: `heq_cofApp_comm` is at the presheaf level, where the universes are already split,
and `heq_mulSheafHom_comm` and `heq_transportMulApp_comm` keep the two site universes of the
transport apart.

No `@[stacks]` tag is claimed. Tag 0FQW is the definition of a sheaf of graded algebras and
Tag 0FQX its pullback; a property of one construction of them is neither.

## References

* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry TensorProduct PresheafOfModules
open Stacks.PresheafOfModules.ChangeOfRings
open Stacks.Sheaves.BilinearChangeOfRings
open Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.ToposPullback
open Stacks.Sheaves.GradedAlgebraInverseImage

/-! ### Base change of the multiplication of a graded algebra -/

namespace Stacks.Sheaves.GradedAlgebraExtendScalars

universe v u w

variable {C : Type u} [Category.{v} C] {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : O₁ ⟶ O₂)
  {P : ℤ → PMod O₁}

/-- **Base change of a commutative multiplication is commutative, in every pair of degrees.**
On pure tensors the base change is `(a ⊗ m, c ⊗ n) ↦ ac ⊗ (m · n)`, which is symmetric because
the ring of sections is commutative; the general case is two inductions on the tensor product,
with the equality of degrees `i + j = j + i` carried through the sum and the pure tensor by
`heq_cof_add` and `heq_cof_tmul`. -/
public lemma heq_cofApp_comm (A : Stacks.GradedAlgebra P) (i j : ℤ)
    (hc : ∀ (X : Cᵒᵖ) (m : (P i).obj X) (n : (P j).obj X),
      HEq ((A.mul i j).app X m n) ((A.mul j i).app X n m))
    (X : Cᵒᵖ) (x : cofObj θ (P i) X) (y : cofObj θ (P j) X) :
    HEq (cofApp θ (A.mul i j) X x y) (cofApp θ (A.mul j i) X y x) := by
  let := (θ.app X).hom.toAlgebra
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ =>
    exact (heq_of_eq (cofApp_add_left θ (A.mul i j) X x₁ x₂ y)).trans
      ((heq_cof_add θ (Q := P) (add_comm i j) h₁ h₂).trans
        (heq_of_eq (cofApp_add_right θ (A.mul j i) X y x₁ x₂)).symm)
  | tmul a m =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ =>
      exact (heq_of_eq (cofApp_add_right θ (A.mul i j) X _ y₁ y₂)).trans
        ((heq_cof_add θ (Q := P) (add_comm i j) h₁ h₂).trans
          (heq_of_eq (cofApp_add_left θ (A.mul j i) X y₁ y₂ _)).symm)
    | tmul c n =>
      refine (heq_of_eq (cofApp_tmul θ (A.mul i j) X a c m n)).trans
        (((?_ : HEq _ _)).trans (heq_of_eq (cofApp_tmul θ (A.mul j i) X c a n m)).symm)
      rw [mul_comm a c]
      exact heq_cof_tmul θ (Q := P) (add_comm i j) (c * a) (hc X m n)

/-- **Base change of a commutative graded algebra of presheaves of modules is commutative.** -/
public theorem isCommutative_changeOfRingsGradedAlgebra (A : Stacks.GradedAlgebra P)
    [hA : A.IsCommutative] : (changeOfRingsGradedAlgebra θ A).IsCommutative :=
  ⟨fun i j X x y => heq_cofApp_comm θ A i j
    (fun X' m n => Stacks.GradedAlgebra.IsCommutative.mul_comm i j X' m n) X x y⟩

end Stacks.Sheaves.GradedAlgebraExtendScalars

/-! ### Transport along a functor of sheaves of sets, and the inverse image -/

namespace Stacks.Sheaves.GradedAlgebraInverseImage

universe t w w' v u v' u'

/-- Precomposing with the braiding `prod.lift prod.snd prod.fst` of the binary product swaps the
two entries of a pair, after applying a finite-product-preserving functor to types. -/
private theorem map_swap_comp_apply {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
    {P : Sheaf K (Type w') ⥤ Type t} [PreservesFiniteProducts P] {A B Z : Sheaf K (Type w')}
    (g : B ⨯ A ⟶ Z) (x : P.obj A) (y : P.obj B) :
    P.map (prod.lift prod.snd prod.fst ≫ g) (Functor.prodObjMk x y) =
      P.map g (Functor.prodObjMk y x) := by
  rw [Functor.map_comp_apply, Functor.map_lift_apply, Functor.map_fst_prodObjMk,
    Functor.map_snd_prodObjMk]

section Operations

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget RingCat.{w'})] [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  {O : Sheaf K RingCat.{w'}} (A : SheafOfModules.GradedAlgebra.{w', w'} O)

omit [K.HasSheafCompose (forget RingCat.{w'})] in
/-- **A commutative multiplication is a symmetric morphism of sheaves of sets, in every pair of
degrees.** Precomposing `Stacks.Sheaves.GradedAlgebraInverseImage.mulSheafHom` in degrees
`(j, i)` with the braiding of the binary product gives `mulSheafHom` in degrees `(i, j)` — not
on the nose, because the two have targets `pieceSheaf A (j + i)` and `pieceSheaf A (i + j)`, but
heterogeneously. This is the form in which commutativity survives a transport: both sides are
morphisms of sheaves of sets on the target site. -/
public lemma heq_mulSheafHom_comm (i j : ℤ)
    (hc : ∀ (X : Dᵒᵖ) (x : (A.piece i).val.obj X) (y : (A.piece j).val.obj X),
      HEq ((A.mul i j).app X x y) ((A.mul j i).app X y x)) :
    HEq (mulSheafHom A i j)
      ((prod.lift prod.snd prod.fst :
            pieceSheaf A i ⨯ pieceSheaf A j ⟶ pieceSheaf A j ⨯ pieceSheaf A i) ≫
        mulSheafHom A j i) := by
  refine heq_sheafHom_of_sections (congrArg (pieceSheaf A) (add_comm i j)) _ _ fun V s => ?_
  obtain ⟨x, y, rfl⟩ : ∃ x y, s = Functor.prodObjMk x y :=
    ⟨_, _, (Functor.prodObjMk_map_fst_map_snd s).symm⟩
  rw [sections_mulSheafHom, map_swap_comp_apply, sections_mulSheafHom]
  exact hc V x y

end Operations

section Transport

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (Φ : Sheaf K (Type w') ⥤ Sheaf J (Type w)) [PreservesFiniteProducts Φ]
  {O : Sheaf K RingCat.{w'}} (A : SheafOfModules.GradedAlgebra.{w', w'} O)

omit [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **A transport inherits commutativity of the multiplication, in every pair of degrees.** The
transported multiplication is the image of
`Stacks.Sheaves.GradedAlgebraInverseImage.mulSheafHom` under a finite-product-preserving functor
to types, so the heterogeneous symmetry of that morphism of sheaves of sets is carried along by
`heq_map_of_heq_hom`. -/
public theorem heq_transportMulApp_comm (i j : ℤ)
    (hc : ∀ (X : Dᵒᵖ) (x : (A.piece i).val.obj X) (y : (A.piece j).val.obj X),
      HEq ((A.mul i j).app X x y) ((A.mul j i).app X y x))
    (X : Cᵒᵖ) (x : (transportSections J Φ X).obj (pieceSheaf A i))
    (y : (transportSections J Φ X).obj (pieceSheaf A j)) :
    HEq (transportMulApp J Φ A i j X x y) (transportMulApp J Φ A j i X y x) := by
  have key := heq_map_of_heq_hom (congrArg (pieceSheaf A) (add_comm i j))
    (heq_mulSheafHom_comm A i j hc) (transportSections J Φ X) (Functor.prodObjMk x y)
  exact key.trans (heq_of_eq ((map_swap_comp_apply _ _ _).trans rfl))

/-- **A transported sheaf of graded algebras inherits commutativity in every pair of
degrees.** -/
public theorem isCommutative_transportGradedAlgebra [hA : A.IsCommutative] :
    (transportGradedAlgebra J Φ A).IsCommutative :=
  ⟨fun i j X x y => heq_transportMulApp_comm J Φ A i j
    (fun X' u v => Stacks.GradedAlgebra.IsCommutative.mul_comm
      (A := A.toPresheafGradedAlgebra) i j X' u v) X x y⟩

end Transport

section InverseImage

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (O : Sheaf K RingCat.{w'}) (A : SheafOfModules.GradedAlgebra.{w', w'} O)

/-- **The inverse image of a sheaf of graded algebras inherits commutativity in every pair of
degrees.** -/
public theorem isCommutative_inverseImageGradedAlgebra [hA : A.IsCommutative] :
    (inverseImageGradedAlgebra f O A).IsCommutative := by
  have : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits
  exact isCommutative_transportGradedAlgebra J f.inverseImage A

end InverseImage

end Stacks.Sheaves.GradedAlgebraInverseImage

/-! ### Extension of scalars -/

namespace Stacks.Sheaves.GradedAlgebraExtendScalars

universe v u w

variable {C : Type u} [Category.{v} C] {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : O₁ ⟶ O₂)
  (J : GrothendieckTopology C)
  (h₁ : Presheaf.IsSheaf J (ringPresheaf O₁)) (h₂ : Presheaf.IsSheaf J (ringPresheaf O₂))
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Extension of scalars inherits commutativity in every pair of degrees.** At the presheaf
level the multiplication is the base change `(a ⊗ x)(c ⊗ y) = ac ⊗ xy`, which is symmetric by
`heq_cofApp_comm`; `Stacks.GradedAlgebra.heq_sheafify_mul_comm` carries that through the
sheafification. -/
public theorem isCommutative_extendScalarsGradedAlgebra
    (B : SheafOfModules.GradedAlgebra.{w, w} (commRingSheaf J O₁ h₁)) [hB : B.IsCommutative] :
    (extendScalarsGradedAlgebra θ J h₁ h₂ B).IsCommutative :=
  ⟨fun i j U x y => Stacks.GradedAlgebra.heq_sheafify_mul_comm
    (𝟙 (commRingSheaf J O₂ h₂).obj)
    (changeOfRingsGradedAlgebra θ (forgetSheaf J h₁ B))
    (fun i' j' X m n => heq_cofApp_comm θ (forgetSheaf J h₁ B) i' j'
      (fun X' u v => Stacks.GradedAlgebra.IsCommutative.mul_comm
        (A := B.toPresheafGradedAlgebra) i' j' X' u v) X m n)
    i j U.unop x y⟩

end Stacks.Sheaves.GradedAlgebraExtendScalars

/-! ### The pullback along a morphism of ringed topoi -/

namespace Stacks.Sheaves.GradedAlgebraPullback

universe w v u

variable {X Y : RingedTopos.{v, u, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y)

/-- **The pullback of a sheaf of graded algebras inherits commutativity in every pair of
degrees.** The pullback is the inverse image followed by extension of scalars, and both steps
preserve commutativity.

This is the hypothesis Situation 0849 asks of a sheaf of graded algebras, so a pullback of a
commutative sheaf of graded algebras is again an admissible input to the relative Proj
construction. -/
public theorem isCommutative_toposPullbackGradedAlgebra
    (B : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    [hB : B.IsCommutative] :
    (toposPullbackGradedAlgebra f B).IsCommutative :=
  Stacks.Sheaves.GradedAlgebraExtendScalars.isCommutative_extendScalarsGradedAlgebra
    (fSharpCommRing f) X.J _ _
    (inverseImageGradedAlgebra f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B)
    (hB := isCommutative_inverseImageGradedAlgebra f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B)

end Stacks.Sheaves.GradedAlgebraPullback

end
