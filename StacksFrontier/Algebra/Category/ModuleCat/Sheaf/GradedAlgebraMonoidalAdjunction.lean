module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraFunctoriality
public import StacksCore.Tactic.StacksAttribute

/-!
# Sheaves of graded algebras and a monoidal adjunction

Let `L ⊣ G` be an adjunction between categories of sheaves of modules, with `L` strong monoidal
for the tensor product of Tag 01CA and `G` lax monoidal compatibly with the adjunction (which
is automatic: `CategoryTheory.Adjunction.rightAdjointLaxMonoidal` produces exactly such a
structure on the right adjoint). Then the two transports of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraFunctoriality` are themselves
adjoint: **homomorphisms of sheaves of graded algebras `L(B) ⟶ A` correspond bijectively, and
naturally in both arguments, to homomorphisms `B ⟶ G(A)`.**

This is part (3) of the functoriality of sheaves of graded algebras for a morphism of ringed
topoi, in the generality in which its proof actually runs. The Stacks remark says part (3)
"follows immediately from the usual adjunction between `f^*` and `f_*` on sheaves of modules";
what makes that immediate is precisely that the adjunction is monoidal, and the two
compatibilities `CategoryTheory.Adjunction.unit_app_tensor_comp_map_δ` and
`CategoryTheory.Functor.LaxMonoidal.μ_natural` are the only facts about it that are used.

## Main definitions

* `Stacks.MonoidalGraded.mapMul_comp_iff`: for a monoidal adjunction, a square expressing
  multiplicativity over `L` transposes to a square expressing multiplicativity over `G`. This
  is pure category theory and is where the monoidality of the adjunction is consumed.
* `SheafOfModules.GradedAlgebra.transportHomEquiv`: **the bijection
  `(L(B) ⟶ A) ≃ (B ⟶ G(A))` between homomorphisms of sheaves of graded algebras.**
* `SheafOfModules.GradedAlgebra.transportAdjunction`: the same bijection as an adjunction
  between the two induced functors on categories of sheaves of graded algebras.

## Implementation notes

**Why the transposition lemma is stated for an arbitrary monoidal adjunction.** The degreewise
bijection is the module-level `CategoryTheory.Adjunction.homEquiv`; the only content is that it
matches multiplicativity on the two sides, and that is a diagram chase in an arbitrary monoidal
category. Keeping it in `Stacks.MonoidalGraded` beside the transport lemmas means the sheaf
layer of this file consists only of `mulSheaf_comp_eq_iff` and `mulSheaf_transport`, both from
the imported file, and no tensor-product spelling hazard arises here at all.

**Strong monoidality of the left adjoint is used, and only through `μ_δ` and `δ_μ`.** The
transposed square is `L.map m ≫ c = δ L X Y ≫ (a ⊗ₘ b) ≫ m'`, and passing between that and the
form `mapMul L m ≫ c = (a ⊗ₘ b) ≫ m'` is composition with the two halves of the tensorator
being inverse. For a merely lax monoidal `L` the two statements are not equivalent, so this
hypothesis is not removable.

**The unit is not part of a homomorphism.** `SheafOfModules.GradedAlgebra.Hom` does not require
preservation of the distinguished degree-zero unit, matching the source, so no transposition
statement about `Stacks.MonoidalGraded.mapOne` is needed. The unital homomorphisms are
`SheafOfModules.GradedAlgebra.UnitalHom`, and the bijection here does not claim to restrict to
them.

## References

* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX) — functoriality of
  sheaves of graded algebras for a morphism of ringed topoi; part (3) is the correspondence
  between homomorphisms out of a pullback and homomorphisms into a pushforward.
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW) — sheaves of graded
  algebras and their homomorphisms.
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7) — the adjunction
  between pullback and pushforward of sheaves of modules.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf PresheafOfModules

universe v₁ v₂ u₁ u₂ w

namespace Stacks.MonoidalGraded

/-! ### Transposing a multiplicativity square along a monoidal adjunction -/

section Transpose

variable {E : Type u₁} [Category.{v₁} E] [MonoidalCategory E]
  {E' : Type u₂} [Category.{v₂} E'] [MonoidalCategory E']
  {L : E' ⥤ E} {G : E ⥤ E'} (adj : L ⊣ G)
  [L.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal]

/-- **A square expressing multiplicativity over the left adjoint transposes to one expressing
multiplicativity over the right adjoint.** The two multiplications `m` and `m'` and the triple
`a`, `b`, `c` are arbitrary, so the degree bookkeeping of a graded algebra never enters. -/
theorem mapMul_comp_iff {X Y Z : E'} {X' Y' Z' : E} (m : X ⊗ Y ⟶ Z) (m' : X' ⊗ Y' ⟶ Z')
    (a : L.obj X ⟶ X') (b : L.obj Y ⟶ Y') (c : L.obj Z ⟶ Z') :
    mapMul L m ≫ c = (a ⊗ₘ b) ≫ m' ↔
      m ≫ adj.homEquiv Z Z' c =
        (adj.homEquiv X X' a ⊗ₘ adj.homEquiv Y Y' b) ≫ mapMul G m' := by
  have key : (adj.homEquiv X X' a ⊗ₘ adj.homEquiv Y Y' b) ≫ mapMul G m' =
      adj.homEquiv (X ⊗ Y) Z'
        (Functor.OplaxMonoidal.δ L X Y ≫ (a ⊗ₘ b) ≫ m') := by
    simp only [Adjunction.homEquiv_unit, mapMul, Functor.map_comp,
      ← MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      Functor.LaxMonoidal.μ_natural_assoc, Adjunction.unit_app_tensor_comp_map_δ_assoc]
  have step : mapMul L m ≫ c = (a ⊗ₘ b) ≫ m' ↔
      L.map m ≫ c = Functor.OplaxMonoidal.δ L X Y ≫ (a ⊗ₘ b) ≫ m' :=
    ⟨fun h ↦ by simp only [← h, mapMul, Category.assoc, Functor.Monoidal.δ_μ_assoc],
      fun h ↦ by simp only [mapMul, Category.assoc, h, Functor.Monoidal.μ_δ_assoc]⟩
  rw [step, key, ← adj.homEquiv_naturality_left]
  exact ((adj.homEquiv (X ⊗ Y) Z').apply_eq_iff_eq).symm

end Transpose

end Stacks.MonoidalGraded

namespace SheafOfModules.GradedAlgebra

/-! ### The correspondence of homomorphisms of sheaves of graded algebras -/

section Adjunction

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Psharp : Sheaf K CommRingCat.{w}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable {L : SheafOfModules.{w} (toRingCat K Psharp) ⥤ SheafOfModules.{w} (toRingCat J Osharp)}
  {G : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp)}
  (adj : L ⊣ G) [L.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal]
  (hO : Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))
  (hP : Presheaf.IsSheaf K
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Psharp.obj))

include hO hP

variable {A : GradedAlgebra.{w, w} (toRingCat J Osharp)}
  {B : GradedAlgebra.{w, w} (toRingCat K Psharp)}

/-- **The adjoint transpose of a homomorphism of sheaves of graded algebras `L(B) ⟶ A`**: a
homomorphism `B ⟶ G(A)`, given degreewise by the hom-set bijection of the adjunction on sheaves
of modules. -/
noncomputable def transportHomForward (φ : transport L B hP hO ⟶ A) :
    B ⟶ transport G A hO hP where
  app n := adj.homEquiv (B.piece n) (A.piece n) (φ.app n)
  map_mul i j := by
    refine (mulSheaf_comp_eq_iff hP B (transport G A hO hP)
      (fun n ↦ adj.homEquiv (B.piece n) (A.piece n) (φ.app n)) i j).mp ?_
    simp only [mulSheaf_transport]
    refine (Stacks.MonoidalGraded.mapMul_comp_iff adj (mulSheaf B i j) (mulSheaf A i j)
      (φ.app i) (φ.app j) (φ.app (i + j))).mp ?_
    have h := (mulSheaf_comp_eq_iff hO (transport L B hP hO) A φ.app i j).mpr (φ.map_mul i j)
    rwa [mulSheaf_transport] at h

/-- The degree-`n` component of `transportHomForward adj hO hP φ` is the adjoint transpose of
the degree-`n` component of `φ`. -/
@[simp]
theorem transportHomForward_app (φ : transport L B hP hO ⟶ A) (n : ℤ) :
    (transportHomForward adj hO hP φ).app n = adj.homEquiv (B.piece n) (A.piece n) (φ.app n) :=
  rfl

/-- **The adjoint transpose of a homomorphism of sheaves of graded algebras `B ⟶ G(A)`**: a
homomorphism `L(B) ⟶ A`, given degreewise by the inverse hom-set bijection. -/
noncomputable def transportHomBackward (ψ : B ⟶ transport G A hO hP) :
    transport L B hP hO ⟶ A where
  app n := (adj.homEquiv (B.piece n) (A.piece n)).symm (ψ.app n)
  map_mul i j := by
    refine (mulSheaf_comp_eq_iff hO (transport L B hP hO) A
      (fun n ↦ (adj.homEquiv (B.piece n) (A.piece n)).symm (ψ.app n)) i j).mp ?_
    simp only [mulSheaf_transport]
    refine (Stacks.MonoidalGraded.mapMul_comp_iff adj (mulSheaf B i j) (mulSheaf A i j)
      ((adj.homEquiv (B.piece i) (A.piece i)).symm (ψ.app i))
      ((adj.homEquiv (B.piece j) (A.piece j)).symm (ψ.app j))
      ((adj.homEquiv (B.piece (i + j)) (A.piece (i + j))).symm (ψ.app (i + j)))).mpr ?_
    have cancel : ∀ n : ℤ, adj.homEquiv (B.piece n) (A.piece n)
        ((adj.homEquiv (B.piece n) (A.piece n)).symm (ψ.app n)) = ψ.app n :=
      fun n ↦ (adj.homEquiv (B.piece n) (A.piece n)).apply_symm_apply (ψ.app n)
    simp only [cancel]
    have h := (mulSheaf_comp_eq_iff hP B (transport G A hO hP) ψ.app i j).mpr (ψ.map_mul i j)
    rwa [mulSheaf_transport] at h

/-- The degree-`n` component of `transportHomBackward adj hO hP ψ` is the inverse adjoint
transpose of the degree-`n` component of `ψ`. -/
@[simp]
theorem transportHomBackward_app (ψ : B ⟶ transport G A hO hP) (n : ℤ) :
    (transportHomBackward adj hO hP ψ).app n =
      (adj.homEquiv (B.piece n) (A.piece n)).symm (ψ.app n) :=
  rfl

/-- **Homomorphisms of sheaves of graded algebras out of `L(B)` correspond bijectively to
homomorphisms into `G(A)`.** Degreewise the bijection is the hom-set bijection of the
adjunction on sheaves of modules. -/
noncomputable def transportHomEquiv (A : GradedAlgebra.{w, w} (toRingCat J Osharp))
    (B : GradedAlgebra.{w, w} (toRingCat K Psharp)) :
    (transport L B hP hO ⟶ A) ≃ (B ⟶ transport G A hO hP) where
  toFun := transportHomForward adj hO hP
  invFun := transportHomBackward adj hO hP
  left_inv φ := Hom.ext fun n ↦ by
    simp only [transportHomBackward_app, transportHomForward_app]
    exact (adj.homEquiv (B.piece n) (A.piece n)).symm_apply_apply (φ.app n)
  right_inv ψ := Hom.ext fun n ↦ by
    simp only [transportHomForward_app, transportHomBackward_app]
    exact (adj.homEquiv (B.piece n) (A.piece n)).apply_symm_apply (ψ.app n)

/-- The bijection `transportHomEquiv` sends `φ` to `transportHomForward adj hO hP φ`. -/
@[simp]
theorem transportHomEquiv_apply (φ : transport L B hP hO ⟶ A) :
    transportHomEquiv adj hO hP A B φ = transportHomForward adj hO hP φ :=
  rfl

/-- The inverse of `transportHomEquiv` sends `ψ` to `transportHomBackward adj hO hP ψ`. -/
@[simp]
theorem transportHomEquiv_symm_apply (ψ : B ⟶ transport G A hO hP) :
    (transportHomEquiv adj hO hP A B).symm ψ = transportHomBackward adj hO hP ψ :=
  rfl

/-- **The transport of sheaves of graded algebras along the left adjoint of a monoidal
adjunction is left adjoint to the transport along the right adjoint.** For a morphism of ringed
topoi this is part (3) of the functoriality of sheaves of graded algebras: the pullback of
graded algebras is left adjoint to the pushforward, so homomorphisms `f^*B ⟶ A` correspond to
homomorphisms `B ⟶ f_*A`, naturally in both arguments. -/
@[stacks 0FQX "part (3): adjunction for graded algebras"]
noncomputable def transportAdjunction :
    transportFunctor L hP hO ⊣ transportFunctor G hO hP :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun B A ↦ transportHomEquiv adj hO hP A B
      homEquiv_naturality_left_symm := fun β ψ ↦ Hom.ext fun n ↦ by
        simp only [categoryStruct_comp_app, transportFunctor_map_app]
        exact adj.homEquiv_naturality_left_symm (β.app n) (ψ.app n)
      homEquiv_naturality_right := fun φ α ↦ Hom.ext fun n ↦ by
        simp only [categoryStruct_comp_app, transportFunctor_map_app]
        exact adj.homEquiv_naturality_right (φ.app n) (α.app n) }

/-- The hom-set bijection of `transportAdjunction` is the degreewise adjoint transpose. -/
theorem transportAdjunction_homEquiv :
    (transportAdjunction adj hO hP).homEquiv =
      fun B A ↦ transportHomEquiv adj hO hP A B :=
  Adjunction.mkOfHomEquiv_homEquiv _

end Adjunction

end SheafOfModules.GradedAlgebra

end
