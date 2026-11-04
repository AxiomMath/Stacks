module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackGradedAlgebra
public import StacksCore.Tactic.StacksAttribute

/-!
# Transport of a sheaf of graded algebras along a lax monoidal functor

Let `R` be a sheaf of rings on a site `C` and `S` a sheaf of rings on a site `D`, and let
`F : SheafOfModules R ⥤ SheafOfModules S` be a lax monoidal functor for the tensor product of
sheaves of modules of Tag 01CA. Then `F` carries a sheaf of graded `R`-algebras to a sheaf of
graded `S`-algebras: the homogeneous pieces are the images `F(A_n)`, and the multiplication is
the multiplication of `A` conjugated by the tensorator of `F`. This is functorial in the
algebra.

The construction is behind both halves of the functoriality of sheaves of graded algebras for a
morphism of ringed topoi: the pullback of a sheaf of graded algebras is the transport along the
pullback of sheaves of modules, which is strong monoidal, and the pushforward is the transport
along the pushforward, which is lax monoidal because it is right adjoint to the pullback.

The two levels at which the algebra axioms live are already reconciled upstream: a lax monoidal
functor transports morphism-level identities (`Stacks.MonoidalGraded.mapMul_assoc` and its unit
counterparts) and `SheafOfModules.GradedAlgebra.ofMorphismData` descends morphism-level data to
the sectionwise `HEq` fields of a sheaf of graded algebras. What this file adds is, first, the
two lemmas saying that `ofMorphismData` is a section of that correspondence
(`mulSheaf_ofMorphismData`, `oneHom_ofMorphismData`), and second the **morphism-level reading
of a homomorphism of sheaves of graded algebras**, `mulSheaf_comp_eq_iff`. Without the latter
the transport would be functorial only on objects: `SheafOfModules.GradedAlgebra.Hom` states
multiplicativity at arbitrary local sections, whereas a monoidal functor transports equalities
of morphisms.

## Main definitions

* `SheafOfModules.GradedAlgebra.transportedMul` and `transportedOne`: the multiplication
  `F(A_i) ⊗ F(A_j) ⟶ F(A_{i+j})` and the unit `𝟙_ ⟶ F(A_0)` conjugated by the lax monoidal
  structure of `F`.
* `SheafOfModules.GradedAlgebra.transport`: **the sheaf of graded `S`-algebras `F(A)`.**
* `SheafOfModules.GradedAlgebra.transportHom` and
  `SheafOfModules.GradedAlgebra.transportFunctor`: the image of a homomorphism of sheaves of
  graded algebras and the resulting functor `GradedAlgebra R ⥤ GradedAlgebra S`.

## Main results

* `Stacks.MonoidalGraded.mapMul_naturality`: a lax monoidal functor transports a morphism-level
  multiplicativity square.
* `Stacks.TensorSheafWorld.tensorHom_val_app_tensorSheafUnit`: the tensor product of two
  morphisms of sheaves of modules, on a local pure tensor.
* `SheafOfModules.GradedAlgebra.mulSheaf_ofMorphismData` and `oneHom_ofMorphismData`: the
  morphism-level multiplication and unit of `ofMorphismData` are the given ones.
* `SheafOfModules.GradedAlgebra.mulSheaf_comp_eq_iff`: **a degreewise family of morphisms of
  sheaves of modules preserves products of homogeneous local sections if and only if it
  commutes with the morphism-level multiplications.** This is the morphism-level reading of
  `SheafOfModules.GradedAlgebra.Hom`.
* `SheafOfModules.GradedAlgebra.transportedMul_assoc`, `transportedOne_mul` and
  `transportedMul_one`: the transported multiplication is associative and unital, as equalities
  of morphisms.
* `SheafOfModules.GradedAlgebra.mulSheaf_transport` and `oneHom_transport`: the morphism-level
  multiplication and unit of `F(A)` are the transported ones, so a consumer never unfolds
  `transport`.

## Implementation notes

**Why the morphism-level reading of `Hom` is an iff and not two lemmas.** Both directions are
used: the forward one to produce the homomorphism `F(A) ⟶ F(B)`, the backward one to read off
the hypothesis attached to a given homomorphism. Each is one evaluation of
`PresheafOfModules.tensorSheaf_hom_ext` against the pure-tensor formulas of Tag 01CA, so
stating them together costs nothing and keeps the two uses symmetric.

**No `rw` crosses the tensor-product boundary.** `(M ⊗ N).val.obj U` and
`(((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj M).obj N).val.obj U` are definitionally
equal and
not syntactically so, so every step of the section-level lemmas is `Eq.trans`, `congrArg` or
`exact`, and the extensionality principle is applied with its sheaf arguments passed
explicitly. This is the discipline of the imported files, recorded in their implementation
notes.

**Why `transport` never has to be unfolded.** `mulSheaf_transport` and `oneHom_transport`
identify the morphism-level data of `F(A)` with `transportedMul` and `transportedOne`, so the
functoriality statements are proved against `Stacks.MonoidalGraded` and never against
`ofMorphismData`. The one place the two spellings meet is `simp only [mulSheaf_transport]`
inside `transportHom`, which matches up to reducible transparency and so does not have to see
through the tensor product.

**Universes.** The two sites are independent (`C : Type u₁` with `Category.{v₁} C` and
`D : Type u₂` with `Category.{v₂} D`), but the ring sheaves and the modules on both sides live
in one universe `w`. That constraint is inherited, not imposed here: Mathlib's monoidal
structure on presheaves of modules, and hence everything about the associator of Tag 01CA,
exists only in that form, and `SheafOfModules.GradedAlgebra.ofMorphismData` consumes it.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW) — sheaves of graded
  algebras and their homomorphisms.
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX) — functoriality of
  sheaves of graded algebras for a morphism of ringed topoi.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf PresheafOfModules

open scoped TensorProduct

universe v₁ v₂ u₁ u₂ w

namespace Stacks.MonoidalGraded

/-! ### A lax monoidal functor transports a multiplicativity square -/

section Naturality

variable {E : Type u₁} [Category.{v₁} E] [MonoidalCategory E]
  {E' : Type u₂} [Category.{v₂} E'] [MonoidalCategory E'] (F : E ⥤ E') [F.LaxMonoidal]

/-- **A lax monoidal functor transports morphism-level multiplicativity.** A triple of
morphisms `a`, `b`, `c` intertwining two multiplications `m` and `m'` is carried to a triple
intertwining their transports. Together with `Stacks.MonoidalGraded.mapMul_assoc` and the two
unit laws this is everything a graded-algebra transport needs. -/
theorem mapMul_naturality {X Y Z X' Y' Z' : E} (m : X ⊗ Y ⟶ Z) (m' : X' ⊗ Y' ⟶ Z')
    (a : X ⟶ X') (b : Y ⟶ Y') (c : Z ⟶ Z') (h : m ≫ c = (a ⊗ₘ b) ≫ m') :
    mapMul F m ≫ F.map c = (F.map a ⊗ₘ F.map b) ≫ mapMul F m' := by
  have h' : F.map m ≫ F.map c = F.map (a ⊗ₘ b) ≫ F.map m' := by
    rw [← Functor.map_comp, ← Functor.map_comp, h]
  simp only [mapMul, Category.assoc, h', Functor.LaxMonoidal.μ_natural_assoc]

end Naturality

end Stacks.MonoidalGraded

namespace Stacks.TensorSheafWorld

/-! ### The tensor product of two morphisms on local pure tensors -/

section TensorHom

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (Osharp : Sheaf J CommRingCat.{w})
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] monoidalCategory

variable (hO : Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj)) (V : Cᵒᵖ)

include hO

/-- **The tensor product of two morphisms of sheaves of modules on a local pure tensor**, in
the tensor-bifunctor spelling. This is the two whiskering formulas of Tag 01CA composed along
`CategoryTheory.MonoidalCategory.tensorHom_def`. -/
theorem tensorHom_val_app_tensorSheafUnit
    {M M' N N' : SheafOfModules.{w} (toRingCat J Osharp)} (f : M ⟶ M') (g : N ⟶ N')
    (m : M.val.obj V) (n : N.val.obj V) :
    (f ⊗ₘ g).val.app V ((tensorSheafUnit M N).app V (m ⊗ₜ n)) =
      (tensorSheafUnit M' N').app V (f.val.app V m ⊗ₜ g.val.app V n) :=
  (congrArg (fun φ : M ⊗ N ⟶ M' ⊗ N' ↦
        φ.val.app V ((tensorSheafUnit M N).app V (m ⊗ₜ n))) (tensorHom_def f g)).trans
    ((congrArg ((M' ◁ g).val.app V)
        (whiskerRight_val_app_tensorSheafUnit Osharp hO V f N m n)).trans
      (whiskerLeft_val_app_tensorSheafUnit Osharp hO V M' g (f.val.app V m) n))

end TensorHom

end Stacks.TensorSheafWorld

namespace SheafOfModules.GradedAlgebra

/-! ### `ofMorphismData` is a section of the morphism-level reading -/

section OfMorphismData

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (hO : Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))
  (piece : ℤ → SheafOfModules.{w} (toRingCat J Osharp))
  (mul : ∀ i j : ℤ, piece i ⊗ piece j ⟶ piece (i + j))
  (one : 𝟙_ (SheafOfModules.{w} (toRingCat J Osharp)) ⟶ piece 0)
  (hassoc : ∀ i j k : ℤ, mul i j ▷ piece k ≫ mul (i + j) k =
    (α_ (piece i) (piece j) (piece k)).hom ≫ piece i ◁ mul j k ≫ mul i (j + k) ≫
      eqToHom (congrArg piece (add_assoc i j k).symm))
  (hone : ∀ i : ℤ, one ▷ piece i ≫ mul 0 i =
    (λ_ (piece i)).hom ≫ eqToHom (congrArg piece (zero_add i).symm))
  (hone' : ∀ i : ℤ, piece i ◁ one ≫ mul i 0 =
    (ρ_ (piece i)).hom ≫ eqToHom (congrArg piece (add_zero i).symm))

include hO

/-- **The morphism-level multiplication of `ofMorphismData` is the given one.** The structure
field is the bilinear map on local sections that a morphism out of the tensor product sheaf
induces, and `mulSheaf` descends a bilinear map back to such a morphism; the two are inverse to
each other. -/
theorem mulSheaf_ofMorphismData (i j : ℤ) :
    mulSheaf (ofMorphismData hO piece mul one hassoc hone hone') i j = mul i j := by
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := Osharp) (F := piece i)
    (G := piece j) (Q := piece (i + j)) fun U x y ↦ ?_
  exact mulSheaf_unit (ofMorphismData hO piece mul one hassoc hone hone') i j U x y

/-- **The morphism-level unit of `ofMorphismData` is the given one.** -/
theorem oneHom_ofMorphismData :
    oneHom (ofMorphismData hO piece mul one hassoc hone hone') = one :=
  (piece 0).unitHomEquiv.symm_apply_apply one

end OfMorphismData

/-! ### The morphism-level reading of a homomorphism of sheaves of graded algebras -/

section Hom

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (hO : Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))
  (A B : GradedAlgebra.{w, w} (toRingCat J Osharp))
  (φ : ∀ n : ℤ, A.piece n ⟶ B.piece n) (i j : ℤ)

include hO

/-- **A degreewise family of morphisms of sheaves of modules commutes with the morphism-level
multiplications if and only if it preserves products of homogeneous local sections.** The
right-hand side is the `map_mul` field of `SheafOfModules.GradedAlgebra.Hom`; the left-hand
side is the form a monoidal functor transports. -/
theorem mulSheaf_comp_eq_iff :
    mulSheaf A i j ≫ φ (i + j) = (φ i ⊗ₘ φ j) ≫ mulSheaf B i j ↔
      ∀ (U : Cᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U),
        (φ (i + j)).val.app U ((A.mul i j).app U x y) =
          (B.mul i j).app U ((φ i).val.app U x) ((φ j).val.app U y) := by
  refine ⟨fun h U x y ↦ ?_, fun h ↦ ?_⟩
  · exact (congrArg ((φ (i + j)).val.app U) (mulSheaf_unit A i j U x y).symm).trans
      ((congrArg (fun ψ : ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (A.piece i)).obj
          (A.piece j) ⟶ B.piece (i + j) ↦
            ψ.val.app U ((tensorSheafUnit (A.piece i) (A.piece j)).app U (x ⊗ₜ y))) h).trans
        ((congrArg ((mulSheaf B i j).val.app U)
            (Stacks.TensorSheafWorld.tensorHom_val_app_tensorSheafUnit Osharp hO U
              (φ i) (φ j) x y)).trans
          (mulSheaf_unit B i j U ((φ i).val.app U x) ((φ j).val.app U y))))
  · refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := Osharp) (F := A.piece i)
      (G := A.piece j) (Q := B.piece (i + j)) fun U x y ↦ ?_
    exact (congrArg ((φ (i + j)).val.app U) (mulSheaf_unit A i j U x y)).trans
      ((h U x y).trans
        ((mulSheaf_unit B i j U ((φ i).val.app U x) ((φ j).val.app U y)).symm.trans
          (congrArg ((mulSheaf B i j).val.app U)
            (Stacks.TensorSheafWorld.tensorHom_val_app_tensorSheafUnit Osharp hO U
              (φ i) (φ j) x y).symm)))

end Hom

/-! ### Transport along a lax monoidal functor -/

section Transport

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Psharp : Sheaf K CommRingCat.{w}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (F : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp))
  [F.LaxMonoidal] (A : GradedAlgebra.{w, w} (toRingCat J Osharp))

/-- **The transported multiplication** `F(A_i) ⊗ F(A_j) ⟶ F(A_{i+j})`: the multiplication of
`A` in degrees `i` and `j`, conjugated by the tensorator of `F`. -/
noncomputable def transportedMul (i j : ℤ) :
    F.obj (A.piece i) ⊗ F.obj (A.piece j) ⟶ F.obj (A.piece (i + j)) :=
  Stacks.MonoidalGraded.mapMul F (X := A.piece i) (Y := A.piece j) (Z := A.piece (i + j))
    (mulSheaf A i j)

/-- **The transported unit** `𝟙_ ⟶ F(A_0)`: the global unit of `A`, conjugated by the unit
morphism of `F`. -/
noncomputable def transportedOne :
    𝟙_ (SheafOfModules.{w} (toRingCat K Psharp)) ⟶ F.obj (A.piece 0) :=
  Stacks.MonoidalGraded.mapOne F (X := A.piece 0) (oneHom A)

variable (hO : Presheaf.IsSheaf J
  (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))

include hO

/-- **The transported multiplication is associative**, as an equality of morphisms out of
`F(A_i) ⊗ F(A_j) ⊗ F(A_k)`. -/
theorem transportedMul_assoc (i j k : ℤ) :
    transportedMul F A i j ▷ F.obj (A.piece k) ≫ transportedMul F A (i + j) k =
      (α_ (F.obj (A.piece i)) (F.obj (A.piece j)) (F.obj (A.piece k))).hom ≫
        F.obj (A.piece i) ◁ transportedMul F A j k ≫ transportedMul F A i (j + k) ≫
          eqToHom (congrArg (fun n ↦ F.obj (A.piece n)) (add_assoc i j k).symm) := by
  refine (Stacks.MonoidalGraded.mapMul_assoc F (mulSheaf A i j) (mulSheaf A j k)
    (mulSheaf A (i + j) k)
    (mulSheaf A i (j + k) ≫ eqToHom (congrArg A.piece (add_assoc i j k).symm))
    (Stacks.TensorSheafWorld.mulSheaf_assoc Osharp hO A i j k)).trans ?_
  rw [Stacks.MonoidalGraded.mapMul_comp F (mulSheaf A i (j + k)), eqToHom_map]
  rfl

/-- **The transported unit is a left identity**, as an equality of morphisms. -/
theorem transportedOne_mul (i : ℤ) :
    transportedOne F A ▷ F.obj (A.piece i) ≫ transportedMul F A 0 i =
      (λ_ (F.obj (A.piece i))).hom ≫
        eqToHom (congrArg (fun n ↦ F.obj (A.piece n)) (zero_add i).symm) := by
  refine (Stacks.MonoidalGraded.mapOne_mul F (oneHom A) (mulSheaf A 0 i)
    (eqToHom (congrArg A.piece (zero_add i).symm)) (mulSheaf_one_mul A hO i)).trans ?_
  rw [eqToHom_map]

/-- **The transported unit is a right identity**, as an equality of morphisms. -/
theorem transportedMul_one (i : ℤ) :
    F.obj (A.piece i) ◁ transportedOne F A ≫ transportedMul F A i 0 =
      (ρ_ (F.obj (A.piece i))).hom ≫
        eqToHom (congrArg (fun n ↦ F.obj (A.piece n)) (add_zero i).symm) := by
  refine (Stacks.MonoidalGraded.mapMul_one F (oneHom A) (mulSheaf A i 0)
    (eqToHom (congrArg A.piece (add_zero i).symm)) (mulSheaf_mul_one A hO i)).trans ?_
  rw [eqToHom_map]

variable (hP : Presheaf.IsSheaf K
  (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Psharp.obj))

include hP

/-- **The transport of a sheaf of graded algebras along a lax monoidal functor between
categories of sheaves of modules**, with homogeneous pieces the images `F(A_n)` of those of
`A`. -/
@[stacks 0FQX "graded_algebra_pushforward, graded_algebra_pullback"]
noncomputable def transport : GradedAlgebra.{w, w} (toRingCat K Psharp) :=
  ofMorphismData (Osharp := Psharp) hP (fun n ↦ F.obj (A.piece n)) (transportedMul F A)
    (transportedOne F A) (transportedMul_assoc F A hO) (transportedOne_mul F A hO)
    (transportedMul_one F A hO)

/-- The homogeneous pieces of `F(A)` are the images of those of `A`. -/
theorem transport_piece (n : ℤ) : (transport F A hO hP).piece n = F.obj (A.piece n) := rfl

/-- The multiplication of `F(A)` on a pure tensor of local sections. -/
theorem transport_mul_app (i j : ℤ) (U : Dᵒᵖ) (x : (F.obj (A.piece i)).val.obj U)
    (y : (F.obj (A.piece j)).val.obj U) :
    ((transport F A hO hP).mul i j).app U x y =
      (transportedMul F A i j).val.app U
        ((tensorSheafUnit (F.obj (A.piece i)) (F.obj (A.piece j))).app U (x ⊗ₜ y)) :=
  rfl

/-- The morphism-level multiplication of `F(A)` is the transported multiplication. -/
@[simp]
theorem mulSheaf_transport (i j : ℤ) :
    mulSheaf (transport F A hO hP) i j = transportedMul F A i j :=
  mulSheaf_ofMorphismData hP _ _ _ _ _ _ i j

/-- The morphism-level unit of `F(A)` is the transported unit. -/
@[simp]
theorem oneHom_transport : oneHom (transport F A hO hP) = transportedOne F A :=
  oneHom_ofMorphismData hP _ _ _ _ _ _

end Transport

/-! ### Functoriality of the transport -/

section Functoriality

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Psharp : Sheaf K CommRingCat.{w}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (F : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp))
  [F.LaxMonoidal]
  (hO : Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))
  (hP : Presheaf.IsSheaf K
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Psharp.obj))

include hO

/-- The degreewise image of a homomorphism of sheaves of graded algebras intertwines the
transported multiplications. -/
theorem transportedMul_comp {A B : GradedAlgebra.{w, w} (toRingCat J Osharp)} (φ : A ⟶ B)
    (i j : ℤ) :
    transportedMul F A i j ≫ F.map (φ.app (i + j)) =
      (F.map (φ.app i) ⊗ₘ F.map (φ.app j)) ≫ transportedMul F B i j :=
  Stacks.MonoidalGraded.mapMul_naturality F (mulSheaf A i j) (mulSheaf B i j)
    (φ.app i) (φ.app j) (φ.app (i + j))
    ((mulSheaf_comp_eq_iff hO A B φ.app i j).mpr (φ.map_mul i j))

include hP

/-- **The image of a homomorphism of sheaves of graded algebras under a lax monoidal functor.**
Degreewise it is `F` applied to the component. -/
noncomputable def transportHom {A B : GradedAlgebra.{w, w} (toRingCat J Osharp)} (φ : A ⟶ B) :
    transport F A hO hP ⟶ transport F B hO hP where
  app n := F.map (φ.app n)
  map_mul i j := by
    refine (mulSheaf_comp_eq_iff hP (transport F A hO hP) (transport F B hO hP)
      (fun n ↦ F.map (φ.app n)) i j).mp ?_
    simp only [mulSheaf_transport]
    exact transportedMul_comp F hO φ i j

/-- The degree-`n` component of `transportHom F hO hP φ` is `F.map (φ.app n)`. -/
@[simp]
theorem transportHom_app {A B : GradedAlgebra.{w, w} (toRingCat J Osharp)} (φ : A ⟶ B) (n : ℤ) :
    (transportHom F hO hP φ).app n = F.map (φ.app n) :=
  rfl

/-- **A lax monoidal functor between categories of sheaves of modules induces a functor between
the categories of sheaves of graded algebras.** -/
@[stacks 0FQX "graded_algebra_pushforward, graded_algebra_pullback: functoriality"]
noncomputable def transportFunctor :
    GradedAlgebra.{w, w} (toRingCat J Osharp) ⥤ GradedAlgebra.{w, w} (toRingCat K Psharp) where
  obj A := transport F A hO hP
  map φ := transportHom F hO hP φ
  map_id _ := Hom.ext fun n ↦ by simp [transport_piece]
  map_comp _ _ := Hom.ext fun n ↦ by simp [transport_piece]

/-- The functor `transportFunctor F hO hP` sends a sheaf of graded algebras `A` to
`transport F A hO hP`. -/
@[simp]
theorem transportFunctor_obj (A : GradedAlgebra.{w, w} (toRingCat J Osharp)) :
    (transportFunctor F hO hP).obj A = transport F A hO hP :=
  rfl

/-- The degree-`n` component of the image of `φ` under `transportFunctor F hO hP` is
`F.map (φ.app n)`. -/
@[simp]
theorem transportFunctor_map_app {A B : GradedAlgebra.{w, w} (toRingCat J Osharp)} (φ : A ⟶ B)
    (n : ℤ) : ((transportFunctor F hO hP).map φ).app n = F.map (φ.app n) :=
  rfl

end Functoriality

end SheafOfModules.GradedAlgebra

end
