module

public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionPresentation

/-!
# Square-zero extensions of `f⁻¹𝒪_S`-algebras and their morphisms

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces and `𝒢` an `𝒪_X`-module. An
*extension of `f⁻¹𝒪_S`-algebras*

`0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0`

*with `𝒢` an ideal of square zero* is a sheaf of commutative rings `𝒪_{X'}` on `X` under
`f⁻¹𝒪_S`, a surjection `𝒪_{X'} ⟶ 𝒪_X` of `f⁻¹𝒪_S`-algebras, and an identification of its kernel
with `𝒢` as `𝒪_X`-modules. These are the objects classified by **Stacks 0GPZ**.

`AlgebraSquareZeroExtension` carries all of this except that the identification of the kernel
with `𝒢` is only a map `Ker(𝒪_{X'} ⟶ 𝒪_X) ⟶ 𝒢`; `SquareZeroAlgebraExtension` asks that map to
be bijective, which is the exactness of `0 ⟶ 𝒢 ⟶ 𝒪_{X'}` at `𝒢` and at `𝒪_{X'}`. The square-zero
condition is then automatic: a restriction datum kills the square of the kernel
(`Stacks.Sites.Conormal.IdealRestriction.app_mul`), so the kernel squares to zero.

A morphism of such extensions is a morphism of sheaves of rings under `f⁻¹𝒪_S`, over `𝒪_X`,
and the identity on `𝒢`. Every morphism is an isomorphism (`isIso_hom`), which is the
five lemma, so the isomorphism classes of **Stacks 0GPZ** are the classes of
`CategoryTheory.isIsomorphicSetoid`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.SquareZeroAlgebraExtension`: an extension of
  `f⁻¹𝒪_S`-algebras of `𝒪_X` by the square-zero ideal `𝒢`.
* `SquareZeroAlgebraExtension.Hom`: morphisms of extensions, forming a category.
* `SquareZeroAlgebraExtension.IsomorphismClasses`: the set of isomorphism classes.

## Main results

* `SquareZeroAlgebraExtension.sq_eq_zero`: the kernel of the reduction squares to zero.
* `SquareZeroAlgebraExtension.isIso_hom`: every morphism of extensions is an isomorphism of
  sheaves of rings, and `SquareZeroAlgebraExtension.isoOfHom` the resulting isomorphism of
  extensions.

## References

* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Sites.Conormal (IdealRestriction kernelIdeal kernelIdeal_le_comap hom_of_comp_eq)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S : RingedSpace.{u, u}}

/-- **An extension `0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_S`-algebras with `𝒢` an ideal of square
zero**, the objects of **Stacks 0GPZ**: an `AlgebraSquareZeroExtension` whose identification of
the kernel of the reduction with `𝒢` is bijective on sections. -/
structure SquareZeroAlgebraExtension (f : X ⟶ S)
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology X.carrier) X.sheaf))
    extends AlgebraSquareZeroExtension f G where
  /-- The kernel of the reduction is identified with `𝒢`. -/
  ideal_bijective : ∀ U : (Opens X.carrier)ᵒᵖ, Function.Bijective (ideal.app U)

namespace SquareZeroAlgebraExtension

variable {f : X ⟶ S}
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}

/-- Two kernel sections with the same image in `𝒢` have the same underlying section. -/
private theorem val_eq_of_ideal_app_eq (P : SquareZeroAlgebraExtension f G)
    {U : (Opens X.carrier)ᵒᵖ} {a b : kernelIdeal P.reduction.hom U}
    (h : P.ideal.app U a = P.ideal.app U b) : a.1 = b.1 :=
  congrArg Subtype.val ((P.ideal_bijective U).1 h)

/-- **The ideal `𝒢` has square zero**: the product of two local sections of `𝒪_{X'}` killed by
the reduction vanishes. -/
theorem sq_eq_zero (P : SquareZeroAlgebraExtension f G) (U : (Opens X.carrier)ᵒᵖ)
    (a b : kernelIdeal P.reduction.hom U) : (a : P.sheaf.obj.obj U) * b = 0 := by
  have h : P.ideal.app U (a * b) = P.ideal.app U 0 :=
    (IdealRestriction.app_mul _ U a b).trans (map_zero _).symm
  exact P.val_eq_of_ideal_app_eq h

/-- A morphism of sheaves of rings over `𝒪_X` carries the kernel of the first reduction into the
kernel of the second. -/
theorem map_mem_kernelIdeal {P Q : SquareZeroAlgebraExtension f G} (N : P.sheaf ⟶ Q.sheaf)
    (hred : N ≫ Q.reduction = P.reduction) (U : (Opens X.carrier)ᵒᵖ)
    (y : kernelIdeal P.reduction.hom U) :
    (N.hom.app U).hom y.1 ∈ kernelIdeal Q.reduction.hom U :=
  kernelIdeal_le_comap P.reduction.hom Q.reduction.hom N.hom (hom_of_comp_eq hred) U y.2

/-- **A morphism of extensions**: a morphism of sheaves of rings under `f⁻¹𝒪_S`, over `𝒪_X`,
and the identity on `𝒢`. -/
@[ext]
structure Hom (P Q : SquareZeroAlgebraExtension f G) where
  /-- The morphism of sheaves of rings `𝒪_{X'} ⟶ 𝒪_{X''}`. -/
  hom : P.sheaf ⟶ Q.sheaf
  /-- It is a morphism over `𝒪_X`. -/
  hom_reduction : hom ≫ Q.reduction = P.reduction := by cat_disch
  /-- It is a morphism under `f⁻¹𝒪_S`. -/
  base_hom : P.base ≫ hom = Q.base := by cat_disch
  /-- It is the identity on `𝒢`. -/
  ideal_hom : ∀ (U : (Opens X.carrier)ᵒᵖ) (y : kernelIdeal P.reduction.hom U),
    Q.ideal.app U ⟨(hom.hom.app U).hom y.1, map_mem_kernelIdeal hom hom_reduction U y⟩ =
      P.ideal.app U y

attribute [reassoc (attr := simp)] Hom.hom_reduction Hom.base_hom

/-- The identity morphism of an extension. -/
@[simps]
def Hom.id (P : SquareZeroAlgebraExtension f G) : Hom P P where
  hom := 𝟙 _
  ideal_hom _ _ := rfl

/-- The composition of morphisms of extensions. -/
@[simps]
def Hom.comp {P Q R : SquareZeroAlgebraExtension f G} (φ : Hom P Q) (ψ : Hom Q R) : Hom P R where
  hom := φ.hom ≫ ψ.hom
  hom_reduction := (Category.assoc _ _ _).trans
    ((congrArg (φ.hom ≫ ·) ψ.hom_reduction).trans φ.hom_reduction)
  base_hom := (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ ψ.hom) φ.base_hom).trans ψ.base_hom)
  ideal_hom U y := (ψ.ideal_hom U ⟨_, map_mem_kernelIdeal φ.hom φ.hom_reduction U y⟩).trans
    (φ.ideal_hom U y)

/-- Extensions of `f⁻¹𝒪_S`-algebras of `𝒪_X` by `𝒢` and their morphisms form a category. -/
instance : Category (SquareZeroAlgebraExtension f G) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

/-- Two morphisms of extensions are equal if their underlying morphisms of sheaves of rings are
equal. -/
@[ext]
theorem hom_ext {P Q : SquareZeroAlgebraExtension f G} {φ ψ : P ⟶ Q}
    (h : φ.hom = ψ.hom) : φ = ψ :=
  Hom.ext h

/-- The underlying morphism of sheaves of rings of the identity is the identity. -/
@[simp] theorem id_hom (P : SquareZeroAlgebraExtension f G) :
    Hom.hom (𝟙 P) = 𝟙 P.sheaf := rfl

/-- The underlying morphism of sheaves of rings of a composite is the composite. -/
@[simp, reassoc] theorem comp_hom {P Q R : SquareZeroAlgebraExtension f G} (φ : P ⟶ Q)
    (ψ : Q ⟶ R) : Hom.hom (φ ≫ ψ) = φ.hom ≫ ψ.hom := rfl

variable {P Q : SquareZeroAlgebraExtension f G}

/-- A morphism of extensions is injective on sections: a section it kills dies in `𝒪_X`, hence
lies in `𝒢`, where the morphism is the identity. -/
theorem Hom.injective (φ : P ⟶ Q) (U : (Opens X.carrier)ᵒᵖ) :
    Function.Injective (φ.hom.hom.app U) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hker : x ∈ kernelIdeal P.reduction.hom U := by
    show (P.reduction.hom.app U).hom x = 0
    rw [← φ.hom_reduction]
    show (Q.reduction.hom.app U).hom ((φ.hom.hom.app U).hom x) = 0
    rw [show (φ.hom.hom.app U).hom x = 0 from hx, map_zero]
  have h : P.ideal.app U ⟨x, hker⟩ = P.ideal.app U 0 := by
    rw [← φ.ideal_hom U ⟨x, hker⟩, map_zero]
    exact (congrArg (Q.ideal.app U) (Subtype.ext hx)).trans (map_zero _)
  exact P.val_eq_of_ideal_app_eq h

/-- A morphism of extensions is locally surjective: locally a section of the target has the same
image in `𝒪_X` as a section of the source, and the difference lies in `𝒢`, where the morphism
is the identity. -/
theorem Hom.isLocallySurjective (φ : P ⟶ Q) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) φ.hom.hom where
  imageSieve_mem {U} y := by
    refine (Opens.grothendieckTopology X.carrier).superset_covering (fun V g hg ↦ ?_)
      (Presheaf.imageSieve_mem _ P.reduction.hom ((Q.reduction.hom.app (op U)).hom y))
    obtain ⟨x, hx⟩ := hg
    let y' := (Q.sheaf.obj.map g.op).hom y
    have hd : y' - (φ.hom.hom.app (op V)).hom x ∈ kernelIdeal Q.reduction.hom (op V) := by
      show (Q.reduction.hom.app (op V)).hom (y' - (φ.hom.hom.app (op V)).hom x) = 0
      rw [map_sub]
      have e1 : (Q.reduction.hom.app (op V)).hom ((φ.hom.hom.app (op V)).hom x) =
          (P.reduction.hom.app (op V)).hom x := by
        rw [← φ.hom_reduction]; rfl
      have e2 : (Q.reduction.hom.app (op V)).hom y' =
          (X.sheaf.obj.map g.op).hom ((Q.reduction.hom.app (op U)).hom y) :=
        NatTrans.naturality_apply Q.reduction.hom g.op y
      rw [e1, e2, hx, sub_self]
    obtain ⟨k, hk⟩ := (P.ideal_bijective (op V)).2 (Q.ideal.app (op V) ⟨_, hd⟩)
    have hk' : (φ.hom.hom.app (op V)).hom k.1 = y' - (φ.hom.hom.app (op V)).hom x := by
      have := (φ.ideal_hom (op V) k).trans hk
      exact Q.val_eq_of_ideal_app_eq this
    refine ⟨x + k.1, ?_⟩
    show (φ.hom.hom.app (op V)).hom (x + k.1) = y'
    rw [map_add, hk', add_sub_cancel]

/-- **Every morphism of extensions is an isomorphism of sheaves of rings.** -/
instance isIso_hom (φ : P ⟶ Q) : IsIso φ.hom := by
  have hi : Sheaf.IsLocallyInjective φ.hom :=
    Presheaf.isLocallyInjective_of_injective _ _ (φ.injective)
  have hs : Sheaf.IsLocallySurjective φ.hom := φ.isLocallySurjective
  exact (Sheaf.isLocallyBijective_iff_isIso φ.hom).1 ⟨hi, hs⟩

/-- The inverse of a morphism of extensions, as a morphism of extensions. -/
def Hom.inv (φ : P ⟶ Q) : Q ⟶ P where
  hom := CategoryTheory.inv φ.hom
  hom_reduction := (IsIso.inv_comp_eq φ.hom).2 φ.hom_reduction.symm
  base_hom := (IsIso.comp_inv_eq φ.hom).2 φ.base_hom.symm
  ideal_hom U y := by
    have hy : (φ.hom.hom.app U).hom ((((CategoryTheory.inv φ.hom).hom.app U).hom) y.1) = y.1 :=
      congrArg (fun t : Q.sheaf ⟶ Q.sheaf ↦ (t.hom.app U).hom y.1) (IsIso.inv_hom_id φ.hom)
    refine (φ.ideal_hom U ⟨_, map_mem_kernelIdeal _
      ((IsIso.inv_comp_eq φ.hom).2 φ.hom_reduction.symm) U y⟩).symm.trans ?_
    exact congrArg (Q.ideal.app U) (Subtype.ext hy)

/-- **A morphism of extensions is an isomorphism of extensions.** -/
@[simps hom]
def isoOfHom (φ : P ⟶ Q) : P ≅ Q where
  hom := φ
  inv := φ.inv
  hom_inv_id := hom_ext (IsIso.hom_inv_id φ.hom)
  inv_hom_id := hom_ext (IsIso.inv_hom_id φ.hom)

/-! ### The inclusion of `𝒢` -/

section Inclusion

variable (P : SquareZeroAlgebraExtension f G) (U : (Opens X.carrier)ᵒᵖ)

/-- The identification of the kernel of the reduction with `𝒢`, on sections over `U`. -/
def idealEquiv : kernelIdeal P.reduction.hom U ≃+ G.val.obj U :=
  AddEquiv.ofBijective (P.ideal.app U) (P.ideal_bijective U)

/-- **The inclusion `𝒢 ⟶ 𝒪_{X'}`** on sections over `U`. -/
def incl (g : G.val.obj U) : P.sheaf.obj.obj U :=
  ((P.idealEquiv U).symm g).1

/-- The inclusion of `𝒢` lands in the kernel of the reduction. -/
theorem incl_mem (g : G.val.obj U) : P.incl U g ∈ kernelIdeal P.reduction.hom U :=
  ((P.idealEquiv U).symm g).2

/-- The reduction `𝒪_{X'} ⟶ 𝒪_X` kills the image of `𝒢`. -/
theorem reduction_incl (g : G.val.obj U) : (P.reduction.hom.app U).hom (P.incl U g) = 0 :=
  P.incl_mem U g

/-- The identification of the kernel with `𝒢` sends the image of `g` back to `g`. -/
theorem ideal_incl (g : G.val.obj U) : P.ideal.app U ⟨P.incl U g, P.incl_mem U g⟩ = g :=
  (P.idealEquiv U).apply_symm_apply g

/-- The inclusion of `𝒢` sends the image of a kernel section `y` back to `y`. -/
theorem incl_ideal (y : kernelIdeal P.reduction.hom U) : P.incl U (P.ideal.app U y) = y.1 :=
  congrArg Subtype.val ((P.idealEquiv U).symm_apply_apply y)

/-- The inclusion `𝒢 ⟶ 𝒪_{X'}` is injective on sections. -/
theorem incl_injective : Function.Injective (P.incl U) := fun _ _ h ↦
  (P.idealEquiv U).symm.injective (Subtype.ext h)

/-- The inclusion `𝒢 ⟶ 𝒪_{X'}` is additive. -/
theorem incl_add (g g' : G.val.obj U) : P.incl U (g + g') = P.incl U g + P.incl U g' :=
  congrArg Subtype.val (map_add (P.idealEquiv U).symm g g')

/-- The inclusion `𝒢 ⟶ 𝒪_{X'}` sends zero to zero. -/
theorem incl_zero : P.incl U 0 = 0 :=
  congrArg Subtype.val (map_zero (P.idealEquiv U).symm)

/-- The inclusion `𝒢 ⟶ 𝒪_{X'}` commutes with subtraction. -/
theorem incl_sub (g g' : G.val.obj U) : P.incl U (g - g') = P.incl U g - P.incl U g' :=
  congrArg Subtype.val (map_sub (P.idealEquiv U).symm g g')

/-- The inclusion `𝒢 ⟶ 𝒪_{X'}` commutes with negation. -/
theorem incl_neg (g : G.val.obj U) : P.incl U (-g) = -P.incl U g :=
  congrArg Subtype.val (map_neg (P.idealEquiv U).symm g)

/-- If a kernel section `y` maps to `g` in `𝒢`, then the inclusion of `g` is `y`. -/
private theorem incl_eq_of_ideal_app_eq {y : kernelIdeal P.reduction.hom U} {g : G.val.obj U}
    (h : P.ideal.app U y = g) : P.incl U g = y.1 :=
  h ▸ P.incl_ideal U y

/-- `𝒪_{X'}` acts on `𝒢` through `𝒪_X`. -/
theorem incl_smul (x : P.sheaf.obj.obj U) (g : G.val.obj U) :
    P.incl U (Stacks.Sites.Conormal.presentationScalar P.reduction U x • g) =
      x * P.incl U g := by
  have h := P.ideal.app_smul U x ⟨P.incl U g, P.incl_mem U g⟩
  rw [P.ideal_incl] at h
  exact P.incl_eq_of_ideal_app_eq U h

/-- The ideal `𝒢` has square zero. -/
theorem incl_mul_incl (g g' : G.val.obj U) : P.incl U g * P.incl U g' = 0 :=
  P.sq_eq_zero U ⟨_, P.incl_mem U g⟩ ⟨_, P.incl_mem U g'⟩

/-- The inclusion `𝒢 ⟶ 𝒪_{X'}` commutes with restriction of sections. -/
theorem incl_map {V : (Opens X.carrier)ᵒᵖ} (i : U ⟶ V) (g : G.val.obj U) :
    (P.sheaf.obj.map i).hom (P.incl U g) = P.incl V (G.val.map i g) := by
  have h := P.ideal.app_map i ⟨P.incl U g, P.incl_mem U g⟩
  rw [P.ideal_incl] at h
  exact (P.incl_eq_of_ideal_app_eq V h).symm

end Inclusion

variable (f G) in
/-- **The isomorphism classes of extensions** `0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of
`f⁻¹𝒪_S`-algebras with `𝒢` an ideal of square zero. -/
abbrev IsomorphismClasses : Type (u + 1) :=
  Quotient (isIsomorphicSetoid (SquareZeroAlgebraExtension f G))

end SquareZeroAlgebraExtension

end AlgebraicGeometry.RingedSpaceThickening

end
