module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Functor.EpiMono
public import StacksFrontier.CategoryTheory.Monoidal.InternalEndMonoid

/-!
# The image of a point of a monoid object, and the module it carries

Let `𝒜` be an abelian monoidal closed category, let `C` be a monoid object of `𝒜` and let
`p : 𝟙_ 𝒜 ⟶ C.X` be a *point* of it. There are two endomorphisms of `C.X` attached to `p`:
right multiplication `CategoryTheory.Mon.rightMul C p`, which on elements is `x ↦ x * p`, and
left multiplication `CategoryTheory.Mon.leftMul C p`, which is `x ↦ p * x`. Their images are
the subobjects `C * p` and `p * C` of `C.X`, and each is a module over `C`: the image of right
multiplication is a *left* module, and the image of left multiplication is a *right* module.
The right module is then read as a morphism of monoid objects
`C ⟶ MonoidalClosed.internalEnd (p * C)`.

The existence of the restricted multiplication is the only non-formal step. Tensoring with a
fixed object is a left adjoint in a closed monoidal category, hence preserves epimorphisms, so
`C.X ◁ factorThruImage (rightMul C p)` is an epimorphism; composing the candidate action with the
cokernel of the image inclusion and precomposing with that epimorphism gives

`(C.X ◁ rightMul C p) ≫ μ ≫ cokernel.π ι = μ ≫ rightMul C p ≫ cokernel.π ι = 0`

by the key associativity identity `CategoryTheory.Mon.mul_comp_rightMul`, which says
`(x * y) * p = x * (y * p)`. So the candidate action is killed by the cokernel of a
monomorphism, and in an abelian category it therefore factors through that monomorphism
(`CategoryTheory.Abelian.monoLift`).

## Main definitions

* `CategoryTheory.Limits.imageIsoOfConj`: the images of two conjugate endomorphisms are
  isomorphic. This is a general fact about images, recorded here because the two statements
  about isomorphisms of monoid objects both reduce to it.
* `CategoryTheory.Mon.rightMul` and `CategoryTheory.Mon.leftMul`: right and left multiplication
  by a point of a monoid object.
* `CategoryTheory.Mon.imageAction`: the left action of `C` on the image of right multiplication
  by `p`.
* `CategoryTheory.Mon.imageActionRight`: the right action of `C` on the image of left
  multiplication by `p`.
* `CategoryTheory.Mon.imageRep`: the induced morphism of monoid objects from `C` to the internal
  endomorphism monoid of the image of left multiplication by `p`.
* `CategoryTheory.Mon.imageIso` and `CategoryTheory.Mon.imageIsoLeft`: an isomorphism of monoid
  objects carrying one point to the other carries each image to the corresponding image.

## Main results

* `CategoryTheory.Mon.mul_comp_rightMul`: **right multiplication by a point commutes with the
  multiplication of the monoid**, `(x * y) * p = x * (y * p)`, and
  `CategoryTheory.Mon.mul_comp_leftMul` is its mirror `p * (x * y) = (p * x) * y`. Everything
  else rests on these.
* `CategoryTheory.Mon.imageAction_comp_ι` and `CategoryTheory.Mon.imageActionRight_comp_ι`: each
  action is the restriction of the multiplication of `C`, which is what characterises it.
* `CategoryTheory.Mon.one_imageAction`, `CategoryTheory.Mon.mul_imageAction`,
  `CategoryTheory.Mon.imageActionRight_one` and `CategoryTheory.Mon.imageActionRight_mul`:
  **the module axioms.**
* `CategoryTheory.Mon.isMonHom_imageRepHom`: **the right action is a morphism of monoid objects
  into the internal endomorphism monoid.**
* `CategoryTheory.Mon.imageAction_comp_imageIso_hom` and
  `CategoryTheory.Mon.imageActionRight_comp_imageIsoLeft_hom`: the comparison of images
  intertwines the two actions, and `CategoryTheory.Mon.imageRep_naturality` says the same for
  the induced representations.

## Implementation notes

The module axioms are proved by composing with the image inclusion, which is a monomorphism, and
rewriting with `CategoryTheory.Mon.imageAction_comp_ι`; `cancel_mono` is the whole technique.

The *right* action, not the left one, is what represents into
`CategoryTheory.MonoidalClosed.internalEnd`. Mathlib's `MonoidalClosed.comp x y z` is the
*diagrammatic* composition `(x ⟶ y) ⊗ (y ⟶ z) ⟶ (x ⟶ z)` — its first factor is applied first,
see `CategoryTheory.MonoidalClosed.compTranspose` — so the monoid object `internalEnd H` is the
opposite of the endomorphism monoid under composition of functions, and a morphism of monoid
objects `C ⟶ internalEnd H` uncurries to a *right* `C`-module structure on `H`. A left module
gives an anti-morphism instead; concretely, for a left action `a` the two sides of the
multiplication law of `MonoidalClosed.curry ((β_ H C.X).hom ≫ a)` reduce to

`(β_ H (C.X ⊗ C.X)).hom ≫ (α_ C.X C.X H).hom ≫ C.X ◁ a ≫ a` and
`(α_ H C.X C.X).inv ≫ (β_ H C.X).hom ▷ C.X ≫ (β_ (C.X ⊗ H) C.X).hom ≫ C.X ◁ a ≫ a`,

i.e. to `x * (y * h)` and `y * (x * h)`, which differ. This is why `imageRep` is built on
`leftMul` and `imageActionRight`: the subobject `p * C` is stable under multiplication on the
right, which `C * p` is not.

`CategoryTheory.Mon.epi_whiskerRight` needs a braiding, because `MonoidalClosed` only makes
`MonoidalCategory.tensorLeft` a left adjoint; the braiding identifies `- ▷ X` with `X ◁ -` up to
isomorphism.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits MonoidalClosed
open scoped MonObj

namespace CategoryTheory.Limits

variable {𝒜 : Type*} [Category 𝒜] {A B : 𝒜} {f : A ⟶ A} {g : B ⟶ B}

/-- Conjugating `g` back along `u` returns `f`. -/
theorem conj_comp_inv (u : A ≅ B) (h : f ≫ u.hom = u.hom ≫ g) : u.hom ≫ g ≫ u.inv = f := by
  rw [← Category.assoc, ← h, Category.assoc, u.hom_inv_id, Category.comp_id]

/-- Conjugacy of endomorphisms is symmetric. -/
theorem conj_symm (u : A ≅ B) (h : f ≫ u.hom = u.hom ≫ g) :
    g ≫ u.symm.hom = u.symm.hom ≫ f := by
  simp only [Iso.symm_hom]
  rw [← cancel_epi u.hom, Iso.hom_inv_id_assoc, conj_comp_inv u h]

variable [HasImage f] [HasImage g]

/-- The comparison map between the images of two conjugate endomorphisms: the image of `g`,
pulled back along `u`, is a mono factorisation of `f`. -/
noncomputable def imageHomOfConj (u : A ≅ B) (h : f ≫ u.hom = u.hom ≫ g) : image f ⟶ image g :=
  image.lift
    { I := image g
      m := image.ι g ≫ u.inv
      e := u.hom ≫ factorThruImage g
      fac := by rw [Category.assoc, image.fac_assoc, conj_comp_inv u h] }

/-- The comparison map between the images of two conjugate endomorphisms is compatible with the
two image inclusions and the conjugating isomorphism. -/
@[reassoc (attr := simp)]
theorem imageHomOfConj_comp_ι (u : A ≅ B) (h : f ≫ u.hom = u.hom ≫ g) :
    imageHomOfConj u h ≫ image.ι g = image.ι f ≫ u.hom := by
  rw [← Iso.comp_inv_eq, Category.assoc]
  exact image.lift_fac _

/-- **Conjugate endomorphisms have isomorphic images.** -/
noncomputable def imageIsoOfConj (u : A ≅ B) (h : f ≫ u.hom = u.hom ≫ g) : image f ≅ image g where
  hom := imageHomOfConj u h
  inv := imageHomOfConj u.symm (conj_symm u h)
  hom_inv_id := by
    rw [← cancel_mono (image.ι f), Category.assoc, imageHomOfConj_comp_ι,
      imageHomOfConj_comp_ι_assoc]
    simp
  inv_hom_id := by
    rw [← cancel_mono (image.ι g), Category.assoc, imageHomOfConj_comp_ι,
      imageHomOfConj_comp_ι_assoc]
    simp

end CategoryTheory.Limits

namespace CategoryTheory.Mon

variable {𝒜 : Type*} [Category 𝒜] [MonoidalCategory 𝒜]

/-- The underlying isomorphism of an isomorphism of monoid objects. -/
@[simps]
def homIso {C D : Mon 𝒜} (e : C ≅ D) : C.X ≅ D.X where
  hom := e.hom.hom
  inv := e.inv.hom
  hom_inv_id := congrArg Mon.Hom.hom e.hom_inv_id
  inv_hom_id := congrArg Mon.Hom.hom e.inv_hom_id

/-- Right multiplication by a point `p : 𝟙_ 𝒜 ⟶ C.X` of a monoid object `C`: the endomorphism
`x ↦ x * p` of `C.X`. -/
def rightMul (C : Mon 𝒜) (p : 𝟙_ 𝒜 ⟶ C.X) : C.X ⟶ C.X := (ρ_ C.X).inv ≫ (C.X ◁ p) ≫ μ

/-- Left multiplication by a point `p : 𝟙_ 𝒜 ⟶ C.X` of a monoid object `C`: the endomorphism
`x ↦ p * x` of `C.X`. -/
def leftMul (C : Mon 𝒜) (p : 𝟙_ 𝒜 ⟶ C.X) : C.X ⟶ C.X := (λ_ C.X).inv ≫ (p ▷ C.X) ≫ μ

/-- **Right multiplication by a point commutes with the multiplication of the monoid**:
`(x * y) * p = x * (y * p)`. This is the associativity axiom of `C` together with coherence,
and it is the identity the left action below rests on. -/
@[reassoc]
theorem mul_comp_rightMul (C : Mon 𝒜) (p : 𝟙_ 𝒜 ⟶ C.X) :
    μ ≫ rightMul C p = (C.X ◁ rightMul C p) ≫ μ := by
  simp only [rightMul, MonoidalCategory.whiskerLeft_comp, Category.assoc,
    rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc]
  rw [MonObj.mul_assoc, associator_naturality_right_assoc, rightUnitor_tensor_inv_assoc]
  simp

/-- **Left multiplication by a point commutes with the multiplication of the monoid**:
`p * (x * y) = (p * x) * y`. This is the identity the right action below rests on. -/
@[reassoc]
theorem mul_comp_leftMul (C : Mon 𝒜) (p : 𝟙_ 𝒜 ⟶ C.X) :
    μ ≫ leftMul C p = (leftMul C p ▷ C.X) ≫ μ := by
  simp only [leftMul, comp_whiskerRight, Category.assoc,
    leftUnitor_inv_naturality_assoc, whisker_exchange_assoc]
  rw [MonObj.mul_assoc_flip, associator_inv_naturality_left_assoc, leftUnitor_tensor_inv_assoc]
  simp

/-- A morphism of monoid objects carries right multiplication by a point to right multiplication
by the image of that point. -/
theorem rightMul_comp_hom {C D : Mon 𝒜} (f : C ⟶ D) (p : 𝟙_ 𝒜 ⟶ C.X) :
    rightMul C p ≫ f.hom = f.hom ≫ rightMul D (p ≫ f.hom) := by
  rw [rightMul, rightMul, Category.assoc, Category.assoc, IsMonHom.mul_hom f.hom,
    ← Category.assoc (C.X ◁ p), tensorHom_def, ← Category.assoc (C.X ◁ p),
    whisker_exchange, Category.assoc, Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, ← rightUnitor_inv_naturality_assoc]

/-- A morphism of monoid objects carries left multiplication by a point to left multiplication
by the image of that point. -/
theorem leftMul_comp_hom {C D : Mon 𝒜} (f : C ⟶ D) (p : 𝟙_ 𝒜 ⟶ C.X) :
    leftMul C p ≫ f.hom = f.hom ≫ leftMul D (p ≫ f.hom) := by
  rw [leftMul, leftMul, Category.assoc, Category.assoc, IsMonHom.mul_hom f.hom,
    ← Category.assoc (p ▷ C.X), tensorHom_def', ← Category.assoc (p ▷ C.X),
    ← whisker_exchange, Category.assoc, Category.assoc,
    ← comp_whiskerRight_assoc, ← leftUnitor_inv_naturality_assoc]

/-- An isomorphism of monoid objects carrying `p` to `q` conjugates right multiplication by `p`
into right multiplication by `q`. -/
theorem rightMul_conj {C D : Mon 𝒜} (e : C ≅ D) {p : 𝟙_ 𝒜 ⟶ C.X} {q : 𝟙_ 𝒜 ⟶ D.X}
    (h : p ≫ e.hom.hom = q) :
    rightMul C p ≫ (homIso e).hom = (homIso e).hom ≫ rightMul D q := by
  rw [homIso_hom, rightMul_comp_hom, h]

/-- An isomorphism of monoid objects carrying `p` to `q` conjugates left multiplication by `p`
into left multiplication by `q`. -/
theorem leftMul_conj {C D : Mon 𝒜} (e : C ≅ D) {p : 𝟙_ 𝒜 ⟶ C.X} {q : 𝟙_ 𝒜 ⟶ D.X}
    (h : p ≫ e.hom.hom = q) :
    leftMul C p ≫ (homIso e).hom = (homIso e).hom ≫ leftMul D q := by
  rw [homIso_hom, leftMul_comp_hom, h]

/-- Tensoring on the left with a fixed object of a closed monoidal category preserves
epimorphisms, because it is a left adjoint. -/
theorem epi_whiskerLeft [MonoidalClosed 𝒜] (X : 𝒜) {A B : 𝒜} (f : A ⟶ B) [Epi f] :
    Epi (X ◁ f) := by
  have : Epi ((tensorLeft X).map f) := inferInstance
  simpa using this

/-- Tensoring on the right with a fixed object of a braided closed monoidal category preserves
epimorphisms: the braiding turns `- ▷ X` into `X ◁ -` up to isomorphism. -/
theorem epi_whiskerRight [BraidedCategory 𝒜] [MonoidalClosed 𝒜] (X : 𝒜) {A B : 𝒜} (f : A ⟶ B)
    [Epi f] : Epi (f ▷ X) := by
  have hf : f ▷ X = (β_ A X).hom ≫ (X ◁ f) ≫ (β_ B X).inv := by
    rw [← Category.assoc, ← BraidedCategory.braiding_naturality_left, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have := epi_whiskerLeft X f
  rw [hf]
  infer_instance

/-! ### The left action on the image of right multiplication -/

section RightMul

variable [Abelian 𝒜] [MonoidalClosed 𝒜] (C : Mon 𝒜) (p : 𝟙_ 𝒜 ⟶ C.X)

omit [MonoidalClosed 𝒜] in
/-- Right multiplication by `p` is killed by the cokernel of the inclusion of its image. -/
theorem rightMul_comp_cokernel_π :
    rightMul C p ≫ cokernel.π (image.ι (rightMul C p)) = 0 := by
  rw [← image.fac_assoc, cokernel.condition, comp_zero]

/-- The multiplication of `C`, restricted along the inclusion of the image of right
multiplication by `p`, is killed by the cokernel of that inclusion. This is the hypothesis
`CategoryTheory.Mon.imageAction` needs. -/
theorem whiskerLeft_ι_mul_comp_cokernel_π :
    ((C.X ◁ image.ι (rightMul C p)) ≫ μ) ≫ cokernel.π (image.ι (rightMul C p)) = 0 := by
  have := epi_whiskerLeft C.X (factorThruImage (rightMul C p))
  rw [← cancel_epi (C.X ◁ factorThruImage (rightMul C p)), comp_zero]
  simp only [Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, image.fac, ← mul_comp_rightMul_assoc,
    rightMul_comp_cokernel_π, comp_zero]

/-- The left action of the monoid object `C` on the image of right multiplication by the point
`p`, i.e. on the subobject `C * p` of `C.X`: the multiplication of `C` factored through the
inclusion of the image. -/
noncomputable def imageAction : C.X ⊗ image (rightMul C p) ⟶ image (rightMul C p) :=
  Abelian.monoLift (image.ι (rightMul C p)) ((C.X ◁ image.ι (rightMul C p)) ≫ μ)
    (whiskerLeft_ι_mul_comp_cokernel_π C p)

/-- The action of `C` on `C * p` is the restriction of the multiplication of `C`. As the
inclusion of the image is a monomorphism, this characterises the action. -/
@[reassoc (attr := simp)]
theorem imageAction_comp_ι : imageAction C p ≫ image.ι (rightMul C p)
    = (C.X ◁ image.ι (rightMul C p)) ≫ μ :=
  Abelian.monoLift_comp _ _ _

/-- **The unit axiom of the left action of `C` on `C * p`.** -/
theorem one_imageAction :
    (λ_ (image (rightMul C p))).inv ≫ (η[C.X] ▷ image (rightMul C p)) ≫ imageAction C p
      = 𝟙 (image (rightMul C p)) := by
  rw [← cancel_mono (image.ι (rightMul C p))]
  simp only [Category.assoc, imageAction_comp_ι, Category.id_comp]
  rw [← whisker_exchange_assoc, MonObj.one_mul]
  simp

/-- The unit axiom of the left action of `C` on `C * p`, with the unitor on the right. -/
@[reassoc (attr := simp)]
theorem one_whiskerRight_imageAction :
    (η[C.X] ▷ image (rightMul C p)) ≫ imageAction C p = (λ_ (image (rightMul C p))).hom := by
  have h := one_imageAction C p
  rw [Iso.inv_comp_eq] at h
  simpa using h

/-- **The associativity axiom of the left action of `C` on `C * p`.** -/
theorem mul_imageAction :
    (μ[C.X] ▷ image (rightMul C p)) ≫ imageAction C p
      = (α_ C.X C.X (image (rightMul C p))).hom ≫ (C.X ◁ imageAction C p) ≫ imageAction C p := by
  rw [← cancel_mono (image.ι (rightMul C p))]
  simp only [Category.assoc, imageAction_comp_ι, ← MonoidalCategory.whiskerLeft_comp_assoc,
    imageAction_comp_ι]
  rw [← whisker_exchange_assoc, MonObj.mul_assoc, associator_naturality_right_assoc]
  simp [MonoidalCategory.whiskerLeft_comp]

variable {C} {D : Mon 𝒜} (e : C ≅ D) {p} {q : 𝟙_ 𝒜 ⟶ D.X} (h : p ≫ e.hom.hom = q)

/-- **An isomorphism of monoid objects carrying one point to the other carries the image of
right multiplication to the image of right multiplication.** -/
noncomputable def imageIso : image (rightMul C p) ≅ image (rightMul D q) :=
  imageIsoOfConj _ (rightMul_conj e h)

omit [MonoidalClosed 𝒜] in
/-- The comparison of the images of right multiplication is compatible with the two image
inclusions. -/
@[reassoc (attr := simp)]
theorem imageIso_hom_comp_ι :
    (imageIso e h).hom ≫ image.ι (rightMul D q) = image.ι (rightMul C p) ≫ e.hom.hom :=
  imageHomOfConj_comp_ι (homIso e) (rightMul_conj e h)

/-- **The comparison of the images of right multiplication intertwines the two left actions.** -/
theorem imageAction_comp_imageIso_hom :
    imageAction C p ≫ (imageIso e h).hom
      = (e.hom.hom ⊗ₘ (imageIso e h).hom) ≫ imageAction D q := by
  rw [← cancel_mono (image.ι (rightMul D q))]
  simp only [Category.assoc, imageIso_hom_comp_ι, imageAction_comp_ι, imageAction_comp_ι_assoc,
    ← id_tensorHom, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc,
    Category.comp_id, Category.id_comp]

end RightMul

/-! ### The right action on the image of left multiplication, and the representation -/

section LeftMul

variable [Abelian 𝒜] [BraidedCategory 𝒜] [MonoidalClosed 𝒜] (C : Mon 𝒜) (p : 𝟙_ 𝒜 ⟶ C.X)

omit [BraidedCategory 𝒜] [MonoidalClosed 𝒜] in
/-- Left multiplication by `p` is killed by the cokernel of the inclusion of its image. -/
theorem leftMul_comp_cokernel_π :
    leftMul C p ≫ cokernel.π (image.ι (leftMul C p)) = 0 := by
  rw [← image.fac_assoc, cokernel.condition, comp_zero]

/-- The multiplication of `C`, restricted along the inclusion of the image of left
multiplication by `p`, is killed by the cokernel of that inclusion. This is the hypothesis
`CategoryTheory.Mon.imageActionRight` needs. -/
theorem ι_whiskerRight_mul_comp_cokernel_π :
    ((image.ι (leftMul C p) ▷ C.X) ≫ μ) ≫ cokernel.π (image.ι (leftMul C p)) = 0 := by
  have := epi_whiskerRight C.X (factorThruImage (leftMul C p))
  rw [← cancel_epi (factorThruImage (leftMul C p) ▷ C.X), comp_zero]
  simp only [Category.assoc]
  rw [← comp_whiskerRight_assoc, image.fac, ← mul_comp_leftMul_assoc,
    leftMul_comp_cokernel_π, comp_zero]

/-- The right action of the monoid object `C` on the image of left multiplication by the point
`p`, i.e. on the subobject `p * C` of `C.X`: the multiplication of `C` factored through the
inclusion of the image. -/
noncomputable def imageActionRight : image (leftMul C p) ⊗ C.X ⟶ image (leftMul C p) :=
  Abelian.monoLift (image.ι (leftMul C p)) ((image.ι (leftMul C p) ▷ C.X) ≫ μ)
    (ι_whiskerRight_mul_comp_cokernel_π C p)

/-- The action of `C` on `p * C` is the restriction of the multiplication of `C`. As the
inclusion of the image is a monomorphism, this characterises the action. -/
@[reassoc (attr := simp)]
theorem imageActionRight_comp_ι : imageActionRight C p ≫ image.ι (leftMul C p)
    = (image.ι (leftMul C p) ▷ C.X) ≫ μ :=
  Abelian.monoLift_comp _ _ _

/-- **The unit axiom of the right action of `C` on `p * C`.** -/
theorem imageActionRight_one :
    (ρ_ (image (leftMul C p))).inv ≫ (image (leftMul C p) ◁ η[C.X]) ≫ imageActionRight C p
      = 𝟙 (image (leftMul C p)) := by
  rw [← cancel_mono (image.ι (leftMul C p))]
  simp only [Category.assoc, imageActionRight_comp_ι, Category.id_comp]
  rw [whisker_exchange_assoc, MonObj.mul_one]
  simp

/-- The unit axiom of the right action of `C` on `p * C`, with the unitor on the right. -/
@[reassoc (attr := simp)]
theorem whiskerLeft_one_imageActionRight :
    (image (leftMul C p) ◁ η[C.X]) ≫ imageActionRight C p
      = (ρ_ (image (leftMul C p))).hom := by
  have h := imageActionRight_one C p
  rw [Iso.inv_comp_eq] at h
  simpa using h

/-- **The associativity axiom of the right action of `C` on `p * C`.** -/
theorem imageActionRight_mul :
    (image (leftMul C p) ◁ μ[C.X]) ≫ imageActionRight C p
      = (α_ (image (leftMul C p)) C.X C.X).inv ≫ (imageActionRight C p ▷ C.X)
          ≫ imageActionRight C p := by
  rw [← cancel_mono (image.ι (leftMul C p))]
  simp only [Category.assoc, imageActionRight_comp_ι, ← comp_whiskerRight_assoc,
    imageActionRight_comp_ι]
  rw [whisker_exchange_assoc, MonObj.mul_assoc_flip, associator_inv_naturality_left_assoc]
  simp [comp_whiskerRight]

/-- The representation of `C` on the image of left multiplication by `p`, as a morphism of `𝒜`:
the right action of `C` on `p * C`, curried. -/
noncomputable def imageRepHom : C.X ⟶ (ihom (image (leftMul C p))).obj (image (leftMul C p)) :=
  curry (imageActionRight C p)

/-- **The representation of `C` on `p * C` is a morphism of monoid objects** into the internal
endomorphism monoid: the unit and associativity axioms of the right action are exactly the two
laws, after uncurrying. -/
instance isMonHom_imageRepHom : IsMonHom (imageRepHom C p) where
  one_hom := by
    change η[C.X] ≫ _ = MonoidalClosed.id (image (leftMul C p))
    apply uncurry_injective
    rw [uncurry_natural_left, imageRepHom, uncurry_curry, MonoidalClosed.id_eq, uncurry_curry,
      whiskerLeft_one_imageActionRight]
  mul_hom := by
    change μ[C.X] ≫ _ = _ ≫ MonoidalClosed.comp _ _ _
    apply uncurry_injective
    rw [uncurry_natural_left, imageRepHom, uncurry_curry, uncurry_natural_left,
      MonoidalClosed.comp_eq, uncurry_curry, whiskerLeft_tensorHom_compTranspose,
      imageActionRight_mul, uncurry_curry]

/-- **The morphism of monoid objects from `C` to the internal endomorphism monoid of the image
of left multiplication by `p`.** -/
noncomputable def imageRep : C ⟶ MonoidalClosed.internalEnd (image (leftMul C p)) :=
  Mon.Hom.mk' (imageRepHom C p) (IsMonHom.one_hom _) (IsMonHom.mul_hom _)

/-- The underlying morphism of `CategoryTheory.Mon.imageRep` is the curried right action. -/
@[simp]
theorem imageRep_hom : (imageRep C p).hom = curry (imageActionRight C p) := rfl

variable {C} {D : Mon 𝒜} (e : C ≅ D) {p} {q : 𝟙_ 𝒜 ⟶ D.X} (h : p ≫ e.hom.hom = q)

/-- **An isomorphism of monoid objects carrying one point to the other carries the image of
left multiplication to the image of left multiplication.** -/
noncomputable def imageIsoLeft : image (leftMul C p) ≅ image (leftMul D q) :=
  imageIsoOfConj _ (leftMul_conj e h)

omit [BraidedCategory 𝒜] [MonoidalClosed 𝒜] in
/-- The comparison of the images of left multiplication is compatible with the two image
inclusions. -/
@[reassoc (attr := simp)]
theorem imageIsoLeft_hom_comp_ι :
    (imageIsoLeft e h).hom ≫ image.ι (leftMul D q) = image.ι (leftMul C p) ≫ e.hom.hom :=
  imageHomOfConj_comp_ι (homIso e) (leftMul_conj e h)

/-- **The comparison of the images of left multiplication intertwines the two right actions.** -/
theorem imageActionRight_comp_imageIsoLeft_hom :
    imageActionRight C p ≫ (imageIsoLeft e h).hom
      = ((imageIsoLeft e h).hom ⊗ₘ e.hom.hom) ≫ imageActionRight D q := by
  rw [← cancel_mono (image.ι (leftMul D q))]
  simp only [Category.assoc, imageIsoLeft_hom_comp_ι, imageActionRight_comp_ι,
    imageActionRight_comp_ι_assoc, ← tensorHom_id, IsMonHom.mul_hom,
    tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp]

/-- **An isomorphism of monoid objects carrying one point to the other carries the induced
representation to the induced representation**, conjugated by the comparison of the images. -/
theorem imageRep_naturality :
    e.hom ≫ imageRep D q = imageRep C p ≫ (internalEndCongr (imageIsoLeft e h)).hom := by
  apply Mon.Hom.ext'
  change e.hom.hom ≫ imageRepHom D q = imageRepHom C p ≫ internalEndCongrHom (imageIsoLeft e h)
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left, imageRepHom, imageRepHom, uncurry_curry,
    uncurry_internalEndCongrHom, whisker_exchange_assoc,
    whiskerLeft_curry_ihom_ev_app_assoc, imageActionRight_comp_imageIsoLeft_hom, tensorHom_def]
  simp only [Category.assoc, ← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight,
    Category.id_comp]

end LeftMul

end CategoryTheory.Mon
