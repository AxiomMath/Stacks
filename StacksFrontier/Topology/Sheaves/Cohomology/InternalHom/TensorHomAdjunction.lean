module

public import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.InternalHomComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.ComplexesOfModules

/-!
# Composition for internal Hom complexes of modules on a ringed space

Let `(X, O_X)` be a ringed space and let `K`, `L`, `M` be cochain complexes of `O_X`-modules.
Currying identifies the iterated internal Hom complex `SheafHom•(K, SheafHom•(L, M))` with the
internal Hom complex `SheafHom•(Tot(K ⊗_{O_X} L), M)` out of the total tensor complex, and the
identification is functorial in all three complexes. This is [Stacks, Tag 0A8M]; the source
proves it "in exactly the same way" as its module-level counterpart [Stacks, Tag 0A5Y], which
is `StacksFrontier/Homology/HomComplex/Currying.lean`.

The route taken here is not a second copy of that computation. `Mod(O)` is symmetric monoidal
closed for the sheafified tensor product
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/MonoidalSheafTensor.lean`), and complexes in a
symmetric monoidal closed additive category are again symmetric monoidal closed, with internal
hom the internal Hom complex
(`StacksFrontier/Algebra/Homology/InternalHomComplex.lean` and
`StacksFrontier/Algebra/Homology/KoszulSymmetric.lean`).  So the Koszul-sign bookkeeping is
already done, and what is left is the currying isomorphism
`Hom(X, Hom(Y, Z)) ≅ Hom(X ⊗ Y, Z)` of internal homs in an arbitrary *braided* monoidal closed
category, together with its naturality — which is the first half of this file and is proved for
such a category, not for complexes of sheaves.

## Main definitions

* `CategoryTheory.MonoidalClosed.preIso`: an isomorphism in the contravariant variable induces
  an isomorphism of internal Hom functors.
* `CategoryTheory.MonoidalClosed.ihomTensorIso`: the currying isomorphism
  `Hom(X, Hom(Y, Z)) ≅ Hom(X ⊗ Y, Z)` in a braided monoidal closed category.
* `CategoryTheory.MonoidalClosed.ihomMap`: the map of internal homs induced by a morphism in
  each variable.
* `Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplex` and
  `Stacks.Cohomology.SheafHomComplexCurrying.tensorComplex`: the internal Hom complex
  `SheafHom•(K, L)` and the total tensor complex `Tot(K ⊗_O L)` of complexes of `O`-modules on a
  ringed site.
* `Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplexMap`: the induced map of internal Hom
  complexes.
* `Stacks.Cohomology.SheafHomComplexCurrying.SheafHomTensorIsoConstruction`: the isomorphism of Tag
  0A8M on a ringed space
  together with its simultaneous functoriality, as a single datum.

## Main results

* `CategoryTheory.MonoidalClosed.ihomTensorIso_naturality_left`,
  `CategoryTheory.MonoidalClosed.ihomTensorIso_naturality_middle`,
  `CategoryTheory.MonoidalClosed.ihomTensorIso_naturality_right` and
  `CategoryTheory.MonoidalClosed.ihomTensorIso_naturality`: naturality of the currying
  isomorphism in each variable separately and in all three at once.
* `Stacks.Cohomology.SheafHomComplexCurrying.sheafHomTensorIso` and
  `Stacks.Cohomology.SheafHomComplexCurrying.sheafHomTensorIso_natural`: Tag 0A8M for
  a ringed site, and `Stacks.Cohomology.SheafHomComplexCurrying.sheafHomTensorIsoConstruction` for
    a ringed space.

## Implementation notes

`SheafHom•(K, L)` is `(ihom K).obj L` for the closed structure on `Comp(Mod(O))`, which
`sheafHomComplex_eq` records as `CochainComplex.internalHomComplex K L`: in degree `n` the
product over `p` of the internal Hom sheaves `SheafHom(K^p, L^(p + n))`, with the Hom-complex
differential. `Tot(K ⊗_O L)` is `Stacks.SheafOfModules.Tensor.tensorComplex`, the totalization of
  the
sheafified tensor product used by the K-flatness predicate of Tag 06Y9 and by Tag 06YM; it is
the monoidal product of `Comp(Mod(O))` on the nose, which is `tensorComplex_eq`. The tensor
product of a pair of morphisms is written as the tagged statement writes it, as the composite of the two
one-variable maps of `Stacks.SheafOfModules.Tensor.tensorComplex`.

The statement is proved for a ringed site and then specialized to a ringed space, which is
where Tag 0A8M is stated. Over the site `Opens X` the universe of the site and the universe of
the sections of `O_X` coincide, and instance search then has to solve `max ?u ?v =?= u` with
both unknown; so each instance of the ringed-space section is named and applied with its site
written out, rather than synthesized. None of them is an assumption: they are the same
instances as in the ringed-site section.

The closed and symmetric structures on `Comp(Mod(O))` are not global instances -- complexes
carry several of each, as recorded in `StacksFrontier/Algebra/Homology/InternalHomComplex.lean` --
so they are seated locally here. The `∀`-quantified graded-object hypotheses of the monoidal
structure are named rather than synthesized, because instance search solves them only in
applied form.

## References

* [The Stacks Project, Tag 0A8M](https://stacks.math.columbia.edu/tag/0A8M)
* [The Stacks Project, Tag 0A5Y](https://stacks.math.columbia.edu/tag/0A5Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe v u

namespace CategoryTheory.MonoidalClosed

variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [MonoidalClosed D]

/-- Precomposition with an isomorphism is an isomorphism of internal Hom functors. -/
def preIso {A B : D} (e : A ≅ B) : ihom B ≅ ihom A where
  hom := pre e.hom
  inv := pre e.inv
  hom_inv_id := by rw [← pre_map, e.inv_hom_id, pre_id]
  inv_hom_id := by rw [← pre_map, e.hom_inv_id, pre_id]

/-- The forward map of `preIso e` is precomposition with `e.hom`. -/
@[simp] lemma preIso_hom {A B : D} (e : A ≅ B) : (preIso e).hom = pre e.hom := rfl

variable [BraidedCategory D]

/-- **The internal currying isomorphism**
`Hom(X, Hom(Y, Z)) ≅ Hom(X ⊗ Y, Z)`. -/
def ihomTensorIso (X Y Z : D) : (ihom X).obj ((ihom Y).obj Z) ≅ (ihom (X ⊗ Y)).obj Z :=
  (ihomCurryIso Y X Z).symm ≪≫ (preIso (β_ X Y)).app Z

/-- The currying isomorphism is internal uncurrying followed by the braiding. -/
lemma ihomTensorIso_hom (X Y Z : D) :
    (ihomTensorIso X Y Z).hom =
      ihomUncurry Y X Z ≫ (pre (β_ X Y).hom).app Z := rfl

/-- **The currying isomorphism, uncurried**: braid, reassociate and evaluate twice.  This pins
the isomorphism down, and every naturality statement below is proved from it. -/
lemma uncurry_ihomTensorIso_hom (X Y Z : D) :
    uncurry (ihomTensorIso X Y Z).hom =
      (β_ X Y).hom ▷ ((ihom X).obj ((ihom Y).obj Z)) ≫ (α_ Y X _).hom ≫
        Y ◁ (ihom.ev X).app ((ihom Y).obj Z) ≫ (ihom.ev Y).app Z := by
  rw [ihomTensorIso_hom, uncurry_pre_app, uncurry_ihomUncurry]

/-- Uncurrying `a ≫ (ihomTensorIso X Y Z).hom`: braid, reassociate and evaluate twice on `a`. -/
private lemma uncurry_comp_ihomTensorIso_hom {X Y Z A : D} (a : A ⟶ (ihom X).obj ((ihom Y).obj Z)) :
    uncurry (a ≫ (ihomTensorIso X Y Z).hom) =
      (β_ X Y).hom ▷ A ≫ (α_ Y X A).hom ≫ Y ◁ (X ◁ a ≫ (ihom.ev X).app _) ≫ (ihom.ev Y).app Z := by
  rw [uncurry_natural_left, uncurry_ihomTensorIso_hom, whisker_exchange_assoc,
    associator_naturality_right_assoc, MonoidalCategory.whiskerLeft_comp_assoc]

/-- Naturality of the currying isomorphism in the covariant variable. -/
lemma ihomTensorIso_naturality_right (X Y : D) {Z Z' : D} (m : Z ⟶ Z') :
    (ihom X).map ((ihom Y).map m) ≫ (ihomTensorIso X Y Z').hom =
      (ihomTensorIso X Y Z).hom ≫ (ihom (X ⊗ Y)).map m := by
  apply uncurry_injective
  rw [uncurry_comp_ihomTensorIso_hom, uncurry_natural_right, uncurry_ihomTensorIso_hom,
    ihom.ev_naturality, MonoidalCategory.whiskerLeft_comp_assoc, ihom.ev_naturality]
  simp

/-- Naturality of the currying isomorphism in the second contravariant variable. -/
@[reassoc]
lemma ihomTensorIso_naturality_middle (X : D) {Y Y' : D} (l : Y' ⟶ Y) (Z : D) :
    (ihom X).map ((pre l).app Z) ≫ (ihomTensorIso X Y' Z).hom =
      (ihomTensorIso X Y Z).hom ≫ (pre (X ◁ l)).app Z := by
  apply uncurry_injective
  rw [uncurry_comp_ihomTensorIso_hom, uncurry_pre_app, uncurry_ihomTensorIso_hom,
    ihom.ev_naturality, MonoidalCategory.whiskerLeft_comp_assoc, id_tensor_pre_app_comp_ev,
    ← comp_whiskerRight_assoc, BraidedCategory.braiding_naturality_right,
    comp_whiskerRight_assoc, associator_naturality_left_assoc]
  have h : Y' ◁ (ihom.ev X).app ((ihom Y).obj Z) ≫ l ▷ (ihom Y).obj Z =
      l ▷ (X ⊗ (ihom X).obj ((ihom Y).obj Z)) ≫ Y ◁ (ihom.ev X).app ((ihom Y).obj Z) :=
    whisker_exchange _ _
  rw [reassoc_of% h]

/-- Naturality of the currying isomorphism in the first contravariant variable. -/
@[reassoc]
lemma ihomTensorIso_naturality_left {X X' : D} (k : X' ⟶ X) (Y Z : D) :
    (pre k).app ((ihom Y).obj Z) ≫ (ihomTensorIso X' Y Z).hom =
      (ihomTensorIso X Y Z).hom ≫ (pre (k ▷ Y)).app Z := by
  apply uncurry_injective
  rw [uncurry_comp_ihomTensorIso_hom, uncurry_pre_app, uncurry_ihomTensorIso_hom,
    id_tensor_pre_app_comp_ev, MonoidalCategory.whiskerLeft_comp_assoc,
    ← comp_whiskerRight_assoc, BraidedCategory.braiding_naturality_left,
    comp_whiskerRight_assoc, associator_naturality_middle_assoc]

/-- The map of internal Homs induced by a morphism `g` in the contravariant variable and a
morphism `f` in the covariant variable. -/
def ihomMap {X X' Z Z' : D} (g : X' ⟶ X) (f : Z ⟶ Z') :
    (ihom X).obj Z ⟶ (ihom X').obj Z' :=
  (pre g).app Z ≫ (ihom X').map f

/-- **The currying isomorphism is natural simultaneously in all three variables.** -/
lemma ihomTensorIso_naturality {X X' Y Y' Z Z' : D} (k : X' ⟶ X) (l : Y' ⟶ Y) (m : Z ⟶ Z') :
    ihomMap k (ihomMap l m) ≫ (ihomTensorIso X' Y' Z').hom =
      (ihomTensorIso X Y Z).hom ≫ ihomMap (k ▷ Y' ≫ X ◁ l) m := by
  simp only [ihomMap, Functor.map_comp, Category.assoc]
  rw [ihomTensorIso_naturality_right, ihomTensorIso_naturality_middle_assoc,
    ihomTensorIso_naturality_left_assoc, pre_app_comp_assoc, whisker_exchange]

end CategoryTheory.MonoidalClosed

namespace Stacks.Cohomology.SheafHomComplexCurrying

open CategoryTheory.MonoidalClosed

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

/-- `Mod(O)`, the category of `O`-modules on the ringed site `(C, O)`. -/
abbrev Mod := SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)

/-- `Comp(Mod(O))`, the category of cochain complexes of `O`-modules. -/
abbrev Complexes := CochainComplex (Mod R) ℤ

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor

/-- Sheafification of abelian-group-valued presheaves on `J` exists. -/
local instance : HasWeakSheafify J AddCommGrpCat.{max u v} := inferInstance
/-- On `J`, the weak equivalences of abelian presheaves are the locally bijective maps. -/
local instance : J.WEqualsLocallyBijective AddCommGrpCat.{max u v} := inferInstance
/-- The monoidal structure on `Mod(O)` whose tensor product is the sheafified `⊗_O`. -/
local instance : MonoidalCategory (Mod R) := SheafOfModules.monoidalCategorySheafTensor R
/-- `Mod(O)` has colimits of every shape whose objects and morphisms live in `Type`. -/
local instance : HasColimitsOfSize.{0, 0} (Mod R) := inferInstance

/-- The graded tensor products of `O`-modules exist. -/
local instance hasTensor : ∀ (X₁ X₂ : GradedObject ℤ (Mod R)), GradedObject.HasTensor X₁ X₂ :=
  fun _ _ => inferInstance

/-- The left-bracketed triple graded tensor products of `O`-modules are good. -/
local instance hasGoodTensor₁₂Tensor : ∀ (X₁ X₂ X₃ : GradedObject ℤ (Mod R)),
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := fun _ _ _ => inferInstance

/-- The right-bracketed triple graded tensor products of `O`-modules are good. -/
local instance hasGoodTensorTensor₂₃ : ∀ (X₁ X₂ X₃ : GradedObject ℤ (Mod R)),
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := fun _ _ _ => inferInstance

/-- A morphism out of a fourfold graded tensor product of `O`-modules is determined on the
summands. -/
local instance hasTensor₄ObjExt : ∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (Mod R)),
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := fun _ _ _ _ => inferInstance

/-- The total complexes of the tensor double complexes of complexes of `O`-modules exist. -/
local instance hasMapBifunctor :
    letI := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, v, max u v, max u v, max u v}
      (C := C) (J := J) R
    ∀ (K L : Complexes R),
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} R)
        (ComplexShape.up ℤ) :=
  @Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor.{u, v, max u v, max u v, max u v}
    C inferInstance J R
    (inferInstance : HasWeakSheafify J AddCommGrpCat.{max u v})
    (inferInstance : J.WEqualsLocallyBijective AddCommGrpCat.{max u v})
    (inferInstance : HasBinaryBiproducts (Mod R))

attribute [local instance] CochainComplex.monoidalClosed CochainComplex.symmetricCategory

/-- `Tot(K ⊗_O L)`, the total complex of the tensor double complex. -/
abbrev tensorComplex (K L : Complexes R) : Complexes R :=
  haveI := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, v, max u v, max u v, max u v}
    (C := C) (J := J) R
  ((Stacks.SheafOfModules.Tensor.tensorComplex.{u, v, max u v} R).obj K).obj L

/-- `SheafHom•(K, L)`, the internal Hom complex of two complexes of `O`-modules. -/
abbrev sheafHomComplex (K L : Complexes R) : Complexes R := (ihom K).obj L

/-- The internal Hom complex is the one built degreewise out of the internal Hom sheaves: in
degree `n` it is `∏_p SheafHom(K^p, L^(p + n))`, with the Hom-complex differential. -/
lemma sheafHomComplex_eq (K L : Complexes R) :
    sheafHomComplex R K L = CochainComplex.internalHomComplex K L := rfl

/-- **The degreewise description of `SheafHom•(K, L)`**: its degree-`n` term is the product
over `p` of the internal Hom sheaves `SheafHom(K^p, L^(p + n))`. -/
lemma sheafHomComplex_X (K L : Complexes R) (n : ℤ) :
    (sheafHomComplex R K L).X n =
      ∏ᶜ (fun p : ℤ => (ihom (K.X p)).obj (L.X (p + n))) := rfl

/-- `Tot(K ⊗_O L)` is the monoidal product of `Comp(Mod(O))`. -/
lemma tensorComplex_eq (K L : Complexes R) : tensorComplex R K L = K ⊗ L := rfl

/-- The map `SheafHom•(K, L) ⟶ SheafHom•(K', L')` induced by `g : K' ⟶ K` and `f : L ⟶ L'`. -/
def sheafHomComplexMap {K K' L L' : Complexes R} (g : K' ⟶ K) (f : L ⟶ L') :
    sheafHomComplex R K L ⟶ sheafHomComplex R K' L' :=
  ihomMap g f

/-- **Stacks 0A8M.** The canonical isomorphism
`SheafHom•(K, SheafHom•(L, M)) ≅ SheafHom•(Tot(K ⊗ L), M)`. -/
def sheafHomTensorIso (K L M : Complexes R) :
    sheafHomComplex R K (sheafHomComplex R L M) ≅
      sheafHomComplex R (tensorComplex R K L) M :=
  ihomTensorIso K L M

/-- **Stacks 0A8M, functoriality.**  The isomorphism is natural simultaneously in all three
complexes. -/
theorem sheafHomTensorIso_natural {K K' L L' M M' : Complexes R}
    (k : K' ⟶ K) (l : L' ⟶ L) (m : M ⟶ M') :
    letI := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, v, max u v, max u v, max u v}
      (C := C) (J := J) R
    sheafHomComplexMap R k (sheafHomComplexMap R l m) ≫ (sheafHomTensorIso R K' L' M').hom =
      (sheafHomTensorIso R K L M).hom ≫
        sheafHomComplexMap R
          (((Stacks.SheafOfModules.Tensor.tensorComplex.{u, v, max u v} R).map k).app L' ≫
            ((Stacks.SheafOfModules.Tensor.tensorComplex.{u, v, max u v} R).obj K).map l) m := by
  let := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, v, max u v, max u v, max u v}
    (C := C) (J := J) R
  exact ihomTensorIso_naturality k l m

section RingedSpace

open TopologicalSpace

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive

/-- The monoidal structure on `Mod(O_X)` whose tensor product is `⊗_{O_X}`, named for the same
reason. -/
local instance monoidalSpace : MonoidalCategory (Mod Rc) :=
  SheafOfModules.monoidalCategorySheafTensor (J := Opens.grothendieckTopology X) Rc

/-- `⊗_{O_X}` is symmetric, named for the same reason. -/
local instance symmetricSpace : SymmetricCategory (Mod Rc) :=
  SheafOfModules.symmetricCategorySheafTensor (J := Opens.grothendieckTopology X) Rc

/-- `⊗_{O_X}` is bilinear on morphisms, named for the same reason. -/
local instance monoidalPreadditiveSpace : MonoidalPreadditive (Mod Rc) :=
  SheafOfModules.monoidalPreadditiveSheafTensor (J := Opens.grothendieckTopology X) Rc

/-- `Mod(O_X)` is monoidal closed, named for the same reason. -/
local instance monoidalClosedSpace : MonoidalClosed (Mod Rc) :=
  SheafOfModules.monoidalClosedSheafTensor (J := Opens.grothendieckTopology X) Rc

/-- `- ⊗_{O_X} 𝒢` commutes with colimits, named for the same reason. -/
local instance preservesColimitTensorRightSpace {T : Type*} [Category T] (F : T ⥤ Mod Rc)
    (N : Mod Rc) : PreservesColimit F (tensorRight N) :=
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
    (J := Opens.grothendieckTopology X) Rc F N

/-- The total complexes of the tensor double complexes exist, named for the same reason. -/
local instance hasMapBifunctorSpace : ∀ (K L : Complexes Rc),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Rc) (ComplexShape.up ℤ) :=
  hasMapBifunctor (J := Opens.grothendieckTopology X) Rc

/-- The graded tensor products exist, named for the same reason. -/
local instance hasTensorSpace : ∀ (A B : GradedObject ℤ (Mod Rc)),
    GradedObject.HasTensor A B :=
  hasTensor (J := Opens.grothendieckTopology X) Rc

/-- The left-bracketed triple graded tensor products are good, named for the same reason. -/
local instance hasGoodTensor₁₂TensorSpace : ∀ (A B D : GradedObject ℤ (Mod Rc)),
    GradedObject.HasGoodTensor₁₂Tensor A B D :=
  hasGoodTensor₁₂Tensor (J := Opens.grothendieckTopology X) Rc

/-- The right-bracketed triple graded tensor products are good, named for the same reason. -/
local instance hasGoodTensorTensor₂₃Space : ∀ (A B D : GradedObject ℤ (Mod Rc)),
    GradedObject.HasGoodTensorTensor₂₃ A B D :=
  hasGoodTensorTensor₂₃ (J := Opens.grothendieckTopology X) Rc

/-- A morphism out of a fourfold graded tensor product is determined on the summands, named for
the same reason. -/
local instance hasTensor₄ObjExtSpace : ∀ (A B D E : GradedObject ℤ (Mod Rc)),
    GradedObject.HasTensor₄ObjExt A B D E :=
  hasTensor₄ObjExt (J := Opens.grothendieckTopology X) Rc

/-- `Comp(Mod(O_X))`, the complexes of `O_X`-modules on a ringed space `(X, O_X)`. -/
abbrev SpaceComplexes := CochainComplex (SheafOfModules.{u} (structureSheaf Rc)) ℤ

/-- The tensor--internal-Hom isomorphism on a ringed space, together with its functoriality in
the two contravariant variables and the covariant target. -/
structure SheafHomTensorIsoConstruction where
  /-- The canonical currying isomorphism of complexes. -/
  iso (K L M : SpaceComplexes Rc) :
    sheafHomComplex Rc K (sheafHomComplex Rc L M) ≅
      sheafHomComplex Rc (tensorComplex Rc K L) M
  /-- The currying isomorphism is natural simultaneously in all three entries. -/
  natural {K K' L L' M M' : SpaceComplexes Rc}
      (k : K' ⟶ K) (l : L' ⟶ L) (m : M ⟶ M') :
    sheafHomComplexMap Rc k (sheafHomComplexMap Rc l m) ≫ (iso K' L' M').hom =
      (iso K L M).hom ≫
        sheafHomComplexMap Rc
          (((Stacks.SheafOfModules.Tensor.tensorComplex Rc).map k).app L' ≫
            ((Stacks.SheafOfModules.Tensor.tensorComplex Rc).obj K).map l) m

/-- **Stacks 0A8M.** For complexes `K`, `L`, `M` of `O_X`-modules on a ringed space there is an
isomorphism `SheafHom•(K, SheafHom•(L, M)) ≅ SheafHom•(Tot(K ⊗_{O_X} L), M)` of complexes of
`O_X`-modules, functorial in `K`, `L` and `M`. -/
@[stacks 0A8M]
def sheafHomTensorIsoConstruction : SheafHomTensorIsoConstruction Rc where
  iso K L M := sheafHomTensorIso Rc K L M
  natural k l m := sheafHomTensorIso_natural Rc k l m

end RingedSpace

end Stacks.Cohomology.SheafHomComplexCurrying

end

end
