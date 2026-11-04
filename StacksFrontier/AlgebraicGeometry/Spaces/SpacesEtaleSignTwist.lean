module

public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleLocalization
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels

/-!
# The rank one twist attached to a character of a free finite group action

Let `W` be an algebraic space over a scheme `S` carrying a free action of a finite group `G`,
let `U = W/G` be the quotient and let `χ : G → {+1, -1}` be a character.  Stacks 0727 attaches
to these data a rank one locally free sheaf of `ℤ`-modules `ℤ(χ)` on `U_étale` whose tensor
product with an abelian sheaf `F` computes the `χ`-semi-invariant sections of `F` over `W`.
Stacks 072A is the statement that tensoring with `ℤ(χ)` preserves quasi-coherence.

`AlgebraicGeometry.Space.SignTwistSetup` packages the data and conclusions of Stacks 0727 as
hypotheses, which is the exact form in which Stacks 072A uses them: the Stacks statement of
072A reads "with `S`, `W`, `G`, `U`, `χ` as in Lemma 0727".  Quasi-coherence of the twist is
then proved from that package.

## Main definitions

* `AlgebraicGeometry.Space.characterSections` is the subgroup of the sections of an abelian
  sheaf over `W` that transform according to `χ`.
* `AlgebraicGeometry.Space.IsFreeOfRankOneOn` and
  `AlgebraicGeometry.Space.IsLocallyFreeOfRankOne` are freeness of rank one of an abelian
  sheaf on an object of the spaces-étale site, and local freeness of rank one.
* `AlgebraicGeometry.Space.SignTwistSetup` bundles a free action of a finite group on an
  algebraic space, its étale quotient morphism, a character, and the rank one twist attached
  to the character.
* `AlgebraicGeometry.Space.SignTwistSetup.twist` is the `𝒪_U`-module `F ⊗_ℤ ℤ(χ)`.
* `Stacks.SheafOfModules.tensorAbelianModule` is the tensor product over `ℤ` of a sheaf of
  modules with a presheaf of abelian groups, with the structure sheaf acting on the left-hand
  factor.
* `AddCommGrpCat.presheafTensorInsert` inserts a global integral section into the right-hand
  factor of an objectwise tensor product over `ℤ`.
* `AlgebraicGeometry.Space.splitDoubleCover` is the coproduct `X ⊔ X` of two copies of an
  algebraic space in its own spaces-étale site, with the swap of its two summands as an
  action of the two-element group `ℤˣ`.
* `AlgebraicGeometry.Space.signTwistSetupOfSwap` is an inhabitant of
  `AlgebraicGeometry.Space.SignTwistSetup` for the nontrivial group `ℤˣ`.

## Main results

* `AlgebraicGeometry.Space.SignTwistSetup.isQuasicoherentOnSite_twist` is **Stacks 072A**: if
  `F` is a quasi-coherent `𝒪_U`-module, so is `F ⊗_ℤ ℤ(χ)`.
* `Stacks.SheafOfModules.isQuasicoherentOnSite_of_locally_iso`: a sheaf of modules locally
  isomorphic to a quasi-coherent one is quasi-coherent.
* `Stacks.SheafOfModules.nonempty_over_iso_of_tensor_generator`: on a slice on which the
  right-hand factor of the tensor product has a trivializing global section, the tensor
  product is isomorphic to the left-hand factor.
* `AlgebraicGeometry.Space.isFreeOnNonemptyPoints_splitDoubleCover`: the swap of the two
  summands of `X ⊔ X` is free on the points over every test object whose underlying scheme is
  nonempty.
* `AlgebraicGeometry.Space.SpacesEtale.existsUnique_section_of_isColimit_cofan`: a section of
  an abelian sheaf over a coproduct of the spaces-étale site is the same thing as an arbitrary
  family of sections over the two members.
* `AlgebraicGeometry.Space.SpacesEtale.abelianSheafTensorConstantIso` and
  `AlgebraicGeometry.Space.constantSheafOverIso`: tensoring over `ℤ` with the constant sheaf
  `ℤ` changes nothing, and the constant sheaf restricts to the constant sheaf on a slice;
  hence `AlgebraicGeometry.Space.isLocallyFreeOfRankOne_constantSheaf`.

## Implementation notes

The twist of Stacks 0727 lives on the spaces-étale site of `U`, because `W` itself is an
algebraic space étale over `U` and so is an object of that site but not of the small étale
site; the `χ`-semi-invariant sections over `W` are the sections of an abelian sheaf at that
object.  Quasi-coherent modules, on the other hand, live on the small étale ringed site of
Stacks 03G9.  `AlgebraicGeometry.Space.SignTwistSetup.smallEtaleSheaf` restricts the twist
along the comparison functor of Stacks 03G1, and the tensor product is formed there.

Freeness of the action is `AlgebraicGeometry.Space.IsFreeOnNonemptyPoints`, freeness on the
points over the test objects whose underlying scheme is nonempty.  Asking instead for a
cancellative action over *every* test object forces `G` to be trivial, by
`AlgebraicGeometry.Space.forall_isCancelSMul_iff_subsingleton`, and would make the whole
package unsatisfiable for a nontrivial group.

Since Stacks 072A is universally quantified over the package, the package has to be shown
inhabited for a nontrivial group, or the statement would be vacuous.
`AlgebraicGeometry.Space.signTwistSetupOfSwap` does that with the split double cover
`X ⊔ X` of an algebraic space `X` over `S`: the group is `ℤˣ` acting by the swap of the two
summands, the quotient is `X` with the fold map, the character is the identity of `ℤˣ` — the
sign character of the swap — and the twist `ℤ(χ)` is the constant sheaf `ℤ`, which is what
the twist of a *split* cover is.  The `χ`-semi-invariant sections of an abelian sheaf `F` over
`X ⊔ X` are then the pairs `(a, -a)`, that is the global sections of `F`, matching
`H⁰(X, F ⊗_ℤ ℤ)`.

The mathematics of Stacks 072A is local: the `𝒪_U`-module structure on `F ⊗_ℤ ℤ(χ)` is the
one in which `𝒪_U` acts on the left-hand factor, and on a covering of `U` trivializing
`ℤ(χ)` the twist is isomorphic to `F` itself.  The isomorphism is produced by inserting the
trivializing global section into the right-hand factor of the tensor product; it is inverted
by sheafification because the section is, and a morphism of sheaves of modules inverted by
sheafification is an isomorphism.

## References

* [Stacks Project, Tag 072A](https://stacks.math.columbia.edu/tag/072A)
* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Enriched.FunctorCategory
open scoped TensorProduct CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

universe u v u₁ u₂ r

/-! ### Inserting a global integral section into an objectwise tensor product -/

namespace AddCommGrpCat

/-- Scalar multiplication of an abelian group by a universe-lifted integer, as a `ℤ`-bilinear
map. -/
def uliftIntSmul (A : Type (u + 1)) [AddCommGroup A] :
    A →ₗ[ℤ] (ULift.{u + 1} ℤ →ₗ[ℤ] A) where
  toFun a := (ULift.moduleEquiv : ULift.{u + 1} ℤ ≃ₗ[ℤ] ℤ).toLinearMap.smulRight a
  map_add' a b := by ext y; exact smul_add _ a b
  map_smul' r a := by ext y; exact smul_comm _ r a

/-- An abelian group tensored over `ℤ` with a universe lift of the integers on the right is
the group itself: the map sending `a ⊗ n` to `n • a`. -/
def tensorULiftIntRid (A : Type (u + 1)) [AddCommGroup A] :
    TensorProduct ℤ A (ULift.{u + 1} ℤ) →+ A :=
  (TensorProduct.lift (uliftIntSmul A)).toAddMonoidHom

/-- The identification of an abelian group tensored with the integers on a pure tensor. -/
@[simp]
lemma tensorULiftIntRid_tmul (A : Type (u + 1)) [AddCommGroup A] (a : A)
    (y : ULift.{u + 1} ℤ) : tensorULiftIntRid A (a ⊗ₜ[ℤ] y) = y.down • a := rfl

/-- The objectwise tensor product over `ℤ` of a presheaf of abelian groups with the constant
presheaf `ℤ`, at a single object: tensoring with the integers changes nothing. -/
def presheafTensorUnitApp {C : Type*} [Category C] (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (V : Cᵒᵖ) :
    (presheafTensor F ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).obj V ≅
      F.obj V where
  hom := AddCommGrpCat.ofHom
    { toFun := tensorULiftIntRid (F.obj V)
      map_zero' := by exact map_zero _
      map_add' := fun x y => map_add _ x y }
  inv := AddCommGrpCat.ofHom
    { toFun := fun x => x ⊗ₜ[ℤ] (ULift.up (1 : ℤ))
      map_zero' := TensorProduct.zero_tmul _ _
      map_add' := fun x y => TensorProduct.add_tmul _ _ _ }
  hom_inv_id := by
    ext z
    induction z using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | add x y hx hy =>
        exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
    | tmul x y =>
        have hy : y.down • (ULift.up (1 : ℤ) : ULift.{u + 1} ℤ) = y := by
          apply ULift.ext
          simp
        change (y.down • x) ⊗ₜ[ℤ] (ULift.up (1 : ℤ)) = x ⊗ₜ[ℤ] y
        rw [TensorProduct.smul_tmul, hy]
  inv_hom_id := by
    ext x
    change (1 : ℤ) • x = x
    rw [one_smul]

/-- The inverse of the identification with the tensor unit tensors with the integer `1`. -/
@[simp]
lemma presheafTensorUnitApp_inv_apply {C : Type*} [Category C] (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (V : Cᵒᵖ) (x : F.obj V) :
    (presheafTensorUnitApp F V).inv x = x ⊗ₜ[ℤ] (ULift.up (1 : ℤ)) := rfl

/-- The objectwise tensor product over `ℤ` of a presheaf of abelian groups with the constant
presheaf `ℤ` is the presheaf itself. -/
def presheafTensorUnitIso {C : Type*} [Category C] (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    presheafTensor F ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≅ F :=
  NatIso.ofComponents (presheafTensorUnitApp F) (by
    intro V W f
    ext z
    induction z using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | add x y hx hy =>
        exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
    | tmul x y =>
        change y.down • F.map f x = F.map f (y.down • x)
        exact (map_zsmul (F.map f).hom _ _).symm)

/-- Insert a global section of `L` as the right-hand factor of the objectwise tensor product
over `ℤ`: the map sending `x` to `x ⊗ s`. -/
def presheafTensorInsert {C : Type*} [Category C] (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    {L : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    (s : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ L) :
    F ⟶ presheafTensor F L where
  app V := AddCommGrpCat.ofHom
    { toFun := fun x => x ⊗ₜ[ℤ] s.app V (ULift.up 1)
      map_zero' := TensorProduct.zero_tmul _ _
      map_add' := fun x y => TensorProduct.add_tmul _ _ _ }
  naturality V W f := by
    ext x
    have hs : s.app W (ULift.up (1 : ℤ)) = L.map f (s.app V (ULift.up 1)) :=
      congrArg (fun k => (AddCommGrpCat.Hom.hom k) (ULift.up (1 : ℤ))) (s.naturality f)
    change (F.map f x) ⊗ₜ[ℤ] s.app W (ULift.up (1 : ℤ)) =
      TensorProduct.map (F.map f).hom.toIntLinearMap (L.map f).hom.toIntLinearMap
        (x ⊗ₜ[ℤ] s.app V (ULift.up 1))
    rw [TensorProduct.map_tmul, hs]
    rfl

/-- Inserting a global section tensors with its value at the object. -/
@[simp]
lemma presheafTensorInsert_app {C : Type*} [Category C] (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    {L : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    (s : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ L)
    (V : Cᵒᵖ) (x : F.obj V) :
    (presheafTensorInsert F s).app V x = x ⊗ₜ[ℤ] s.app V (ULift.up 1) := rfl

/-- Inserting a global section is the objectwise tensor product of the section with an
identity, read through the identification of the constant presheaf `ℤ` with a tensor unit. -/
lemma presheafTensorInsert_eq {C : Type*} [Category C] (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    {L : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    (s : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ L) :
    presheafTensorInsert F s = (presheafTensorUnitIso F).inv ≫ presheafTensorMap (𝟙 F) s := by
  ext V x
  show x ⊗ₜ[ℤ] s.app V (ULift.up 1) =
    (presheafTensorMap (𝟙 F) s).app V ((presheafTensorUnitApp F V).inv x)
  rw [presheafTensorUnitApp_inv_apply, presheafTensorMap_app_tmul]
  rfl

/-- Inserting a global integral section which sheafification inverts gives a morphism which
sheafification inverts: the insertion is the objectwise tensor product of the section with an
identity, up to the isomorphism identifying the constant presheaf `ℤ` with a tensor unit. -/
theorem presheafTensorInsert_mem {C : Type u₁} [Category.{u₂} C] [UnivLE.{max u₁ u₂, u + 1}]
    (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    {L : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    (s : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ L) (hs : J.W s) :
    J.W (presheafTensorInsert F s) := by
  let : MonoidalCategory AddCommGrpCat.{u + 1} := monoidalCategory.{u + 1}
  let : (uliftIntEquivalence.{u + 1}).inverse.Monoidal := by
    show (Monoidal.equivalenceTransported (uliftIntEquivalence.{u + 1})).inverse.Monoidal
    infer_instance
  let : (uliftIntEquivalence.{u + 1}).functor.Monoidal := by
    show (Monoidal.equivalenceTransported (uliftIntEquivalence.{u + 1})).functor.Monoidal
    infer_instance
  let : BraidedCategory AddCommGrpCat.{u + 1} := by
    show BraidedCategory (Monoidal.Transported (uliftIntEquivalence.{u + 1}))
    infer_instance
  let : MonoidalClosed AddCommGrpCat.{u + 1} :=
    MonoidalClosed.ofEquiv (uliftIntEquivalence.{u + 1}).inverse
      (uliftIntEquivalence.{u + 1}).symm.toAdjunction
  let : HasLimitsOfSize.{max u₁ u₂, max u₁ u₂} AddCommGrpCat.{u + 1} :=
    hasLimitsOfSizeOfUnivLE.{u + 1, u + 1, max u₁ u₂, max u₁ u₂} _
  let : EnrichedOrdinaryCategory AddCommGrpCat.{u + 1} AddCommGrpCat.{u + 1} := inferInstance
  let : ∀ F₁ F₂ : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      HasFunctorEnrichedHom AddCommGrpCat.{u + 1} F₁ F₂ := by
    intro F₁ F₂ V
    infer_instance
  let : ∀ F₁ F₂ : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      HasEnrichedHom AddCommGrpCat.{u + 1} F₁ F₂ := by
    intro F₁ F₂
    infer_instance
  rw [presheafTensorInsert_eq]
  refine J.W.comp_mem _ _ (J.W.of_isIso _) ?_
  apply MorphismProperty.RespectsIso.precomp
  apply MorphismProperty.RespectsIso.postcomp
  exact J.W.tensorHom_mem (𝟙 F) s (J.W.id_mem F) hs

end AddCommGrpCat

/-! ### Tensoring a sheaf of modules with a presheaf of abelian groups -/

namespace Stacks.SheafOfModules

open AddCommGrpCat

variable {C : Type u₁} [Category.{u₂} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

section Construction

variable (F : SheafOfModules.{u + 1} R) (L : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1})

/-- The sections of a sheaf of `R`-modules, read as an abelian presheaf, are a module over
the ring of sections. -/
local instance moduleAbelianSections (V : Cᵒᵖ) : Module (R.obj.obj V) (F.val.presheaf.obj V) :=
  inferInstanceAs (Module (R.obj.obj V) (F.val.obj V))

/-- The sections of the objectwise tensor product over `ℤ` of a sheaf of `R`-modules with a
presheaf of abelian groups are a module over the ring of sections, acting on the left-hand
factor. -/
local instance moduleTensorAbelian (V : Cᵒᵖ) :
    Module (R.obj.obj V) ((presheafTensor F.val.presheaf L).obj V) :=
  inferInstanceAs (Module (R.obj.obj V)
    (TensorProduct ℤ (F.val.presheaf.obj V) (L.obj V)))

/-- The restriction maps of the objectwise tensor product over `ℤ` are semilinear for the
action of the ring of sections on the left-hand factor. -/
theorem tensorAbelian_map_smul {V W : Cᵒᵖ} (f : V ⟶ W) (a : R.obj.obj V)
    (z : TensorProduct ℤ (F.val.presheaf.obj V) (L.obj V)) :
    TensorProduct.map (F.val.presheaf.map f).hom.toIntLinearMap
        (L.map f).hom.toIntLinearMap (a • z) =
      (R.obj.map f) a • TensorProduct.map (F.val.presheaf.map f).hom.toIntLinearMap
        (L.map f).hom.toIntLinearMap z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | tmul x y =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.smul_tmul']
    congr 1
    exact F.val.map_smul f a x

/-- The objectwise tensor product over `ℤ` of a sheaf of `R`-modules with a presheaf of
abelian groups, as a presheaf of `R`-modules: the ring of sections acts on the left-hand
factor. -/
def tensorAbelianPresheaf : PresheafOfModules.{u + 1} R.obj :=
  PresheafOfModules.ofPresheaf (presheafTensor F.val.presheaf L)
    (fun _ _ f a z => tensorAbelian_map_smul F L f a z)

/-- The underlying abelian presheaf of the objectwise tensor product is the objectwise tensor
product of the underlying abelian presheaves. -/
lemma tensorAbelianPresheaf_presheaf :
    (tensorAbelianPresheaf F L).presheaf = presheafTensor F.val.presheaf L := rfl

variable [HasWeakSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]

/-- The tensor product over `ℤ` of a sheaf of `R`-modules with a presheaf of abelian groups:
the sheafification of the objectwise tensor product, with the ring of sections acting on the
left-hand factor. -/
def tensorAbelianModule : SheafOfModules.{u + 1} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj (tensorAbelianPresheaf F L)

/-- The canonical map from the objectwise tensor product to the sections of the tensor
product. -/
def toTensorAbelianModule :
    presheafTensor F.val.presheaf L ⟶ (tensorAbelianModule F L).val.presheaf :=
  CategoryTheory.toSheafify J (presheafTensor F.val.presheaf L)

/-- Sheafification inverts the canonical map to the tensor product. -/
theorem toTensorAbelianModule_mem : J.W (toTensorAbelianModule F L) :=
  J.W_toSheafify _

/-- The canonical map to the tensor product is linear in the left-hand factor. -/
theorem toTensorAbelianModule_smul_tmul (V : Cᵒᵖ) (a : R.obj.obj V) (x : F.val.obj V)
    (y : L.obj V) :
    (toTensorAbelianModule F L).app V ((a • x) ⊗ₜ[ℤ] y) =
      a • (show (tensorAbelianModule F L).val.obj V from
        (toTensorAbelianModule F L).app V (x ⊗ₜ[ℤ] y)) :=
  ((PresheafOfModules.toSheafify (𝟙 R.obj)
    (CategoryTheory.toSheafify J (tensorAbelianPresheaf F L).presheaf)).app V).hom.map_smul
      a (x ⊗ₜ[ℤ] y)

end Construction

/-! ### Quasi-coherence is a local property -/

/-- A sheaf of modules which is locally isomorphic to a quasi-coherent one is quasi-coherent:
restrict a presentation of the quasi-coherent module to a covering of each object on which the
two agree. -/
theorem isQuasicoherentOnSite_of_locally_iso {M N : SheafOfModules.{u + 1} R}
    (hM : M.IsQuasicoherentOnSite)
    (h : ∀ V : C, ∃ (I : Type (max u₁ u₂)) (Z : I → C) (f : ∀ i, Z i ⟶ V),
      Sieve.ofArrows Z f ∈ J V ∧ ∀ i, Nonempty (M.over (Z i) ≅ N.over (Z i))) :
    N.IsQuasicoherentOnSite := by
  classical
  refine ⟨fun V => ?_⟩
  obtain ⟨I, Z, f, hf, he⟩ := h V
  choose K Y g hg hp using fun i => hM.locally_hasGlobalPresentation (Z i)
  refine ⟨Σ i, K i, fun p => Y p.1 p.2, fun p => g p.1 p.2 ≫ f p.1, ?_, ?_⟩
  · show Sieve.generate (Presieve.ofArrows _ _) ∈ J V
    rw [← Presieve.bindOfArrows_ofArrows]
    exact J.bindOfArrows hf hg
  · intro p
    exact _root_.SheafOfModules.HasGlobalPresentation.of_iso
      (((_root_.SheafOfModules.overFunctorMap R (g p.1 p.2)).app M).symm ≪≫
        (_root_.SheafOfModules.overMap R (g p.1 p.2)).mapIso (he p.1).some ≪≫
        ((_root_.SheafOfModules.overFunctorMap R (g p.1 p.2)).app N))
      (hp p.1 p.2)

/-! ### Trivializing a tensor factor on a slice -/

/-- Whiskering along a cocontinuous functor preserves the morphisms inverted by
sheafification. -/
theorem w_whiskerLeft_of_isCocontinuous {D : Type*} [Category D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (H : C ⥤ D)
    [H.IsCocontinuous J K]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {F G : Dᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (f : F ⟶ G) (hf : K.W f) :
    J.W (Functor.whiskerLeft H.op f) := by
  have := hf.isLocallyInjective
  have := hf.isLocallySurjective
  have := Presheaf.isLocallyInjective_whisker J K H f
  have := Presheaf.isLocallySurjective_whisker J K H f
  exact J.W_of_isLocallyBijective _

/-- On a slice on which the right-hand factor has a trivializing global section, the tensor
product over `ℤ` is isomorphic to the left-hand factor. -/
theorem nonempty_over_iso_of_tensor_generator [UnivLE.{max u₁ u₂, u + 1}]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (F M : SheafOfModules.{u + 1} R) (L : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (η : presheafTensor F.val.presheaf L ⟶ M.val.presheaf) (hη : J.W η)
    (hlinear : ∀ (V : Cᵒᵖ) (a : R.obj.obj V) (x : F.val.obj V) (y : L.obj V),
      η.app V ((a • x) ⊗ₜ[ℤ] y) = a • (show M.val.obj V from η.app V (x ⊗ₜ[ℤ] y)))
    (U : C)
    [HasWeakSheafify (J.over U) AddCommGrpCat.{u + 1}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (s : (Functor.const (Over U)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
      (Over.forget U).op ⋙ L)
    (hs : (J.over U).W s) : Nonempty (F.over U ≅ M.over U) := by
  let a : (F.over U).val.presheaf ⟶ (M.over U).val.presheaf :=
    presheafTensorInsert (F.over U).val.presheaf s ≫ Functor.whiskerLeft (Over.forget U).op η
  let f : F.over U ⟶ M.over U := ⟨PresheafOfModules.homMk a (by
    intro V b x
    show η.app ((Over.forget U).op.obj V) ((b • x) ⊗ₜ[ℤ] s.app V (ULift.up 1)) =
      b • (show (M.over U).val.obj V from
        η.app ((Over.forget U).op.obj V) (x ⊗ₜ[ℤ] s.app V (ULift.up 1)))
    exact hlinear _ b x _)⟩
  have ha : (J.over U).W a := (J.over U).W.comp_mem _ _
    (presheafTensorInsert_mem (J.over U) _ s hs)
    (w_whiskerLeft_of_isCocontinuous (J.over U) J (Over.forget U) η hη)
  have hiso : IsIso ((_root_.SheafOfModules.toSheaf (R.over U)).map f) :=
    (((J.over U).W_sheafToPresheaf_map_iff_isIso _).1 ha)
  have := isIso_of_reflects_iso f (_root_.SheafOfModules.toSheaf (R.over U))
  exact ⟨asIso f⟩

/-- A trivialization of an abelian sheaf on a slice of the target site produces a global
integral section on the corresponding slice of the source site which sheafification
inverts. -/
theorem exists_generator_on_over {D : Type*} [Category D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (H : C ⥤ D)
    [H.IsCocontinuous J K]
    (L : Sheaf K AddCommGrpCat.{u + 1}) (U : C) (V : D) (b : H.obj U ⟶ V)
    [HasWeakSheafify (K.over V) AddCommGrpCat.{u + 1}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [(K.over V).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (e : L.over V ≅ (constantSheaf (K.over V) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) :
    ∃ s : (Functor.const (Over U)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
      (Over.forget U).op ⋙ (H.op ⋙ L.obj), (J.over U).W s := by
  let c := CategoryTheory.toSheafify (K.over V)
    ((Functor.const (Over V)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫ e.inv.hom
  have hc : (K.over V).W c :=
    (K.over V).W.comp_mem _ _ ((K.over V).W_toSheafify _)
      (((K.over V).W_sheafToPresheaf_map_iff_isIso e.inv).mpr inferInstance)
  have hcc : (Over.post (X := U) H ⋙ Over.map b).IsCocontinuous (J.over U) (K.over V) :=
    isCocontinuous_comp (Over.post H) (Over.map b) (J.over U) (K.over (H.obj U))
  exact ⟨Functor.whiskerLeft (Over.post (X := U) H ⋙ Over.map b).op c,
    w_whiskerLeft_of_isCocontinuous (J.over U) (K.over V)
      (Over.post (X := U) H ⋙ Over.map b) c hc⟩

end Stacks.SheafOfModules

/-! ### The rank one twist attached to a character -/

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (G : Type v) [Group G]
  (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) [∀ T, MulAction G (W.obj T)]

/-- Acting by `g` is an endomorphism of the presheaf of points of `W`. -/
def actionHom (hnat : IsNaturalAction B S hS G W) (g : G) : W ⟶ W where
  app _ := ↾(fun x => g • x)
  naturality _ _ f := ConcreteCategory.hom_ext _ _ fun x => (hnat f g x).symm

variable {B S hS G W}

/-- Acting by `g` is an automorphism of `W` as an object of the spaces-étale site of a
quotient `X` through a `G`-invariant étale morphism `q : W ⟶ X`. -/
def actionEtale {hW : IsAlgebraicSpace B S hS W} {X : AlgebraicSpaces B S hS}
    {q : (⟨W, hW⟩ : AlgebraicSpaces B S hS) ⟶ X} (hq : IsEtale B S hS q.hom)
    {hnat : IsNaturalAction B S hS G W}
    (hinv : ∀ g : G, actionHom B S hS G W hnat g ≫ q.hom = q.hom) (g : G) :
    etaleObject B S hS q hq ⟶ etaleObject B S hS q hq :=
  ObjectProperty.homMk
    (Over.homMk (ObjectProperty.homMk (actionHom B S hS G W hnat g))
      (ObjectProperty.hom_ext _ (hinv g)))

/-- The sections of an abelian sheaf `F` on the spaces-étale site of `X` over `W` that
transform according to the character `χ`, that is `H⁰(W, F|_W)^χ`. -/
def characterSections {hW : IsAlgebraicSpace B S hS W} {X : AlgebraicSpaces B S hS}
    {q : (⟨W, hW⟩ : AlgebraicSpaces B S hS) ⟶ X} (hq : IsEtale B S hS q.hom)
    {hnat : IsNaturalAction B S hS G W}
    (hinv : ∀ g : G, actionHom B S hS G W hnat g ≫ q.hom = q.hom) (χ : G →* ℤˣ)
    (F : Sheaf (SpacesEtale.topology B S hS X) AddCommGrpCat.{u + 1}) :
    AddSubgroup (F.obj.obj (Opposite.op (etaleObject B S hS q hq))) where
  carrier := {s | ∀ g : G, F.obj.map (actionEtale hq hinv g).op s = (χ g : ℤ) • s}
  zero_mem' := fun g => by simp only [map_zero, zsmul_zero]
  add_mem' := fun ha hb g => by rw [map_add, ha g, hb g, zsmul_add]
  neg_mem' := fun ha g => by rw [map_neg, ha g, zsmul_neg]

variable (B S hS)

/-- An abelian sheaf on the spaces-étale site of `X` is *free of rank one* on the object `V`
when its restriction to the localization of the site at `V` is isomorphic to the constant
sheaf `ℤ`. -/
def IsFreeOfRankOneOn (X : AlgebraicSpaces B S hS)
    (L : Sheaf (SpacesEtale.topology B S hS X) AddCommGrpCat.{u + 1})
    (V : SpacesEtale B S hS X) : Prop :=
  Nonempty (L.over V ≅
    (constantSheaf ((SpacesEtale.topology B S hS X).over V) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

/-- An abelian sheaf on the spaces-étale site of `X` is *locally free of rank one* when it is
free of rank one on every member of some covering family of `X`. -/
def IsLocallyFreeOfRankOne (X : AlgebraicSpaces B S hS)
    (L : Sheaf (SpacesEtale.topology B S hS X) AddCommGrpCat.{u + 1}) : Prop :=
  ∃ E : PreZeroHypercover.{u + 1} (SpacesEtale.final B S hS X),
    SpacesEtale.IsCovering B S hS X ⟨SpacesEtale.final B S hS X, E⟩ ∧
      ∀ i, IsFreeOfRankOneOn B S hS X L (E.X i)

variable (G W)

/-- The data and conclusions of Stacks 0727 for a free action of a finite group `G` on the
algebraic space `W` and a character `χ : G → {+1, -1}`: the quotient `U = W/G` with its étale
and `G`-invariant quotient morphism, and the rank one locally free sheaf of `ℤ`-modules
`ℤ(χ)` on `U_étale` identifying the `χ`-semi-invariant sections of an abelian sheaf over `W`
with the global sections of its twist.

Stacks 072A is stated over this package, since its hypothesis is literally "with `S`, `W`,
`G`, `U`, `χ` as in Lemma 0727". -/
structure SignTwistSetup [Finite G] (χ : G →* ℤˣ) where
  /-- `W` is an algebraic space over `S`. -/
  isAlgebraicSpace : IsAlgebraicSpace B S hS W
  /-- The pointwise action of `G` on the points of `W` is compatible with restriction. -/
  natural : IsNaturalAction B S hS G W
  /-- The action is free on the points over every test object with nonempty underlying
  scheme. -/
  free : IsFreeOnNonemptyPoints B S hS G W
  /-- The quotient algebraic space `U = W/G`. -/
  quotient : AlgebraicSpaces B S hS
  /-- The quotient morphism `q : W ⟶ U`. -/
  proj : (⟨W, isAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶ quotient
  /-- The quotient morphism is étale, which uses that `G` is finite. -/
  isEtale_proj : IsEtale B S hS proj.hom
  /-- The quotient morphism is invariant under the action. -/
  actionHom_comp_proj : ∀ g : G, actionHom B S hS G W natural g ≫ proj.hom = proj.hom
  /-- The rank one sheaf of `ℤ`-modules `ℤ(χ)` on `U_étale`. -/
  sheaf : Sheaf (SpacesEtale.topology B S hS quotient) AddCommGrpCat.{u + 1}
  /-- `ℤ(χ)` is locally free of rank one. -/
  locallyFree : IsLocallyFreeOfRankOne B S hS quotient sheaf
  /-- `H⁰(W, F|_W)^χ = H⁰(U, F ⊗_ℤ ℤ(χ))` for every abelian sheaf `F` on `U_étale`. -/
  sectionsEquiv (F : Sheaf (SpacesEtale.topology B S hS quotient) AddCommGrpCat.{u + 1}) :
    characterSections isEtale_proj actionHom_comp_proj χ F ≃+
      (SpacesEtale.abelianSheafTensor B S hS quotient F sheaf).obj.obj
        (Opposite.op (SpacesEtale.final B S hS quotient))

namespace SignTwistSetup

variable {B S hS G W} [Finite G] {χ : G →* ℤˣ} (h : SignTwistSetup B S hS G W χ)

/-- The twist `ℤ(χ)`, restricted along the comparison functor of Stacks 03G1 to the small
étale site of the quotient, where the quasi-coherent modules live. -/
def smallEtaleSheaf :
    Sheaf (SmallEtale.topology B S hS h.quotient.1) AddCommGrpCat.{u + 1} :=
  ((comparisonFunctor B S hS h.quotient).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B S hS h.quotient.1)
    (SpacesEtale.topology B S hS h.quotient)).obj h.sheaf

/-- The twist `F ⊗_ℤ ℤ(χ)` of an `𝒪_U`-module `F`, with `𝒪_U` acting on the left-hand
factor. -/
def twist (F : Modules.{u, u + 1} B S hS h.quotient.1 h.quotient.2) :
    Modules.{u, u + 1} B S hS h.quotient.1 h.quotient.2 :=
  Stacks.SheafOfModules.tensorAbelianModule F h.smallEtaleSheaf.obj

/-- **Stacks 072A.** With `S`, `W`, `G`, `U`, `χ` as in Stacks 0727: if `F` is a
quasi-coherent `𝒪_U`-module, then so is `F ⊗_ℤ ℤ(χ)`.

Quasi-coherence may be checked étale locally, and `ℤ(χ)` is free of rank one on a covering of
`U`; on each member of that covering a trivializing section identifies the twist with `F`
itself. -/
@[stacks 072A]
theorem isQuasicoherentOnSite_twist
    (F : Modules.{u, u + 1} B S hS h.quotient.1 h.quotient.2) (hF : F.IsQuasicoherentOnSite) :
    (h.twist F).IsQuasicoherentOnSite := by
  classical
  have hcc : (comparisonFunctor B S hS h.quotient).IsCocontinuous
      (SmallEtale.topology B S hS h.quotient.1)
      (SpacesEtale.topology B S hS h.quotient) :=
    (comparisonFunctor_specialCocontinuous B S hS h.quotient).1
  have hη : (SmallEtale.topology B S hS h.quotient.1).W
      (Stacks.SheafOfModules.toTensorAbelianModule F h.smallEtaleSheaf.obj) :=
    Stacks.SheafOfModules.toTensorAbelianModule_mem _ _
  refine Stacks.SheafOfModules.isQuasicoherentOnSite_of_locally_iso (M := F) hF ?_
  intro U
  obtain ⟨E, hE, he⟩ := h.locallyFree
  have hcover : E.sieve₀ ∈ (SpacesEtale.topology B S hS h.quotient)
      (SpacesEtale.final B S hS h.quotient) :=
    Precoverage.generate_mem_toGrothendieck
      (J := SpacesEtale.precoverage B S hS h.quotient) ⟨E, rfl, hE⟩
  let q := (SpacesEtale.final_isTerminal B S hS h.quotient).from
    ((comparisonFunctor B S hS h.quotient).obj U)
  let T := (E.sieve₀.pullback q).functorPullback (comparisonFunctor B S hS h.quotient)
  have hTmem : T ∈ (SmallEtale.topology B S hS h.quotient.1) U :=
    (comparisonFunctor B S hS h.quotient).cover_lift _ _
      ((SpacesEtale.topology B S hS h.quotient).pullback_stable q hcover)
  refine ⟨{a : Over U // T.arrows a.hom}, fun a => a.1.left, fun a => a.1.hom, ?_, ?_⟩
  · have hEq : Sieve.ofArrows (fun a : {a : Over U // T.arrows a.hom} => a.1.left)
        (fun a => a.1.hom) = T := by
      apply le_antisymm
      · intro Z g hg
        rw [Sieve.mem_ofArrows_iff] at hg
        obtain ⟨a, b, rfl⟩ := hg
        exact T.downward_closed a.2 b
      · intro Z g hg
        exact Sieve.ofArrows_mk (fun a : {a : Over U // T.arrows a.hom} => a.1.left)
          (fun a => a.1.hom) ⟨Over.mk g, hg⟩
    rwa [hEq]
  · rintro ⟨a, ha⟩
    have ha' : Sieve.ofArrows E.X E.f
        ((comparisonFunctor B S hS h.quotient).map a.hom ≫ q) := ha
    rw [Sieve.mem_ofArrows_iff] at ha'
    obtain ⟨i, b, _⟩ := ha'
    obtain ⟨s, hs⟩ := Stacks.SheafOfModules.exists_generator_on_over
      (SmallEtale.topology B S hS h.quotient.1)
      (SpacesEtale.topology B S hS h.quotient)
      (comparisonFunctor B S hS h.quotient) h.sheaf a.left (E.X i) b (he i).some
    exact Stacks.SheafOfModules.nonempty_over_iso_of_tensor_generator F (h.twist F)
      h.smallEtaleSheaf.obj
      (Stacks.SheafOfModules.toTensorAbelianModule F h.smallEtaleSheaf.obj) hη
      (Stacks.SheafOfModules.toTensorAbelianModule_smul_tmul F h.smallEtaleSheaf.obj)
      a.left s hs

end SignTwistSetup

/-! ### A nontrivial group satisfying the package -/

variable (X : AlgebraicSpaces B S hS)

private lemma hom_apply_comp {A A' A'' : AddCommGrpCat.{u + 1}} (f : A ⟶ A') (g : A' ⟶ A'')
    (a : A) : g (f a) = (f ≫ g) a := rfl

private lemma integerHomEquiv_symm_comp {A A' : AddCommGrpCat.{u + 1}} (g : A ⟶ A')
    (a : A) : (SpacesEtale.integerHomEquiv A).symm a ≫ g =
      (SpacesEtale.integerHomEquiv A').symm (g a) := by
  ext z
  exact map_zsmul g.hom z.down a

namespace SpacesEtale

/-- **A section of an abelian sheaf over a coproduct of the spaces-étale site of `X` is the
same thing as an arbitrary family of sections over the members.**

This is the sheaf condition for the covering family of a coproduct
(`AlgebraicGeometry.Space.SpacesEtale.ofArrows_mem_topology_of_isColimit_cofan`), read through
the identification of sections with homomorphisms out of the integers
(`AlgebraicGeometry.Space.SpacesEtale.integerHomEquiv`).  No compatibility hypothesis is
needed: two indices either agree, and then the two test morphisms agree because the inclusions
are monomorphisms, or differ, and then the test object is covered by the empty sieve, so the
sheaf has a single section over it. -/
theorem existsUnique_section_of_isColimit_cofan
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1})
    {Y : WalkingPair → SpacesEtale B S hS X} {P : SpacesEtale B S hS X} (i : ∀ p, Y p ⟶ P)
    (hP : IsColimit (Cofan.mk P i)) (x : ∀ p, F.obj.obj (Opposite.op (Y p))) :
    ∃! s : F.obj.obj (Opposite.op P), ∀ p, F.obj.map (i p).op s = x p := by
  classical
  have hmono := mono_of_isColimit_cofan B S hS X i hP
  have hcov := ofArrows_mem_topology_of_isColimit_cofan B S hS X i hP
  have hx : ∀ ⦃V : SpacesEtale B S hS X⦄ ⦃k l : ULift.{u + 1} WalkingPair⦄
      (a : V ⟶ Y k.down) (b : V ⟶ Y l.down), a ≫ i k.down = b ≫ i l.down →
      (integerHomEquiv _).symm (x k.down) ≫ F.obj.map a.op =
        (integerHomEquiv _).symm (x l.down) ≫ F.obj.map b.op := by
    intro V k l a b hab
    by_cases hkl : k.down = l.down
    · obtain ⟨k⟩ := k
      obtain ⟨l⟩ := l
      subst hkl
      have := hmono k
      rw [(cancel_mono (i k)).1 hab]
    · have hbot := bot_mem_topology_of_isColimit_cofan B S hS X i hP hkl a b hab
      have hsub : Subsingleton (AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶
          F.obj.obj (Opposite.op V)) :=
        (F.property (AddCommGrpCat.of (ULift.{u + 1} ℤ))).subsingleton_obj_of_bot_mem _ hbot
      exact hsub.elim _ _
  obtain ⟨α, hα, hαuniq⟩ := Presheaf.IsSheaf.existsUnique_amalgamation_ofArrows
    (P := F.obj) F.property (fun k : ULift.{u + 1} WalkingPair => i k.down) hcov
    (fun k => (integerHomEquiv _).symm (x k.down)) hx
  refine ⟨integerHomEquiv _ α, fun p => ?_, fun s hs => ?_⟩
  · have h := congrArg (integerHomEquiv (F.obj.obj (Opposite.op (Y p)))) (hα ⟨p⟩)
    rwa [Equiv.apply_symm_apply] at h
  · have h : (integerHomEquiv _).symm s = α := by
      refine hαuniq _ fun k => ?_
      rw [integerHomEquiv_symm_comp (F.obj.map (i k.down).op) s, hs k.down]
    rw [← h, Equiv.apply_symm_apply]

/-- **Tensoring an abelian sheaf on the spaces-étale site of `X` over `ℤ` with the constant
sheaf `ℤ` changes nothing.**

Inserting the universal integral section into the right-hand factor is a morphism from the
sheaf to the objectwise tensor product which sheafification inverts
(`AddCommGrpCat.presheafTensorInsert_mem`), because the canonical map from the constant
presheaf `ℤ` to the constant sheaf `ℤ` is.  Sheafifying it therefore gives an isomorphism, and
the sheaf is its own sheafification. -/
def abelianSheafTensorConstantIso (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    F ≅ abelianSheafTensor B S hS X F
      ((constantSheaf (topology B S hS X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) := by
  let L := (constantSheaf (topology B S hS X) AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let s : (Functor.const (SpacesEtale B S hS X)ᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ L.obj :=
    CategoryTheory.toSheafify (topology B S hS X) _
  let ins : F.obj ⟶ AddCommGrpCat.presheafTensor F.obj L.obj :=
    AddCommGrpCat.presheafTensorInsert F.obj s
  have hiso : IsIso ((presheafToSheaf (topology B S hS X) AddCommGrpCat.{u + 1}).map ins) :=
    ((topology B S hS X).W_iff ins).1
      (AddCommGrpCat.presheafTensorInsert_mem (topology B S hS X) F.obj s
        ((topology B S hS X).W_toSheafify _))
  exact sheafificationIso F ≪≫
    asIso ((presheafToSheaf (topology B S hS X) AddCommGrpCat.{u + 1}).map ins)

end SpacesEtale

/-- **The restriction of the constant sheaf `ℤ` to a slice of the spaces-étale site of `X` is
the constant sheaf `ℤ` on that slice.**

Restriction along the forgetful functor of the slice preserves the morphisms inverted by
sheafification (`Stacks.SheafOfModules.w_whiskerLeft_of_isCocontinuous`), and it carries the
constant presheaf to the constant presheaf; so the restricted canonical map from the constant
presheaf is still inverted by sheafification. -/
def constantSheafOverIso (V : SpacesEtale B S hS X) (M : AddCommGrpCat.{u + 1}) :
    ((constantSheaf (SpacesEtale.topology B S hS X) AddCommGrpCat.{u + 1}).obj M).over V ≅
      (constantSheaf ((SpacesEtale.topology B S hS X).over V) AddCommGrpCat.{u + 1}).obj M := by
  let t := CategoryTheory.toSheafify (SpacesEtale.topology B S hS X)
    ((Functor.const (SpacesEtale B S hS X)ᵒᵖ).obj M)
  let w := Functor.whiskerLeft (Over.forget V).op t
  have hw : ((SpacesEtale.topology B S hS X).over V).W w :=
    Stacks.SheafOfModules.w_whiskerLeft_of_isCocontinuous
      ((SpacesEtale.topology B S hS X).over V) (SpacesEtale.topology B S hS X) (Over.forget V)
      t ((SpacesEtale.topology B S hS X).W_toSheafify _)
  have hiso : IsIso ((presheafToSheaf ((SpacesEtale.topology B S hS X).over V)
      AddCommGrpCat.{u + 1}).map w) := (((SpacesEtale.topology B S hS X).over V).W_iff w).1 hw
  exact sheafificationIso _ ≪≫ (asIso ((presheafToSheaf
    ((SpacesEtale.topology B S hS X).over V) AddCommGrpCat.{u + 1}).map w)).symm

/-- The constant sheaf of `ℤ`-modules `ℤ` on the spaces-étale site of `X` is locally free of
rank one: it is already free of rank one on `X` itself, which covers `X`. -/
theorem isLocallyFreeOfRankOne_constantSheaf :
    IsLocallyFreeOfRankOne B S hS X ((constantSheaf (SpacesEtale.topology B S hS X)
      AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) := by
  refine ⟨⟨PUnit.{u + 2}, fun _ => SpacesEtale.final B S hS X, fun _ => 𝟙 _⟩,
    fun x => ⟨⟨⟩, x, ?_⟩, fun _ => ⟨constantSheafOverIso B S hS X _ _⟩⟩
  exact congrFun (pointsMap_id B S hS _) x

/-- The *split double cover* of `X`: the coproduct `X ⊔ X` in the spaces-étale site of `X`,
whose structure morphism is the fold map. -/
abbrev splitDoubleCover : SpacesEtale B S hS X :=
  SpacesEtale.final B S hS X ⨿ SpacesEtale.final B S hS X

/-- The two inclusions of `X` into its split double cover. -/
abbrev splitDoubleCoverInj (p : WalkingPair) :
    SpacesEtale.final B S hS X ⟶ splitDoubleCover B S hS X :=
  p.casesOn coprod.inl coprod.inr

/-- The two inclusions exhibit the split double cover as a coproduct of two copies of `X`. -/
def isColimit_cofan_splitDoubleCover :
    IsColimit (Cofan.mk (f := fun _ : WalkingPair => SpacesEtale.final B S hS X)
      (splitDoubleCover B S hS X) (splitDoubleCoverInj B S hS X)) :=
  Cofan.IsColimit.mk _
    (fun t => coprod.desc (t.inj WalkingPair.left) (t.inj WalkingPair.right))
    (fun t p => by cases p; exacts [coprod.inl_desc _ _, coprod.inr_desc _ _])
    (fun t m hm => coprod.hom_ext
      ((hm WalkingPair.left).trans (coprod.inl_desc _ _).symm)
      ((hm WalkingPair.right).trans (coprod.inr_desc _ _).symm))

/-- The automorphism of the split double cover of `X` exchanging its two summands. -/
abbrev splitDoubleCoverSwap : splitDoubleCover B S hS X ⟶ splitDoubleCover B S hS X :=
  coprod.desc coprod.inr coprod.inl

/-- The swap exchanges the two inclusions. -/
theorem splitDoubleCoverInj_comp_swap (p : WalkingPair) :
    splitDoubleCoverInj B S hS X p ≫ splitDoubleCoverSwap B S hS X =
      splitDoubleCoverInj B S hS X p.swap := by
  cases p
  · exact coprod.inl_desc _ _
  · exact coprod.inr_desc _ _

/-- The swap is an involution. -/
theorem splitDoubleCoverSwap_comp_swap :
    splitDoubleCoverSwap B S hS X ≫ splitDoubleCoverSwap B S hS X = 𝟙 _ := by
  apply coprod.hom_ext
  · rw [← Category.assoc, coprod.inl_desc, coprod.inr_desc, Category.comp_id]
  · rw [← Category.assoc, coprod.inr_desc, coprod.inl_desc, Category.comp_id]

/-- The presheaf of points of the split double cover of `X`. -/
abbrev splitDoubleCoverPresheaf : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  ((splitDoubleCover B S hS X).obj.left).obj

/-- The swap, read on the points of the split double cover over a test object. -/
def splitDoubleCoverPointSwap (T : (BigFppfOver B S hS)ᵒᵖ) :
    (splitDoubleCoverPresheaf B S hS X).obj T → (splitDoubleCoverPresheaf B S hS X).obj T :=
  ((SpacesEtale.toSpaces B S hS X).map (splitDoubleCoverSwap B S hS X)).hom.app T

/-- The swap is an involution on points. -/
theorem splitDoubleCoverPointSwap_involutive (T : (BigFppfOver B S hS)ᵒᵖ)
    (x : (splitDoubleCoverPresheaf B S hS X).obj T) :
    splitDoubleCoverPointSwap B S hS X T (splitDoubleCoverPointSwap B S hS X T x) = x := by
  have h : ((SpacesEtale.toSpaces B S hS X).map
      (splitDoubleCoverSwap B S hS X ≫ splitDoubleCoverSwap B S hS X)).hom.app T x = x := by
    rw [splitDoubleCoverSwap_comp_swap, CategoryTheory.Functor.map_id]
    rfl
  rwa [CategoryTheory.Functor.map_comp] at h

/-- The swap on points commutes with restriction. -/
theorem splitDoubleCoverPointSwap_naturality {T U : (BigFppfOver B S hS)ᵒᵖ} (f : T ⟶ U)
    (x : (splitDoubleCoverPresheaf B S hS X).obj T) :
    (splitDoubleCoverPresheaf B S hS X).map f (splitDoubleCoverPointSwap B S hS X T x) =
      splitDoubleCoverPointSwap B S hS X U ((splitDoubleCoverPresheaf B S hS X).map f x) :=
  (NatTrans.naturality_apply
    ((SpacesEtale.toSpaces B S hS X).map (splitDoubleCoverSwap B S hS X)).hom f x).symm

/-- The action of a unit of `ℤ` on the points of the split double cover of `X`: the
nontrivial unit acts by the swap. -/
def splitDoubleCoverSmul (T : (BigFppfOver B S hS)ᵒᵖ) (u : ℤˣ)
    (x : (splitDoubleCoverPresheaf B S hS X).obj T) :
    (splitDoubleCoverPresheaf B S hS X).obj T :=
  if u = 1 then x else splitDoubleCoverPointSwap B S hS X T x

/-- The two-element group `ℤˣ` acts on the points of the split double cover of `X` by the swap
of its two summands, which is an involution. -/
instance splitDoubleCoverMulAction (T : (BigFppfOver B S hS)ᵒᵖ) :
    MulAction ℤˣ ((splitDoubleCoverPresheaf B S hS X).obj T) where
  smul := splitDoubleCoverSmul B S hS X T
  one_smul x := by
    change splitDoubleCoverSmul B S hS X T 1 x = x
    simp [splitDoubleCoverSmul]
  mul_smul u v x := by
    have hne : ¬ ((-1 : ℤˣ) = 1) := by decide
    have hswap : ∀ y, splitDoubleCoverSmul B S hS X T (-1) y =
        splitDoubleCoverPointSwap B S hS X T y := fun y => by simp [splitDoubleCoverSmul, hne]
    have hone : ∀ y, splitDoubleCoverSmul B S hS X T 1 y = y := fun _ => by
      simp [splitDoubleCoverSmul]
    change splitDoubleCoverSmul B S hS X T (u * v) x =
      splitDoubleCoverSmul B S hS X T u (splitDoubleCoverSmul B S hS X T v x)
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl
    · rw [one_mul, hone, hone]
    · rw [one_mul, hone]
    · rw [mul_one, hone]
    · rw [show (-1 : ℤˣ) * (-1) = 1 by decide, hone, hswap, hswap,
        splitDoubleCoverPointSwap_involutive]

/-- The unit `1` acts trivially on the points of the split double cover. -/
theorem splitDoubleCover_one_smul (T : (BigFppfOver B S hS)ᵒᵖ)
    (x : (splitDoubleCoverPresheaf B S hS X).obj T) : (1 : ℤˣ) • x = x := by
  show splitDoubleCoverSmul B S hS X T 1 x = x
  simp [splitDoubleCoverSmul]

/-- The unit `-1` acts by the swap on the points of the split double cover. -/
theorem splitDoubleCover_neg_one_smul (T : (BigFppfOver B S hS)ᵒᵖ)
    (x : (splitDoubleCoverPresheaf B S hS X).obj T) :
    (-1 : ℤˣ) • x = splitDoubleCoverPointSwap B S hS X T x := by
  have hne : ¬ ((-1 : ℤˣ) = 1) := by decide
  show splitDoubleCoverSmul B S hS X T (-1) x = _
  simp [splitDoubleCoverSmul, hne]

/-- The action of `ℤˣ` on the split double cover of `X` is compatible with restriction. -/
theorem isNaturalAction_splitDoubleCover :
    IsNaturalAction B S hS ℤˣ (splitDoubleCoverPresheaf B S hS X) := by
  intro T U f u x
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp only [splitDoubleCover_one_smul]
  · simp only [splitDoubleCover_neg_one_smul, splitDoubleCoverPointSwap_naturality]

/-- **The swap of the two summands of the split double cover of `X` fixes no point over a test
object with nonempty underlying scheme.**

A point of the coproduct over a test object `T` decomposes `T` into two open pieces over which
the point comes from the two summands (Stacks 02WO).  Over such a piece the swap carries the
section of one summand to a section of the *other* summand with the same image in the
coproduct, which forces the piece to have empty underlying scheme; and the two pieces cover
`T`. -/
theorem splitDoubleCoverPointSwap_ne (T : (BigFppfOver B S hS)ᵒᵖ)
    (hT : Nonempty ((BigFppfOver.toScheme B S hS).obj T.unop))
    (x : (splitDoubleCoverPresheaf B S hS X).obj T) :
    splitDoubleCoverPointSwap B S hS X T x ≠ x := by
  intro hx
  obtain ⟨hsh⟩ := SpacesEtale.nonempty_isColimit_cofan_toSheaf B S hS X
    (splitDoubleCoverInj B S hS X) (isColimit_cofan_splitDoubleCover B S hS X)
  obtain ⟨W', pr, hoi, hsec, hdisj, hcov, huniv⟩ :=
    Sheaf.exists_clopen_decomposition_of_isColimit_cofan
      (fun p => (SpacesEtale.toSheaf B S hS X).map (splitDoubleCoverInj B S hS X p)) hsh
      T.unop x
  obtain ⟨w⟩ := hT
  obtain ⟨p, hp⟩ := hcov w
  obtain ⟨z, hz⟩ := hsec p
  have hempty : IsEmpty ((BigFppfOver.toScheme B S hS).obj (W' p)) := by
    refine Sheaf.isEmpty_toScheme_of_eq_of_ne
      (fun p => (SpacesEtale.toSheaf B S hS X).map (splitDoubleCoverInj B S hS X p)) hsh
      (i := p) (j := WalkingPair.swap p) (fun h => by cases p <;> exact absurd h (by decide))
      z z ?_
    have h1 : splitDoubleCoverInj B S hS X (WalkingPair.swap p) =
        splitDoubleCoverInj B S hS X p ≫ splitDoubleCoverSwap B S hS X :=
      (splitDoubleCoverInj_comp_swap B S hS X p).symm
    have hcomp : (((SpacesEtale.toSheaf B S hS X).map (splitDoubleCoverInj B S hS X p) ≫
          (SpacesEtale.toSheaf B S hS X).map
            (splitDoubleCoverSwap B S hS X)).hom.app (Opposite.op (W' p))) z =
        splitDoubleCoverPointSwap B S hS X (Opposite.op (W' p))
          (((SpacesEtale.toSheaf B S hS X).map
            (splitDoubleCoverInj B S hS X p)).hom.app (Opposite.op (W' p)) z) := rfl
    rw [h1, CategoryTheory.Functor.map_comp, hcomp, hz]
    have hgoal := splitDoubleCoverPointSwap_naturality B S hS X (pr p).op x
    rwa [hx] at hgoal
  obtain ⟨y, -⟩ := hp
  exact hempty.false y

/-- **The action of `ℤˣ` by the swap on the split double cover of `X` is free on the points
over the test objects with nonempty underlying scheme.**  This is the satisfiable form of
freeness, and the reason a nontrivial group can appear in
`AlgebraicGeometry.Space.SignTwistSetup` at all. -/
theorem isFreeOnNonemptyPoints_splitDoubleCover :
    IsFreeOnNonemptyPoints B S hS ℤˣ (splitDoubleCoverPresheaf B S hS X) := by
  intro T hT
  refine { left_cancel' := ?_, right_cancel' := ?_ }
  · intro u a b hab
    rcases Int.units_eq_one_or u with rfl | rfl
    · simpa only [splitDoubleCover_one_smul] using hab
    · simpa only [splitDoubleCover_neg_one_smul, splitDoubleCoverPointSwap_involutive] using
        congrArg (splitDoubleCoverPointSwap B S hS X T) hab
  · intro u v a huv
    have hne : (1 : ℤˣ) • a ≠ (-1 : ℤˣ) • a := by
      rw [splitDoubleCover_one_smul, splitDoubleCover_neg_one_smul]
      exact (splitDoubleCoverPointSwap_ne B S hS X T hT a).symm
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl
    exacts [rfl, absurd huv hne, absurd huv.symm hne, rfl]

/-- The unit `1` acts on the split double cover of `X` by the identity. -/
theorem splitDoubleCoverActionHom_one :
    actionHom B S hS ℤˣ (splitDoubleCoverPresheaf B S hS X)
      (isNaturalAction_splitDoubleCover B S hS X) 1 = 𝟙 _ := by
  ext T x
  exact splitDoubleCover_one_smul B S hS X T x

/-- The unit `-1` acts on the split double cover of `X` by the swap. -/
theorem splitDoubleCoverActionHom_neg_one :
    actionHom B S hS ℤˣ (splitDoubleCoverPresheaf B S hS X)
        (isNaturalAction_splitDoubleCover B S hS X) (-1) =
      ((SpacesEtale.toSpaces B S hS X).map (splitDoubleCoverSwap B S hS X)).hom := by
  ext T x
  exact splitDoubleCover_neg_one_smul B S hS X T x

/-- The fold map of the split double cover of `X` is invariant under the action of `ℤˣ`. -/
theorem splitDoubleCoverActionHom_comp_proj (u : ℤˣ) :
    actionHom B S hS ℤˣ (splitDoubleCoverPresheaf B S hS X)
        (isNaturalAction_splitDoubleCover B S hS X) u ≫
      ((splitDoubleCover B S hS X).obj.hom).hom = ((splitDoubleCover B S hS X).obj.hom).hom := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · rw [splitDoubleCoverActionHom_one, Category.id_comp]
  · rw [splitDoubleCoverActionHom_neg_one]
    exact SpacesEtale.toSheaf_map_hom_comp B S hS X (splitDoubleCoverSwap B S hS X)

/-- The unit `1` acts on the split double cover, read in the spaces-étale site of `X`, by the
identity. -/
theorem splitDoubleCoverActionEtale_one :
    actionEtale (hq := (splitDoubleCover B S hS X).property)
        (hinv := splitDoubleCoverActionHom_comp_proj B S hS X) 1 = 𝟙 _ :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _
    (splitDoubleCoverActionHom_one B S hS X)))

/-- The unit `-1` acts on the split double cover, read in the spaces-étale site of `X`, by the
swap. -/
theorem splitDoubleCoverActionEtale_neg_one :
    actionEtale (hq := (splitDoubleCover B S hS X).property)
        (hinv := splitDoubleCoverActionHom_comp_proj B S hS X) (-1) =
      splitDoubleCoverSwap B S hS X :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _
    (splitDoubleCoverActionHom_neg_one B S hS X)))

/-- A section of an abelian sheaf over the split double cover of `X` transforms according to
the identity character of `ℤˣ` exactly when the swap negates it. -/
theorem mem_characterSections_splitDoubleCover_iff
    (F : Sheaf (SpacesEtale.topology B S hS X) AddCommGrpCat.{u + 1})
    (s : F.obj.obj (Opposite.op (splitDoubleCover B S hS X))) :
    s ∈ characterSections (splitDoubleCover B S hS X).property
        (splitDoubleCoverActionHom_comp_proj B S hS X) (MonoidHom.id ℤˣ) F ↔
      F.obj.map (splitDoubleCoverSwap B S hS X).op s = -s := by
  refine ⟨fun hs => ?_, fun hs u => ?_⟩
  · have h := hs (-1)
    rw [splitDoubleCoverActionEtale_neg_one] at h
    exact h.trans (neg_one_zsmul s)
  · rcases Int.units_eq_one_or u with rfl | rfl
    · rw [splitDoubleCoverActionEtale_one]
      show F.obj.map (𝟙 (Opposite.op (splitDoubleCover B S hS X))) s = _
      rw [CategoryTheory.Functor.map_id]
      show s = _
      exact (one_zsmul s).symm
    · rw [splitDoubleCoverActionEtale_neg_one]
      exact hs.trans (neg_one_zsmul s).symm

section Sections

variable (F : Sheaf (SpacesEtale.topology B S hS X) AddCommGrpCat.{u + 1})

/-- Restricting along one inclusion of the split double cover after the swap is restricting
along the other inclusion. -/
theorem map_splitDoubleCoverInj_map_swap (p : WalkingPair)
    (s : F.obj.obj (Opposite.op (splitDoubleCover B S hS X))) :
    F.obj.map (splitDoubleCoverInj B S hS X p).op
        (F.obj.map (splitDoubleCoverSwap B S hS X).op s) =
      F.obj.map (splitDoubleCoverInj B S hS X p.swap).op s := by
  rw [hom_apply_comp, ← CategoryTheory.Functor.map_comp, ← op_comp,
    splitDoubleCoverInj_comp_swap]

/-- The family `(a, -a)` of sections over the two summands of the split double cover of `X`. -/
def splitDoubleCoverSignPair (a : F.obj.obj (Opposite.op (SpacesEtale.final B S hS X)))
    (p : WalkingPair) : F.obj.obj (Opposite.op (SpacesEtale.final B S hS X)) := p.casesOn a (-a)

/-- The family `(a, -a)` is exchanged with its negative by the swap of the two summands. -/
theorem splitDoubleCoverSignPair_swap
    (a : F.obj.obj (Opposite.op (SpacesEtale.final B S hS X))) (p : WalkingPair) :
    splitDoubleCoverSignPair B S hS X F a p.swap =
      -(splitDoubleCoverSignPair B S hS X F a p) := by
  cases p
  · rfl
  · exact (neg_neg a).symm

/-- The section of an abelian sheaf over the split double cover of `X` which restricts to `a`
on the first summand and to `-a` on the second. -/
def splitDoubleCoverSignSection (a : F.obj.obj (Opposite.op (SpacesEtale.final B S hS X))) :
    F.obj.obj (Opposite.op (splitDoubleCover B S hS X)) :=
  (SpacesEtale.existsUnique_section_of_isColimit_cofan B S hS X F
    (splitDoubleCoverInj B S hS X) (isColimit_cofan_splitDoubleCover B S hS X)
    (splitDoubleCoverSignPair B S hS X F a)).choose

/-- The restrictions of the section glued from `(a, -a)`. -/
theorem splitDoubleCoverSignSection_restrict
    (a : F.obj.obj (Opposite.op (SpacesEtale.final B S hS X))) (p : WalkingPair) :
    F.obj.map (splitDoubleCoverInj B S hS X p).op (splitDoubleCoverSignSection B S hS X F a) =
      splitDoubleCoverSignPair B S hS X F a p :=
  (SpacesEtale.existsUnique_section_of_isColimit_cofan B S hS X F
    (splitDoubleCoverInj B S hS X) (isColimit_cofan_splitDoubleCover B S hS X)
    (splitDoubleCoverSignPair B S hS X F a)).choose_spec.1 p

/-- A section over the split double cover of `X` is determined by its two restrictions. -/
theorem splitDoubleCoverSection_ext
    (s t : F.obj.obj (Opposite.op (splitDoubleCover B S hS X)))
    (h : ∀ p, F.obj.map (splitDoubleCoverInj B S hS X p).op s =
      F.obj.map (splitDoubleCoverInj B S hS X p).op t) : s = t := by
  obtain ⟨w, -, huniq⟩ := SpacesEtale.existsUnique_section_of_isColimit_cofan B S hS X F
    (splitDoubleCoverInj B S hS X) (isColimit_cofan_splitDoubleCover B S hS X)
    (fun p => F.obj.map (splitDoubleCoverInj B S hS X p).op s)
  exact (huniq s fun _ => rfl).trans (huniq t fun p => (h p).symm).symm

/-- The section glued from `(a, -a)` transforms according to the identity character. -/
theorem splitDoubleCoverSignSection_mem
    (a : F.obj.obj (Opposite.op (SpacesEtale.final B S hS X))) :
    splitDoubleCoverSignSection B S hS X F a ∈
      characterSections (splitDoubleCover B S hS X).property
        (splitDoubleCoverActionHom_comp_proj B S hS X) (MonoidHom.id ℤˣ) F := by
  rw [mem_characterSections_splitDoubleCover_iff]
  refine splitDoubleCoverSection_ext B S hS X F _ _ fun p => ?_
  rw [map_splitDoubleCoverInj_map_swap, splitDoubleCoverSignSection_restrict,
    map_neg (F.obj.map (splitDoubleCoverInj B S hS X p).op).hom,
    splitDoubleCoverSignSection_restrict, splitDoubleCoverSignPair_swap]

/-- A section transforming according to the identity character restricts to opposite sections
on the two summands of the split double cover. -/
theorem map_splitDoubleCoverInr_of_mem
    (s : F.obj.obj (Opposite.op (splitDoubleCover B S hS X)))
    (hs : s ∈ characterSections (splitDoubleCover B S hS X).property
      (splitDoubleCoverActionHom_comp_proj B S hS X) (MonoidHom.id ℤˣ) F) :
    F.obj.map (splitDoubleCoverInj B S hS X WalkingPair.right).op s =
      -(F.obj.map (splitDoubleCoverInj B S hS X WalkingPair.left).op s) := by
  rw [mem_characterSections_splitDoubleCover_iff] at hs
  have h := map_splitDoubleCoverInj_map_swap B S hS X F WalkingPair.left s
  rw [hs, map_neg (F.obj.map (splitDoubleCoverInj B S hS X WalkingPair.left).op).hom] at h
  exact h.symm

/-- **The sections of an abelian sheaf over the split double cover of `X` transforming
according to the identity character of `ℤˣ` are the global sections of the sheaf.**

Such a section is a pair `(a, -a)`, and the pair is recovered from `a` alone. -/
def splitDoubleCoverCharacterSectionsEquiv :
    characterSections (splitDoubleCover B S hS X).property
        (splitDoubleCoverActionHom_comp_proj B S hS X) (MonoidHom.id ℤˣ) F ≃+
      F.obj.obj (Opposite.op (SpacesEtale.final B S hS X)) where
  toFun s := F.obj.map (splitDoubleCoverInj B S hS X WalkingPair.left).op s.1
  invFun a :=
    ⟨splitDoubleCoverSignSection B S hS X F a, splitDoubleCoverSignSection_mem B S hS X F a⟩
  left_inv s := by
    refine Subtype.ext (splitDoubleCoverSection_ext B S hS X F _ _ fun p => ?_)
    rw [splitDoubleCoverSignSection_restrict]
    cases p
    · rfl
    · exact (map_splitDoubleCoverInr_of_mem B S hS X F s.1 s.2).symm
  right_inv a := splitDoubleCoverSignSection_restrict B S hS X F a WalkingPair.left
  map_add' s t := map_add (F.obj.map (splitDoubleCoverInj B S hS X WalkingPair.left).op).hom _ _

/-- The identification of `H⁰(X ⊔ X, F)^χ` with `H⁰(X, F ⊗_ℤ ℤ)` for the identity character
`χ` of `ℤˣ`: both are the global sections of `F`. -/
def splitDoubleCoverSectionsEquiv :
    characterSections (splitDoubleCover B S hS X).property
        (splitDoubleCoverActionHom_comp_proj B S hS X) (MonoidHom.id ℤˣ) F ≃+
      (SpacesEtale.abelianSheafTensor B S hS X F
        ((constantSheaf (SpacesEtale.topology B S hS X) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).obj.obj
        (Opposite.op (SpacesEtale.final B S hS X)) :=
  (splitDoubleCoverCharacterSectionsEquiv B S hS X F).trans
    (CategoryTheory.Iso.addCommGroupIsoToAddEquiv
      (((evaluation (SpacesEtale B S hS X)ᵒᵖ AddCommGrpCat.{u + 1}).obj
          (Opposite.op (SpacesEtale.final B S hS X))).mapIso
        ((sheafToPresheaf (SpacesEtale.topology B S hS X) AddCommGrpCat.{u + 1}).mapIso
          (SpacesEtale.abelianSheafTensorConstantIso B S hS X F))))

end Sections

/-- **The hypothesis package of Stacks 0727 is satisfiable for a nontrivial group.**

Take for `W` the split double cover `X ⊔ X` of an algebraic space `X` over `S`, for `G` the
two-element group `ℤˣ` acting by the swap of the two summands, for the quotient `X` itself
with the fold map as its étale quotient morphism, for `χ` the identity character of `ℤˣ` —
the sign character of the swap — and for `ℤ(χ)` the constant sheaf `ℤ` on the spaces-étale
site of `X`.  Freeness holds in the form
`AlgebraicGeometry.Space.IsFreeOnNonemptyPoints` because the two summands are disjoint, and
the `χ`-semi-invariant sections of an abelian sheaf `F` over `X ⊔ X` are the pairs `(a, -a)`,
that is the global sections of `F` itself, which is also `H⁰(X, F ⊗_ℤ ℤ)`.

This matters because `AlgebraicGeometry.Space.SignTwistSetup` is a hypothesis package and
`AlgebraicGeometry.Space.SignTwistSetup.isQuasicoherentOnSite_twist`, which is Stacks 072A, is
universally quantified over it: without an inhabitant for a nontrivial group that statement
could be vacuous.  Compare
`AlgebraicGeometry.Space.forall_isCancelSMul_iff_subsingleton`, which shows that the stronger
freeness condition — cancellativity over *every* test object — forces the group to be
trivial.  The hypotheses carried here are only the standing parameters of Stacks 072A itself —
a big fppf site `B`, a scheme `S` contained in it — together with an algebraic space `X` over
`S`; and `AlgebraicGeometry.Space.terminalSpace` is such an `X`, namely the base `S`. -/
def signTwistSetupOfSwap :
    SignTwistSetup B S hS ℤˣ (splitDoubleCoverPresheaf B S hS X) (MonoidHom.id ℤˣ) where
  isAlgebraicSpace := ((splitDoubleCover B S hS X).obj.left).property
  natural := isNaturalAction_splitDoubleCover B S hS X
  free := isFreeOnNonemptyPoints_splitDoubleCover B S hS X
  quotient := X
  proj := (splitDoubleCover B S hS X).obj.hom
  isEtale_proj := (splitDoubleCover B S hS X).property
  actionHom_comp_proj := splitDoubleCoverActionHom_comp_proj B S hS X
  sheaf := (constantSheaf (SpacesEtale.topology B S hS X) AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  locallyFree := isLocallyFreeOfRankOne_constantSheaf B S hS X
  sectionsEquiv := splitDoubleCoverSectionsEquiv B S hS X

/-- **The hypothesis package of Stacks 072A is inhabited for a nontrivial group**, so the
universally quantified statement
`AlgebraicGeometry.Space.SignTwistSetup.isQuasicoherentOnSite_twist` is not vacuous.  The
group is `ℤˣ`, of order two, acting on the split double cover `X ⊔ X` by the swap of its two
summands. -/
theorem nontrivial_and_nonempty_signTwistSetup :
    Nontrivial ℤˣ ∧ Nonempty (SignTwistSetup B S hS ℤˣ
      (splitDoubleCoverPresheaf B S hS X) (MonoidHom.id ℤˣ)) :=
  ⟨⟨-1, 1, by decide⟩, ⟨signTwistSetupOfSwap B S hS X⟩⟩

end AlgebraicGeometry.Space

end
