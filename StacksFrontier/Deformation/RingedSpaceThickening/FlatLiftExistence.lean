module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.CategoryTheory.Functor.IsIsoMapOfHypothesis
public import StacksFrontier.Deformation.RingedSpaceThickening.ExistenceObstruction
public import StacksFrontier.Deformation.RingedSpaceThickening.FlatLift
import StacksCore.Tactic.StacksAttribute

/-!
# Existence of a flat lift across a strict morphism of first order thickenings (Stacks 08LN)

Let

```
X  --i-->  X'
|          |
f          f'
v          v
S  --t-->  S'
```

be a morphism of first order thickenings of ringed spaces (**Stacks 08KZ**) with ideal sheaves
`ℐ = ker(𝒪_{X'} ⟶ i_* 𝒪_X)` and `𝒥 = ker(𝒪_{S'} ⟶ t_* 𝒪_S)`, let the square be strict
(**Stacks 08L1**) and let `ℱ` be an `𝒪_X`-module flat over `S`. **Stacks 08LN** says that `ℱ`
has a lift to an `𝒪_{X'}`-module flat over `S'` — a flat lift in the sense of **Stacks 08LM** —
exactly when the canonical map `f^* 𝒥 ⊗_{𝒪_X} ℱ ⟶ ℐ ⊗_{𝒪_X} ℱ` is an isomorphism and the
obstruction class `o(ℱ, ℐ ⊗_{𝒪_X} ℱ, 1) ∈ Ext²_{𝒪_X}(ℱ, ℐ ⊗_{𝒪_X} ℱ)` of **Stacks 08L8**
vanishes.

Both directions go through the normalization `c = 1`. A flat lift has a kernel extension
`0 ⟶ i_*(ℐ ⊗_{𝒪_X} ℱ) ⟶ ℱ' ⟶ i_* ℱ ⟶ 0` whose canonical map of **Stacks 08L4** is the
identity, so the obstruction vanishes, and **Stacks 08LI** makes the canonical map invertible.
Conversely, for an extension whose canonical map is invertible the ideal action
`ℐ ⊗_{𝒪_{X'}} ℱ' ⟶ ℱ'` factors as an epimorphism onto `i_* 𝒦` followed by the injection of the
extension; the uniqueness of the epi-mono factorization identifies `i_* 𝒦` with the ideal
multiple `ℐℱ'`, which makes the reduction `ℱ' ⟶ i_* ℱ` a cokernel of the inclusion of `ℐℱ'`,
hence `i^* ℱ' ≅ ℱ`, and makes the second map of **Stacks 08LI** an isomorphism. The criterion of
**Stacks 08LI** then makes `ℱ'` flat over `S'`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.baseIdealTensorComparison_eq`: for `ℱ = i^* ℱ'` the
  canonical map `f^* 𝒥 ⊗_{𝒪_X} ℱ ⟶ ℐ ⊗_{𝒪_X} ℱ` of **Stacks 08LN**(1) is the first map of
  **Stacks 08LI**.
* `AlgebraicGeometry.RingedSpaceThickening.extensionIdealPairing`: the epimorphism
  `ℐ ⊗_{𝒪_{X'}} ℱ' ⟶ i_* 𝒦` through which the ideal action of an extension with invertible
  canonical map factors.
* `AlgebraicGeometry.RingedSpaceThickening.extensionInfinitesimalIso`: the resulting
  identification of the coefficient module `i_* 𝒦` with the ideal multiple `ℐℱ'`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.isoOfEpiMonoFac`: two epi-mono factorizations of one
  morphism of an abelian category are uniquely isomorphic.
* `AlgebraicGeometry.RingedSpaceThickening.isIso_homEquiv_symm_g_of_isIso_action`: the
  restriction `i^* ℱ'` of the middle term of an extension with invertible canonical map is
  isomorphic to `ℱ`.
* `AlgebraicGeometry.RingedSpaceThickening.isIso_restrictedIdealAction_of_isIso_action` and
  `AlgebraicGeometry.RingedSpaceThickening.isIso_sourceIdealActionImage_of_isIso_action`: for
  such an extension the second map of **Stacks 08LI** is an isomorphism.
* `AlgebraicGeometry.RingedSpaceThickening.nonempty_flatLift_iff`: **Stacks 08LN**.

## Implementation notes

The spellings `structureSheafRing` and
`structureSheafRing` of the structure sheaf of a ringed space agree by `rfl`
but only the former is reducible, so a morphism built from a tensor product and consumed by
`i_*` or `i^*` carries one of two `Category` instances that are not interchangeable at the
transparency at which `rw` matches and typeclass synthesis fires. Every step that would need
such a match is therefore routed through a lemma stated over clean variables in an abstract
category — `isIso_of_eq`, `epi_of_eq`, `epi_comp_of_epi`, `isIso_comp_of_isIso`,
`CategoryTheory.Functor.isIso_map_of_isIso`, `epi_of_isIso`, `isIso_of_epi_fac`, `isoOfEpiMonoFac` — and applied in
term mode.

## References

* [Stacks Project, Tag 08LN](https://stacks.math.columbia.edu/tag/08LN)
* [Stacks Project, Tag 08LM](https://stacks.math.columbia.edu/tag/08LM)
* [Stacks Project, Tag 08LI](https://stacks.math.columbia.edu/tag/08LI)
* [Stacks Project, Tag 08L8](https://stacks.math.columbia.edu/tag/08L8)
* [Stacks Project, Tag 08L4](https://stacks.math.columbia.edu/tag/08L4)
* [Stacks Project, Tag 08L1](https://stacks.math.columbia.edu/tag/08L1)
* [Stacks Project, Tag 08KZ](https://stacks.math.columbia.edu/tag/08KZ)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
  TopCat.Presheaf.IsSheaf PresheafOfModules.tensorObj

/- Every tensor product here is matched against the composite of bifunctors that
`Stacks.RingedSpace.comparisonBifunctorIso` produces, and that reconciliation is one `isDefEq`
which does not terminate within the heartbeat budget while
`Stacks.SheafOfModules.Tensor.sheafTensor` is transparent: each traversal re-unfolds it and
re-reduces the sheafification underneath. The section computations below go through
`toTensorSheafSection` and `tensorSheafMap_app_toTensorSheafSection`, which treat the tensor
product as an object, so the bifunctor can be opaque throughout -- the recipe of
ModuleExtension.lean:318 from this same migration. Nothing about the terms produced changes. -/
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

/-! ### Categorical steps over clean variables

Each statement in this section is a one-line fact about an abstract category, taking its
hypotheses as explicit arguments rather than as instances. That is what lets it be applied, in
term mode, to a morphism whose `Category` instance is one of the two interchangeable spellings
of the structure sheaf of a ringed space. -/

section Clean

variable {C : Type*} [Category C]

/-- Invertibility transports along an equality of morphisms. -/
theorem isIso_of_eq {A B : C} {f g : A ⟶ B} (h : f = g) (hf : IsIso f) : IsIso g := by
  rw [← h]; exact hf

/-- Being an epimorphism transports along an equality of morphisms. -/
theorem epi_of_eq {A B : C} {f g : A ⟶ B} (h : f = g) (hf : Epi f) : Epi g := by
  rw [← h]; exact hf

/-- An isomorphism is an epimorphism. -/
theorem epi_of_isIso {A B : C} (f : A ⟶ B) (hf : IsIso f) : Epi f := by
  have := hf; infer_instance

/-- A composite of epimorphisms is an epimorphism. -/
theorem epi_comp_of_epi {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (hf : Epi f) (hg : Epi g) :
    Epi (f ≫ g) := by
  have := hf; have := hg; infer_instance

/-- A composite of isomorphisms is an isomorphism. -/
theorem isIso_comp_of_isIso {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (hf : IsIso f) (hg : IsIso g) :
    IsIso (f ≫ g) := by
  have := hf; have := hg; infer_instance

/-- A functor carries a composite whose two factors it inverts to an isomorphism. -/
theorem isIso_map_of_eq_comp {D' : Type*} [Category D'] (G : C ⥤ D') {A B E : C} {p : A ⟶ E}
    (u : A ⟶ B) (v : B ⟶ E) (h : p = u ≫ v) (hu : IsIso (G.map u)) (hv : IsIso (G.map v)) :
    IsIso (G.map p) := by
  have := hu
  have := hv
  rw [h, G.map_comp]
  infer_instance

/-- If a morphism and a composite with it on the left are invertible, so is the other factor. -/
theorem isIso_of_isIso_comp_left {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (hf : IsIso f)
    (hfg : IsIso (f ≫ g)) : IsIso g := by
  have := hf; have := hfg; exact IsIso.of_isIso_comp_left f g

/-- If a morphism and a composite with it on the right are invertible, so is the other
factor. -/
theorem isIso_of_isIso_comp_right {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (hg : IsIso g)
    (hfg : IsIso (f ≫ g)) : IsIso f := by
  have := hg; have := hfg; exact IsIso.of_isIso_comp_right f g

/-- **A map between two quotients of one object is invertible if both quotients factor through
each other.** For epimorphisms `p` and `q` out of the same object, a map `α` with `p ≫ α = q`
and a map `β` with `q ≫ β = p` are mutually inverse. -/
theorem isIso_of_epi_fac {B P Q : C} (p : B ⟶ P) (q : B ⟶ Q) (hp : Epi p) (hq : Epi q)
    (α : P ⟶ Q) (β : Q ⟶ P) (hα : p ≫ α = q) (hβ : q ≫ β = p) : IsIso α := by
  have := hp
  have := hq
  refine ⟨⟨β, ?_, ?_⟩⟩
  · refine (cancel_epi p).1 ?_
    rw [Category.comp_id, ← Category.assoc, hα, hβ]
  · refine (cancel_epi q).1 ?_
    rw [Category.comp_id, ← Category.assoc, hβ, hα]

/-- **Two epi-mono factorizations of one morphism of an abelian category are uniquely
isomorphic**: there is an isomorphism of the two intermediate objects carrying the one
monomorphism to the other and the one epimorphism to the other. -/
noncomputable def isoOfEpiMonoFac [Abelian C] {A B I₁ I₂ : C} {f : A ⟶ B}
    (e₁ : A ⟶ I₁) (m₁ : I₁ ⟶ B) (h₁ : e₁ ≫ m₁ = f) (he₁ : Epi e₁) (hm₁ : Mono m₁)
    (e₂ : A ⟶ I₂) (m₂ : I₂ ⟶ B) (h₂ : e₂ ≫ m₂ = f) (he₂ : Epi e₂) (hm₂ : Mono m₂) :
    { θ : I₁ ≅ I₂ // θ.hom ≫ m₂ = m₁ ∧ e₁ ≫ θ.hom = e₂ } :=
  haveI := he₁
  haveI := hm₁
  haveI := he₂
  haveI := hm₂
  haveI : StrongEpi e₁ := strongEpi_of_epi e₁
  haveI : StrongEpi e₂ := strongEpi_of_epi e₂
  let a := image.isoStrongEpiMono e₁ m₁ h₁
  let b := image.isoStrongEpiMono e₂ m₂ h₂
  have ha : a.hom ≫ image.ι f = m₁ := image.isoStrongEpiMono_hom_comp_ι e₁ m₁ h₁
  have hb : b.hom ≫ image.ι f = m₂ := image.isoStrongEpiMono_hom_comp_ι e₂ m₂ h₂
  have hmain : (a ≪≫ b.symm).hom ≫ m₂ = m₁ :=
    (Category.assoc a.hom b.inv m₂).trans
      ((congrArg (fun z => a.hom ≫ b.inv ≫ z) hb.symm).trans
        ((congrArg (fun z => a.hom ≫ z) (b.inv_hom_id_assoc (image.ι f))).trans ha))
  ⟨a ≪≫ b.symm, hmain,
    (cancel_mono m₂).1 (((Category.assoc e₁ (a ≪≫ b.symm).hom m₂).trans
      (congrArg (fun z => e₁ ≫ z) hmain)).trans (h₁.trans h₂.symm))⟩

end Clean

/-! ### Bifunctoriality of the tensor product -/

/-- **Bifunctoriality of the tensor product of sheaves of modules.** Applying a map in the first
factor commutes with applying a map in the second. -/
theorem tensorSheafMap_id_comm {Y : RingedSpace.{u, u}}
    {A B C E : SheafOfModules.{u} (structureSheafRing Y)} (φ : A ⟶ B) (ψ : C ⟶ E) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨Y.presheaf, Y.IsSheaf⟩ : Sheaf (JX Y) CommRingCat.{u}))).map ((φ, (𝟙 C)) : (_, _) ⟶ (_, _))) ≫ ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨Y.presheaf, Y.IsSheaf⟩ : Sheaf (JX Y) CommRingCat.{u}))).map (((𝟙 B), ψ) : (_, _) ⟶ (_, _))) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨Y.presheaf, Y.IsSheaf⟩ : Sheaf (JX Y) CommRingCat.{u}))).map (((𝟙 A), ψ) : (_, _) ⟶ (_, _))) ≫ ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨Y.presheaf, Y.IsSheaf⟩ : Sheaf (JX Y) CommRingCat.{u}))).map ((φ, (𝟙 E)) : (_, _) ⟶ (_, _))) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-! ### The canonical map of the first condition -/

/-- For the restriction of a module on `X'` the canonical map of **Stacks 08LN**(1) is the first
of the two maps whose composite **Stacks 08LI** inverts. -/
theorem baseIdealTensorComparison_eq (D : MorphismOfThickenings.{u})
    (F' : SheafOfModules.{u} (structureSheafRing D.X')) :
    baseIdealTensorComparison D ((modulePullback D.i).obj F') =
      baseToSourceIdealTensor D F' := rfl

/-- The canonical map of **Stacks 08LN**(1) is natural in the module. -/
theorem baseIdealTensorComparison_naturality (D : MorphismOfThickenings.{u})
    {F G : SheafOfModules.{u} (structureSheafRing D.X)} (e : F ⟶ G) :
    baseIdealTensorComparison D F ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨D.X.presheaf, D.X.IsSheaf⟩ : Sheaf (JX D.X) CommRingCat.{u}))).map (((𝟙 ((modulePullback D.i).obj D.idealI)), e) : (_, _) ⟶ (_, _))) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨D.X.presheaf, D.X.IsSheaf⟩ : Sheaf (JX D.X) CommRingCat.{u}))).map (((𝟙 ((modulePullback D.f).obj ((modulePullback D.t).obj D.idealJ))), e) : (_, _) ⟶ (_, _))) ≫
        baseIdealTensorComparison D G :=
  tensorSheafMap_id_comm D.baseToSourceIdeal e

/-- **Invertibility of the canonical map of Stacks 08LN(1) depends only on the isomorphism class
of the module**: the map is natural, and tensoring an isomorphism with the identity gives an
isomorphism. -/
theorem isIso_baseIdealTensorComparison_of_iso (D : MorphismOfThickenings.{u})
    {F G : SheafOfModules.{u} (structureSheafRing D.X)} (e : F ≅ G)
    (hF : IsIso (baseIdealTensorComparison D F)) :
    IsIso (baseIdealTensorComparison D G) :=
  isIso_of_isIso_comp_left
    _
    (baseIdealTensorComparison D G)
    (isIso_tensorSheafMap_id_left _ e.hom e.isIso_hom)
    (isIso_of_eq (baseIdealTensorComparison_naturality D e.hom)
      (isIso_comp_of_isIso _ _ hF (isIso_tensorSheafMap_id_left _ e.hom e.isIso_hom)))

/-! ### The ideal action of an extension with invertible canonical map -/

section Extension

variable {X X' : RingedSpace.{u, u}} (i : X ⟶ X')

/-- **The comparison of Stacks 08L4 is an epimorphism.** It is the adjoint transpose of an
isomorphism, hence the unit of `i^* ⊣ i_*` followed by the direct image of an isomorphism, and
the unit is an epimorphism across a thickening. -/
theorem epi_extensionTensorComparison (hi : IsThickening i)
    (F : SheafOfModules.{u} (structureSheafRing X)) : Epi (extensionTensorComparison i F) :=
  epi_of_eq
    ((modulePullbackPushforwardAdjunction i).homEquiv_unit _ _
      (extensionTensorIso i hi F).hom).symm
    (epi_comp_of_epi _ _
      (epi_unit_app_of_isThickening i hi
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨X'.presheaf, X'.IsSheaf⟩ : Sheaf (JX X') CommRingCat.{u})).obj ((AlgebraicGeometry.SheafOfModules.idealSheaf i))).obj (((modulePushforward i).obj F)))))
      (epi_of_isIso _
        ((modulePushforward i).mapIso (extensionTensorIso i hi F)).isIso_hom))

/-- The factorization of the ideal action through the ideal multiple is an epimorphism: it is the
factorization of the action through its image followed by an isomorphism. -/
theorem epi_idealMultipleFactor (hi : IsThickening i)
    (M : SheafOfModules.{u} (structureSheafRing X')) : Epi (idealMultipleFactor i hi M) :=
  epi_comp_of_epi (Abelian.factorThruImage (idealAction i M))
    (idealMultipleIso i hi M).1.hom inferInstance
    (epi_of_isIso _ (idealMultipleIso i hi M).1.isIso_hom)

variable (hi : IsFirstOrderThickening i) (F K : SheafOfModules.{u} (structureSheafRing X))
  (E : CategoryTheory.Abelian.YonedaExtension
    ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0)

/-- **The factorization of the ideal action of an extension through its coefficient module**:
the tensor of the surjection of the extension, the comparison of **Stacks 08L4** and the direct
image of the canonical map of **Stacks 08L4**. -/
noncomputable def extensionIdealPairing :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨X'.presheaf, X'.IsSheaf⟩ : Sheaf (JX X') CommRingCat.{u})).obj ((AlgebraicGeometry.SheafOfModules.idealSheaf i))).obj (E.Z.left)) ⟶
      (modulePushforward i).obj K :=
  ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨X'.presheaf, X'.IsSheaf⟩ : Sheaf (JX X') CommRingCat.{u}))).map (((𝟙 (AlgebraicGeometry.SheafOfModules.idealSheaf i)), E.g) : (_, _) ⟶ (_, _))) ≫
    extensionTensorComparison i F ≫
      (modulePushforward i).map (firstOrderExtensionAction i F K hi E).val

/-- The factorization composed with the injection of the extension is the ideal action: this is
the defining equation of the canonical map of **Stacks 08L4**. -/
theorem extensionIdealPairing_comp_f :
    extensionIdealPairing i hi F K E ≫ E.f = idealAction i E.Z.left :=
  (Category.assoc _ _ _).trans (firstOrderExtensionAction_comp i F K hi E)

/-- The factorization of the ideal action is the unit of `i^* ⊣ i_*` followed by the direct
image of the **Stacks 01CD** comparison, the tensor of the adjoint transpose of the surjection
and the canonical map of **Stacks 08L4**. -/
theorem extensionIdealPairing_eq :
    extensionIdealPairing i hi F K E =
      (modulePullbackPushforwardAdjunction i).unit.app
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨X'.presheaf, X'.IsSheaf⟩ : Sheaf (JX X') CommRingCat.{u})).obj ((AlgebraicGeometry.SheafOfModules.idealSheaf i))).obj (E.Z.left))) ≫
        (modulePushforward i).map
            ((Stacks.RingedSpace.comparisonBifunctorIso i).hom.app
                (AlgebraicGeometry.SheafOfModules.idealSheaf i, E.Z.left) ≫
              ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map (((𝟙 (idealSheafPullback i)), (((modulePullbackPushforwardAdjunction i).homEquiv E.Z.left F).symm E.g)) : (_, _) ⟶ (_, _)))) ≫
        (modulePushforward i).map (firstOrderExtensionAction i F K hi E).val :=
  (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ (modulePushforward i).map (firstOrderExtensionAction i F K hi E).val)
      ((tensorSheafMap_comp_extensionTensorComparison i E.g).trans
        ((modulePullbackPushforwardAdjunction i).homEquiv_unit _ _ _))).trans
      (Category.assoc _ _ _)

/-- **The factorization of the ideal action is an epimorphism** when the canonical map of
**Stacks 08L4** is invertible: the tensor of an epimorphism is one, the comparison of
**Stacks 08L4** is one, and the direct image of an isomorphism is one. -/
theorem epi_extensionIdealPairing
    (hact : IsIso (firstOrderExtensionAction i F K hi E).val) :
    Epi (extensionIdealPairing i hi F K E) :=
  epi_comp_of_epi
    _
    (extensionTensorComparison i F ≫
      (modulePushforward i).map (firstOrderExtensionAction i F K hi E).val)
    (idealTensorFunctor_epi i E.g E.epi_g)
    (epi_comp_of_epi (extensionTensorComparison i F)
      ((modulePushforward i).map (firstOrderExtensionAction i F K hi E).val)
      (epi_extensionTensorComparison i hi.1 F)
      (epi_of_isIso _ (CategoryTheory.Functor.isIso_map_of_isIso (modulePushforward i) _ hact)))

/-- **The coefficient module of an extension whose canonical map is invertible is its ideal
multiple.** The ideal action of the extension factors as an epimorphism onto `i_* 𝒦` followed by
the injection of the extension, and as the factorization through `ℐℱ'` followed by its
inclusion; the two epi-mono factorizations of one morphism are uniquely isomorphic. -/
noncomputable def extensionInfinitesimalIso
    (hact : IsIso (firstOrderExtensionAction i F K hi E).val) :
    { e : (modulePushforward i).obj K ≅ infinitesimalPart i E.Z.left //
      e.hom ≫ infinitesimalι i E.Z.left = E.f ∧
        extensionIdealPairing i hi F K E ≫ e.hom =
          idealMultipleFactor i hi.1 E.Z.left } :=
  isoOfEpiMonoFac
    (extensionIdealPairing i hi F K E) E.f (extensionIdealPairing_comp_f i hi F K E)
    (epi_extensionIdealPairing i hi F K E hact) E.mono_f
    (idealMultipleFactor i hi.1 E.Z.left) (infinitesimalι i E.Z.left)
    ((idealMultipleFactor_comp_infinitesimalι i hi.1 E.Z.left).trans
      (idealActionNatTrans_app i E.Z.left))
    (epi_idealMultipleFactor i hi.1 E.Z.left) (mono_infinitesimalι i E.Z.left)

/-- **The restriction of the middle term of an extension whose canonical map is invertible is
`ℱ`.** The coefficient module is the ideal multiple `ℐℱ'`, which is the kernel of the reduction
`ℱ' ⟶ i_* i^* ℱ'`, so the reduction factors through the surjection of the extension; the
surjection factors through the reduction because the extension is a cokernel. Each factorization
is the direct image of the adjoint transpose of the surjection or its inverse, and `i_*` reflects
isomorphisms across a thickening. -/
theorem isIso_homEquiv_symm_g_of_isIso_action
    (hact : IsIso (firstOrderExtensionAction i F K hi E).val) :
    IsIso (((modulePullbackPushforwardAdjunction i).homEquiv E.Z.left F).symm E.g) := by
  obtain ⟨e, hef, -⟩ := extensionInfinitesimalIso i hi F K E hact
  have : (modulePushforward i).Full :=
    (closedQuotientOfIsThickening i hi.1).full_modulePushforward
  have : (modulePushforward i).Faithful :=
    (closedQuotientOfIsThickening i hi.1).faithful_modulePushforward
  have hcond : infinitesimalι i E.Z.left ≫
      (modulePullbackPushforwardAdjunction i).unit.app E.Z.left = 0 :=
    kernel.condition ((modulePullbackPushforwardAdjunction i).unit.app E.Z.left)
  have hfunit : E.f ≫ (modulePullbackPushforwardAdjunction i).unit.app E.Z.left = 0 := by
    rw [← hef, Category.assoc, hcond, comp_zero]
  have hextensionExact : (ShortComplex.mk E.f E.g
      (CategoryTheory.Abelian.YonedaExtension.comp_eq_zero E)).ShortExact :=
    CategoryTheory.Abelian.YonedaExtension.shortExact E
  have : IsIso ((modulePushforward i).map
      (((modulePullbackPushforwardAdjunction i).homEquiv E.Z.left F).symm E.g)) :=
    isIso_of_epi_fac ((modulePullbackPushforwardAdjunction i).unit.app E.Z.left) E.g
      (epi_unit_app_of_isThickening i hi.1 E.Z.left) E.epi_g
      ((modulePushforward i).map
        (((modulePullbackPushforwardAdjunction i).homEquiv E.Z.left F).symm E.g))
      (hextensionExact.gIsCokernel.desc (CokernelCofork.ofπ
        ((modulePullbackPushforwardAdjunction i).unit.app E.Z.left) hfunit))
      (((modulePullbackPushforwardAdjunction i).homEquiv E.Z.left F).apply_symm_apply E.g)
      (hextensionExact.gIsCokernel.fac _ WalkingParallelPair.one)
  exact isIso_of_reflects_iso _ (modulePushforward i)

end Extension

/-! ### The ideal action on the reduced source -/

/-- **The second map of Stacks 08LI is an isomorphism for an extension whose canonical map is
invertible.** The ideal action on the reduced source is `i^*` of the factorization through the
ideal multiple, which is the factorization of the ideal action of the extension followed by the
identification of the coefficient module with the ideal multiple. The first of these is `i^*` of
the unit of `i^* ⊣ i_*` followed by `i^*` of a direct image of an isomorphism, and `i^*` of the
unit is invertible because the counit is. -/
theorem isIso_restrictedIdealAction_of_isIso_action (D : MorphismOfThickenings.{u})
    (hi : IsFirstOrderThickening D.i) (F K : SheafOfModules.{u} (structureSheafRing D.X))
    (E : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward D.i).obj F) ((modulePushforward D.i).obj K) 0)
    (hact : IsIso (firstOrderExtensionAction D.i F K hi E).val) :
    IsIso (restrictedIdealAction D E.Z.left) := by
  obtain ⟨e, -, hpair⟩ := extensionInfinitesimalIso D.i hi F K E hact
  have hpair' : extensionIdealPairing D.i hi F K E ≫ e.hom =
      idealMultipleFactor D.i D.i_isThickening E.Z.left := hpair
  have hcmp : IsIso ((Stacks.RingedSpace.comparisonBifunctorIso D.i).hom.app
    (AlgebraicGeometry.SheafOfModules.idealSheaf D.i, E.Z.left)) := inferInstance
  have hunit : IsIso ((modulePullback D.i).map
      ((modulePullbackPushforwardAdjunction D.i).unit.app
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨D.X'.presheaf, D.X'.IsSheaf⟩ : Sheaf (JX D.X') CommRingCat.{u})).obj ((AlgebraicGeometry.SheafOfModules.idealSheaf D.i))).obj (E.Z.left))))) :=
    isIso_of_isIso_comp_right _
      ((modulePullbackPushforwardAdjunction D.i).counit.app
        ((modulePullback D.i).obj
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨D.X'.presheaf, D.X'.IsSheaf⟩ : Sheaf (JX D.X') CommRingCat.{u})).obj ((AlgebraicGeometry.SheafOfModules.idealSheaf D.i))).obj (E.Z.left)))))
      (isIso_counit_app D.i D.i_isThickening _)
      (isIso_of_eq
        ((modulePullbackPushforwardAdjunction D.i).left_triangle_components _).symm
        (IsIso.id _))
  have htail : IsIso ((modulePullback D.i).map
      ((modulePushforward D.i).map
          ((Stacks.RingedSpace.comparisonBifunctorIso D.i).hom.app
              (AlgebraicGeometry.SheafOfModules.idealSheaf D.i, E.Z.left) ≫
            ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (⟨D.X.presheaf, D.X.IsSheaf⟩ : Sheaf (JX D.X) CommRingCat.{u}))).map (((𝟙 (idealSheafPullback D.i)), (((modulePullbackPushforwardAdjunction D.i).homEquiv E.Z.left F).symm E.g)) : (_, _) ⟶ (_, _)))) ≫
        (modulePushforward D.i).map (firstOrderExtensionAction D.i F K hi E).val)) :=
    CategoryTheory.Functor.isIso_map_of_isIso (modulePullback D.i) _
      (isIso_comp_of_isIso _ _
        (CategoryTheory.Functor.isIso_map_of_isIso (modulePushforward D.i) _
          (isIso_comp_of_isIso _ _ hcmp
            (isIso_tensorSheafMap_id_left (idealSheafPullback D.i) _
              (isIso_homEquiv_symm_g_of_isIso_action D.i hi F K E hact))))
        (CategoryTheory.Functor.isIso_map_of_isIso (modulePushforward D.i) _ hact))
  have hpairing : IsIso ((modulePullback D.i).map (extensionIdealPairing D.i hi F K E)) :=
    isIso_map_of_eq_comp (modulePullback D.i) _ _
      (extensionIdealPairing_eq D.i hi F K E) hunit htail
  exact isIso_of_eq (restrictedIdealAction_eq D E.Z.left).symm
    (isIso_map_of_eq_comp (modulePullback D.i) (extensionIdealPairing D.i hi F K E) e.hom
      hpair'.symm hpairing (CategoryTheory.Functor.isIso_map_of_isIso (modulePullback D.i) _ e.isIso_hom))

/-- **The second map of Stacks 08LI, read before the Stacks 01CD comparison, is an isomorphism
for an extension whose canonical map is invertible.** -/
theorem isIso_sourceIdealActionImage_of_isIso_action (D : MorphismOfThickenings.{u})
    (hi : IsFirstOrderThickening D.i) (F K : SheafOfModules.{u} (structureSheafRing D.X))
    (E : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward D.i).obj F) ((modulePushforward D.i).obj K) 0)
    (hact : IsIso (firstOrderExtensionAction D.i F K hi E).val) :
    IsIso (sourceIdealActionImage D E.Z.left) :=
  isIso_of_isIso_comp_left
    ((Stacks.RingedSpace.comparisonBifunctorIso D.i).hom.app (D.idealI, E.Z.left))
    (sourceIdealActionImage D E.Z.left) inferInstance
    (isIso_restrictedIdealAction_of_isIso_action D hi F K E hact)

/-! ### The flat lift carried by an extension -/

/-- **The flat lift carried by an extension with invertible canonical map.** Let `E` be an
extension `0 ⟶ i_*(ℐ ⊗_{𝒪_X} ℱ) ⟶ ℱ' ⟶ i_* ℱ ⟶ 0` whose canonical map of **Stacks 08L4** is
invertible, and assume the canonical map `f^* 𝒥 ⊗_{𝒪_X} ℱ ⟶ ℐ ⊗_{𝒪_X} ℱ` is an isomorphism.
Then the adjoint transpose of the surjection identifies `i^* ℱ'` with `ℱ`, and the criterion of
**Stacks 08LI** makes `ℱ'` flat over `S'`. -/
noncomputable def FlatLift.ofExtension (D : MorphismOfThickenings.{u})
    (hi : IsFirstOrderThickening D.i) (ht : IsFirstOrderThickening D.t) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)}
    (hF : AlgebraicGeometry.IsFlatOver D.f F) (hcomp : IsIso (baseIdealTensorComparison D F))
    (E : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward D.i).obj F) ((modulePushforward D.i).obj (idealTensor D F)) 0)
    (hact : IsIso (firstOrderExtensionAction D.i F (idealTensor D F) hi E).val) :
    FlatLift D F :=
  let q : (modulePullback D.i).obj E.Z.left ≅ F :=
    @asIso _ _ _ _ (((modulePullbackPushforwardAdjunction D.i).homEquiv E.Z.left F).symm E.g)
      (isIso_homEquiv_symm_g_of_isIso_action D.i hi F (idealTensor D F) E hact)
  have hrestr : AlgebraicGeometry.IsFlatOver D.f ((modulePullback D.i).obj E.Z.left) :=
    (AlgebraicGeometry.isFlatOver_iff_of_moduleIso D.f q).2 hF
  { module' := E.Z.left
    flat := (isFlatOver_iff_baseToInfinitesimal_isIso D hi ht hs E.Z.left hrestr).2
      (isIso_comp_of_isIso (baseToSourceIdealTensor D E.Z.left)
        (sourceIdealActionImage D E.Z.left)
        (isIso_baseIdealTensorComparison_of_iso D q.symm hcomp)
        (isIso_sourceIdealActionImage_of_isIso_action D hi F (idealTensor D F) E hact))
    identification := q }

/-- The module of the flat lift carried by an extension is the middle term of the
extension. -/
theorem FlatLift.ofExtension_module' (D : MorphismOfThickenings.{u})
    (hi : IsFirstOrderThickening D.i) (ht : IsFirstOrderThickening D.t) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)}
    (hF : AlgebraicGeometry.IsFlatOver D.f F) (hcomp : IsIso (baseIdealTensorComparison D F))
    (E : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward D.i).obj F) ((modulePushforward D.i).obj (idealTensor D F)) 0)
    (hact : IsIso (firstOrderExtensionAction D.i F (idealTensor D F) hi E).val) :
    (FlatLift.ofExtension D hi ht hs hF hcomp E hact).module' = E.Z.left := rfl

/-- **An extension normalized by `c = 1` is a kernel extension of the flat lift it carries.**
The canonical surjection of that lift is the adjoint transpose of its identification, which is
the surjection of the extension. -/
theorem FlatLift.isKernelExtension_ofExtension (D : MorphismOfThickenings.{u})
    (hi : IsFirstOrderThickening D.i) (ht : IsFirstOrderThickening D.t) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)}
    (hF : AlgebraicGeometry.IsFlatOver D.f F) (hcomp : IsIso (baseIdealTensorComparison D F))
    (E : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward D.i).obj F) ((modulePushforward D.i).obj (idealTensor D F)) 0)
    (hact : (firstOrderExtensionAction D.i F (idealTensor D F) hi E).val =
      𝟙 (idealTensor D F)) :
    (FlatLift.ofExtension D hi ht hs hF hcomp E
      (isIso_of_eq hact.symm (IsIso.id _))).IsKernelExtension hi E := by
  refine ⟨hact, Iso.refl _, ?_⟩
  refine (Category.id_comp _).trans ?_
  exact ((modulePullbackPushforwardAdjunction D.i).homEquiv_unit E.Z.left F _).symm.trans
    (((modulePullbackPushforwardAdjunction D.i).homEquiv E.Z.left F).apply_symm_apply E.g)

/-! ### The criterion -/

/-- **Stacks Project, Tag 08LN.** Let `(f, f')` be a strict morphism of first order thickenings
of ringed spaces and let `ℱ` be an `𝒪_X`-module flat over `S`. There is an `𝒪_{X'}`-module `ℱ'`
flat over `S'` with `i^* ℱ' ≅ ℱ` if and only if the canonical map
`f^* 𝒥 ⊗_{𝒪_X} ℱ ⟶ ℐ ⊗_{𝒪_X} ℱ` is an isomorphism and the class
`o(ℱ, ℐ ⊗_{𝒪_X} ℱ, 1) ∈ Ext²_{𝒪_X}(ℱ, ℐ ⊗_{𝒪_X} ℱ)` of **Stacks 08L8** is zero.

The pair `(ℱ', α)` of the source is
`AlgebraicGeometry.RingedSpaceThickening.FlatLift`, and the obstruction class is
`AlgebraicGeometry.RingedSpaceThickening.obstructionClass` for the coefficient module
`ℐ ⊗_{𝒪_X} ℱ` and the normalization `c = 1`. -/
@[stacks 08LN]
theorem nonempty_flatLift_iff (D : MorphismOfThickenings.{u})
    [HasExt (SheafOfModules.{u} (structureSheafRing D.X))]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing D.X))]
    (hi : IsFirstOrderThickening D.i) (ht : IsFirstOrderThickening D.t) (hs : D.IsStrict)
    (F : SheafOfModules.{u} (structureSheafRing D.X))
    (hF : AlgebraicGeometry.IsFlatOver D.f F) :
    Nonempty (FlatLift D F) ↔
      IsIso (baseIdealTensorComparison D F) ∧
        obstructionClass D.i hi F (idealTensor D F) (𝟙 (idealTensor D F)) = 0 := by
  constructor
  · rintro ⟨A⟩
    have hrestr : AlgebraicGeometry.IsFlatOver D.f ((modulePullback D.i).obj A.module') :=
      (AlgebraicGeometry.isFlatOver_iff_of_moduleIso D.f A.identification).2 hF
    refine ⟨isIso_baseIdealTensorComparison_of_iso D A.identification
      (baseToSourceIdealTensor_isIso D hi ht hs A.module' hrestr A.flat), ?_⟩
    exact (obstructionClass_eq_zero_iff D.i hi F (idealTensor D F) _).2
      ⟨A.kernelExtension hi hs, A.kernelExtension_action hi hs⟩
  · rintro ⟨hcomp, hobs⟩
    obtain ⟨E, hE⟩ := (obstructionClass_eq_zero_iff D.i hi F (idealTensor D F) _).1 hobs
    exact ⟨FlatLift.ofExtension D hi ht hs hF hcomp E (isIso_of_eq hE.symm (IsIso.id _))⟩

end AlgebraicGeometry.RingedSpaceThickening

end
