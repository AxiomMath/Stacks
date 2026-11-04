module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Free sheaves of modules as associated sheaves

Let `(X, 𝒪_X)` be a ringed space and `α : R → Γ(X, 𝒪_X)` a ring homomorphism. The sheaf of
`𝒪_X`-modules associated to the free `R`-module on a type `I`, in the sense of construction (3)
of Stacks 01BH, is the free sheaf of `𝒪_X`-modules on `I`, compatibly with the generators.

## Main definitions

* `Stacks.AssociatedSheaf.sectionsEvalTop`: the sections of a sheaf of modules on a ringed space
  are its sections on the whole space.
* `Stacks.AssociatedSheaf.corepresentableIso`: two objects corepresenting the same functor are
  isomorphic, by an isomorphism whose underlying map is read off from the two bijections.
* `Stacks.AssociatedSheaf.freeIsoAssociatedSheaf`: the comparison
  `SheafOfModules.free I ≅ (I →₀ R)^~`.

## Main results

* `Stacks.AssociatedSheaf.freeIsoAssociatedSheaf_hom_app_top`: the comparison sends the `i`-th
  basis section of the free sheaf to the image of `Finsupp.single i 1` under the unit of the
  tensor-sheafification adjunction.
* `Stacks.AssociatedSheaf.preservesColimitsOfSize_associatedSheafFunctor`: clause (2) of Stacks
  01BH, that `M ↦ ℱ_M` commutes with arbitrary colimits.

## Implementation notes

Both sheaves corepresent the functor `𝒢 ↦ (I → Γ(X, 𝒢))` on sheaves of `𝒪_X`-modules: the free
sheaf by `SheafOfModules.freeHomEquiv`, and the associated sheaf by the adjunction
`Stacks.AssociatedSheaf.associatedSheafAdjunction` of Stacks 01BH(4) followed by the free-module
adjunction `ModuleCat.adj`. Comparing the two corepresentations is what makes the generator
identity available; constructing the comparison from colimit preservation instead would leave it
to be recovered from `IsColimit.coconePointUniqueUpToIso`.

`Mathlib.CategoryTheory.Functor.CorepresentableBy.uniqueUpToIso` is the same isomorphism, but its
`hom` is the preimage of a natural isomorphism under `Coyoneda.fullyFaithful`, from which the
value on a generator cannot be read; `corepresentableIso` is the same construction with the
`hom` given by the defining formula, which `homEquiv_corepresentableIso_hom` then states.

The module universe is taken equal to the universe of the ringed space. Universe generality is
not part of the source statement, and `associatedSheaf.{u, v}` lands in
`SheafOfModules.{max u v}`, so `v = u` is where it meets `SheafOfModules.{u}`, which is the
category `SheafOfModules.free` and `SheafOfModules.unit` live in here.

The two sheafification hypotheses of `SheafOfModules.free` are supplied by
`Stacks.AssociatedSheaf.hasModuleSheafify` and
`Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective`, declared local instances for
this file. They are theorems about every ringed space, so this is not an extra hypothesis.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.AssociatedSheaf

universe u v w

section Corepresentable

variable {D : Type w} [Category.{v} D] {F : D ⥤ Type u} {A B : D}

/-- Two objects corepresenting the same functor are isomorphic. Unlike
`CategoryTheory.Functor.CorepresentableBy.uniqueUpToIso`, the underlying map is given by the
defining formula, so that its effect on a universal element can be computed. -/
@[ega "0 8.1.11" "partial"]
def corepresentableIso (e : F.CorepresentableBy A) (e' : F.CorepresentableBy B) : A ≅ B where
  hom := e.homEquiv.symm (e'.homEquiv (𝟙 B))
  inv := e'.homEquiv.symm (e.homEquiv (𝟙 A))
  hom_inv_id := e.homEquiv.injective (by
    rw [e.homEquiv_comp, Equiv.apply_symm_apply, ← e'.homEquiv_comp, Category.id_comp,
      Equiv.apply_symm_apply])
  inv_hom_id := e'.homEquiv.injective (by
    rw [e'.homEquiv_comp, Equiv.apply_symm_apply, ← e.homEquiv_comp, Category.id_comp,
      Equiv.apply_symm_apply])

/-- The defining formula for `corepresentableIso`. -/
lemma homEquiv_corepresentableIso_hom (e : F.CorepresentableBy A) (e' : F.CorepresentableBy B) :
    e.homEquiv (corepresentableIso e e').hom = e'.homEquiv (𝟙 B) :=
  e.homEquiv.apply_symm_apply _

end Corepresentable

attribute [local instance] hasModuleSheafify moduleSheafifyWEqualsLocallyBijective

variable (X : RingedSpace.{u, u})

/-- The morphism in `(Opens X)ᵒᵖ` from the whole space to an open `U`, given by `U ≤ ⊤`. -/
def resTop (U : (Opens X.carrier)ᵒᵖ) : op (⊤ : Opens X.carrier) ⟶ U :=
  (homOfLE (show U.unop ≤ ⊤ from le_top)).op

/-- Composing `resTop X U` with a morphism `U ⟶ V` gives `resTop X V`. -/
lemma resTop_comp {U V : (Opens X.carrier)ᵒᵖ} (f : U ⟶ V) : resTop X U ≫ f = resTop X V :=
  Subsingleton.elim _ _

/-- `resTop` at the whole space is the identity. -/
lemma resTop_top : resTop X (op (⊤ : Opens X.carrier)) = 𝟙 _ := Subsingleton.elim _ _

variable (M : SheafOfModules.{u} (structureSheafRing X))

/-- The compatible family of restrictions of a section on the whole space. -/
def ofTop (x : M.val.obj (op ⊤)) : M.sections :=
  PresheafOfModules.sectionsMk (fun U ↦ M.val.map (resTop X U) x) (fun {U _} f ↦
    ((PresheafOfModules.map_comp_apply _ (resTop X U) f x).symm.trans
      (PresheafOfModules.congr_map_apply _ (resTop_comp X f) x)))

/-- A morphism of sheaves of modules sends the family of restrictions of a global section `x`
to the family of restrictions of the image of `x`. -/
lemma sectionsMap_ofTop {N : SheafOfModules.{u} (structureSheafRing X)}
    (g : M ⟶ N) (x : M.val.obj (op ⊤)) :
    SheafOfModules.sectionsMap g (ofTop X M x) = ofTop X N (g.val.app (op ⊤) x) := by
  ext U
  exact PresheafOfModules.naturality_apply g.val (resTop X U) x

/-- Since the whole space is the terminal open, a compatible family of sections of a sheaf of
modules on a ringed space is the same thing as a section on the whole space. -/
def sectionsEvalTop : M.sections ≃ (M.val.obj (op ⊤) : Type u) where
  toFun s := s.val (op ⊤)
  invFun x := ofTop X M x
  left_inv s := by
    ext U
    exact s.property (resTop X U)
  right_inv x := by
    refine (PresheafOfModules.congr_map_apply _ (resTop_top X) x).trans ?_
    rw [M.val.map_id]
    rfl

variable {X}

/-- The functor `𝒢 ↦ (I → Γ(X, 𝒢))`, corepresented both by the free sheaf of modules on `I` and
by the sheaf associated to the free module on `I`. -/
def freeGeneratorFunctor (I : Type u) :
    SheafOfModules.{u} (structureSheafRing X) ⥤ Type u where
  obj G := I → G.sections
  map {_ _} g := ↾(fun (s : I → _) i ↦ SheafOfModules.sectionsMap g (s i))

variable (X) {R : Type u} [CommRing R] (α : R →+* X.presheaf.obj (op ⊤))

/-- The free sheaf of modules on `I` corepresents `𝒢 ↦ (I → Γ(X, 𝒢))`. -/
def freeCorepresentable (I : Type u) :
    (freeGeneratorFunctor (X := X) I).CorepresentableBy
      (SheafOfModules.free (R := structureSheafRing X) I) where
  homEquiv {G} := SheafOfModules.freeHomEquiv G
  homEquiv_comp g f := by
    funext i
    exact SheafOfModules.freeHomEquiv_comp_apply f g i

/-- The sheaf associated to the free `R`-module on `I` corepresents `𝒢 ↦ (I → Γ(X, 𝒢))`: compose
the tensor-sheafification adjunction of Stacks 01BH(4) with the free-module adjunction. -/
def associatedSheafFreeCorepresentable (I : Type u) :
    (freeGeneratorFunctor (X := X) I).CorepresentableBy
      ((associatedSheafFunctor.{u, u} X α).obj ((ModuleCat.free R).obj I)) where
  homEquiv {G} :=
    ((associatedSheafAdjunction.{u, u} X α).homEquiv _ G).trans
      ((ModuleCat.freeHomEquiv.trans TypeCat.homEquiv).trans
        (Equiv.piCongrRight fun _ ↦
          (((sectionsEvalTop X G).symm :
            ((globalSectionsFunctor.{u, u} X α).obj G : Type u) ≃ G.sections))))
  homEquiv_comp {G G'} g f := by
    funext i
    dsimp only [Equiv.trans_apply, Equiv.piCongrRight_apply]
    rw [(associatedSheafAdjunction.{u, u} X α).homEquiv_naturality_right]
    exact (sectionsMap_ofTop X G g _).symm

/-- **Stacks 01BH.** The free sheaf of `𝒪_X`-modules on a type `I` is the sheaf associated to the
free `R`-module on `I`. -/
def freeIsoAssociatedSheaf (I : Type u) :
    SheafOfModules.free (R := structureSheafRing X) I ≅
      (associatedSheafFunctor.{u, u} X α).obj ((ModuleCat.free R).obj I) :=
  corepresentableIso (freeCorepresentable X I) (associatedSheafFreeCorepresentable X α I)

/-- The comparison `freeIsoAssociatedSheaf` carries the `i`-th basis section of the free sheaf of
modules to the image of `Finsupp.single i 1` under the unit of the tensor-sheafification
adjunction. -/
lemma freeIsoAssociatedSheaf_hom_app_top (I : Type u) (i : I) :
    (freeIsoAssociatedSheaf X α I).hom.val.app (op ⊤)
        ((SheafOfModules.ιFree (R := structureSheafRing X) i).val.app (op ⊤)
          (1 : (structureSheafRing X).obj.obj (op ⊤))) =
      (associatedSheafAdjunction.{u, u} X α).unit.app ((ModuleCat.free R).obj I)
        (Finsupp.single i (1 : R)) := by
  have h := congrFun
    (homEquiv_corepresentableIso_hom (freeCorepresentable X I)
      (associatedSheafFreeCorepresentable X α I)) i
  have h' := congrArg (fun s ↦ PresheafOfModules.sections.eval s (op ⊤)) h
  refine h'.trans ?_
  dsimp only [associatedSheafFreeCorepresentable, Equiv.trans_apply, Equiv.piCongrRight_apply]
  rw [(associatedSheafAdjunction.{u, u} X α).homEquiv_id]
  exact (sectionsEvalTop X _).right_inv _

/-- Construction (3) of Stacks 01BH is a left adjoint, by `associatedSheafAdjunction`, which is
clause (4) of the same tag. -/
theorem isLeftAdjoint_associatedSheafFunctor :
    (associatedSheafFunctor.{u, u} X α).IsLeftAdjoint :=
  (associatedSheafAdjunction.{u, u} X α).isLeftAdjoint

/-- The functor `M ↦ ℱ_M`, sending an `R`-module to the associated sheaf of `𝒪_X`-modules,
commutes with arbitrary colimits. -/
@[stacks 01BH "the functor M ↦ ℱ_M commutes with arbitrary colimits"]
instance preservesColimitsOfSize_associatedSheafFunctor :
    PreservesColimitsOfSize.{w, w} (associatedSheafFunctor.{u, max u v} X α) :=
  (associatedSheafAdjunction.{u, v} X α).leftAdjoint_preservesColimits

end Stacks.AssociatedSheaf
