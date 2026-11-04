module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearYoneda
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforward

/-!
# Bilinear maps of module objects over a ring object

Let `C` be a category with finite products, i.e. a cartesian monoidal category, let `R` be a ring
object of `C` (`CategoryTheory.RingObj`) and let `F`, `G`, `H` be module objects over it
(`CategoryTheory.ModuleObj`). A morphism `f : F ⊗ G ⟶ H` is *bilinear* when it is additive and
compatible with the action of `R` in each argument; each of the four conditions is a commuting
diagram in `C`, imitating the axioms of a bilinear map of modules.

For a sheaf of commutative rings `O` on a site, the underlying sheaf of sets of `O` is a ring
object of the category of sheaves of sets (`Stacks.sheafCommRingObj`) and the underlying sheaf of
sets of every `O`-module is a module object over it (`Stacks.sheafModuleObj`). The main theorem
says that a map of sheaves of sets `F × G → H` is a bilinear map of sheaves of `O`-modules if and
only if it is a bilinear map of these module objects. This is the last way of stating the
definition given in the section [Stacks, Tag 0GIG].

## Main definitions

* `CategoryTheory.ModuleObj.IsBilinear`: bilinearity of a morphism between module objects over a
  ring object in a cartesian monoidal category.

## Main results

* `CategoryTheory.ModuleObj.isBilinear_iff`: bilinearity read on generalized elements: `f` is
  bilinear if and only if `(a, b) ↦ lift a b ≫ f` is a bilinear map
  `Hom(X, F) × Hom(X, G) → Hom(X, H)` of modules over the ring `Hom(X, R)`, for every `X`.
* `Stacks.SheafOfModules.sheafModuleObj_add`, `sheafModuleObj_smul`: the addition and the action
  of the module object of a sheaf of modules are the addition and the scalar multiplication of
  the sheaf, read on its underlying sheaf of sets.
* `Stacks.SheafOfModules.isBilinearPairing_iff_moduleObj_isBilinear`: a map of sheaves of sets
  `F × G → H` is a bilinear map of sheaves of `O`-modules if and only if it is a bilinear map of
  module objects over the ring object `O` of the category of sheaves of sets.

## Implementation notes

The four conditions of `ModuleObj.IsBilinear` are stated at the universal generalized elements,
as single equations of morphisms, in the same way as `CategoryTheory.RingObj` states `mul_add`
and `CategoryTheory.ModuleObj` states `smul_add`; `ModuleObj.isBilinear_iff` converts them to
statements about all generalized elements.

The comparison with sheaves goes through the characterisation of bilinearity by morphisms out of
an arbitrary sheaf of sets, `isBilinearPairing_iff_forall_coyoneda`: on `Hom(S, -)` the
operations transported from the sheaves of modules are composition with `moduleAddHom` and
`moduleSMulHom`, and these are, on the nose, the addition and action of the module objects.

## References

* [Stacks Project, Tag 0GIG](https://stacks.math.columbia.edu/tag/0GIG)
-/

@[expose] public noncomputable section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

universe w v u

namespace CategoryTheory

open MonoidalCategory CartesianMonoidalCategory
open scoped MonObj AddMonObj RingObj ModuleObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]

namespace ModuleObj

/-- A morphism `f : F ⊗ G ⟶ H` between module objects over a ring object `R` is **bilinear**
when it is additive in each argument and compatible with the action of `R` in each argument.
Each condition is a single commuting diagram, stated at the universal generalized elements in the
same way as the axioms of `CategoryTheory.RingObj` and `CategoryTheory.ModuleObj`. -/
structure IsBilinear (R : C) {F G H : C} [RingObj R] [ModuleObj R F] [ModuleObj R G]
    [ModuleObj R H] (f : F ⊗ G ⟶ H) : Prop where
  /-- `f (x + y, z) = f (x, z) + f (y, z)`. -/
  add_left : σ ▷ G ≫ f = lift (fst F F ▷ G ≫ f) (snd F F ▷ G ≫ f) ≫ σ
  /-- `f (x, y + z) = f (x, y) + f (x, z)`. -/
  add_right : F ◁ σ ≫ f = lift (F ◁ fst G G ≫ f) (F ◁ snd G G ≫ f) ≫ σ
  /-- `f (r • x, y) = r • f (x, y)`. -/
  smul_left : γ[R, F] ▷ G ≫ f =
    lift (fst (R ⊗ F) G ≫ fst R F) (lift (fst (R ⊗ F) G ≫ snd R F) (snd (R ⊗ F) G) ≫ f) ≫
      γ[R, H]
  /-- `f (x, r • y) = r • f (x, y)`. -/
  smul_right : F ◁ γ[R, G] ≫ f =
    lift (snd F (R ⊗ G) ≫ fst R G) (lift (fst F (R ⊗ G)) (snd F (R ⊗ G) ≫ snd R G) ≫ f) ≫
      γ[R, H]

variable {R F G H : C} [RingObj R] [ModuleObj R F] [ModuleObj R G] [ModuleObj R H]

/-- Bilinearity read on generalized elements: `f` is bilinear if and only if, for every object
`X`, the rule `Hom(X, F) × Hom(X, G) → Hom(X, H)`, `(a, b) ↦ lift a b ≫ f`, is bilinear over the
ring `Hom(X, R)`. -/
theorem isBilinear_iff (f : F ⊗ G ⟶ H) :
    IsBilinear R f ↔
      (∀ ⦃X : C⦄ (a a' : X ⟶ F) (b : X ⟶ G), lift (a + a') b ≫ f = lift a b ≫ f + lift a' b ≫ f) ∧
      (∀ ⦃X : C⦄ (a : X ⟶ F) (b b' : X ⟶ G), lift a (b + b') ≫ f = lift a b ≫ f + lift a b' ≫ f) ∧
      (∀ ⦃X : C⦄ (r : X ⟶ R) (a : X ⟶ F) (b : X ⟶ G), lift (r • a) b ≫ f = r • (lift a b ≫ f)) ∧
      (∀ ⦃X : C⦄ (r : X ⟶ R) (a : X ⟶ F) (b : X ⟶ G), lift a (r • b) ≫ f = r • (lift a b ≫ f)) := by
  refine ⟨fun h ↦ ⟨fun X a a' b ↦ ?_, fun X a b b' ↦ ?_, fun X r a b ↦ ?_, fun X r a b ↦ ?_⟩,
    fun ⟨h₁, h₂, h₃, h₄⟩ ↦ ⟨?_, ?_, ?_, ?_⟩⟩
  · have := lift (lift a a') b ≫= h.add_left
    simp only [lift_whiskerRight_assoc] at this
    simp only [Hom.add_def, this, ← Category.assoc]
    cat_disch
  · have := lift a (lift b b') ≫= h.add_right
    simp only [lift_whiskerLeft_assoc] at this
    simp only [Hom.add_def, this, ← Category.assoc]
    cat_disch
  · have := lift (lift r a) b ≫= h.smul_left
    simp only [lift_whiskerRight_assoc] at this
    rw [Hom.smul_def, this, Hom.smul_def]
    simp only [comp_lift_assoc, lift_fst_assoc, lift_fst, lift_snd]
  · have := lift a (lift r b) ≫= h.smul_right
    simp only [lift_whiskerLeft_assoc] at this
    rw [Hom.smul_def, this, Hom.smul_def]
    simp only [comp_lift_assoc, lift_snd_assoc, lift_fst, lift_snd]
  · have := h₁ (fst (F ⊗ F) G ≫ fst F F) (fst (F ⊗ F) G ≫ snd F F) (snd (F ⊗ F) G)
    simp only [Hom.add_def] at this
    convert! this using 2
    · cat_disch
    · ext
      · simp only [lift_fst]
        congr 1
        cat_disch
      · simp only [lift_snd]
        congr 1
        cat_disch
  · have := h₂ (fst F (G ⊗ G)) (snd F (G ⊗ G) ≫ fst G G) (snd F (G ⊗ G) ≫ snd G G)
    simp only [Hom.add_def] at this
    convert! this using 2
    · cat_disch
    · ext
      · simp only [lift_fst]
        congr 1
        cat_disch
      · simp only [lift_snd]
        congr 1
        cat_disch
  · have := h₃ (fst (R ⊗ F) G ≫ fst R F) (fst (R ⊗ F) G ≫ snd R F) (snd (R ⊗ F) G)
    simp only [Hom.smul_def] at this
    convert! this using 2
    cat_disch
  · have := h₄ (snd F (R ⊗ G) ≫ fst R G) (fst F (R ⊗ G)) (snd F (R ⊗ G) ≫ snd R G)
    simp only [Hom.smul_def] at this
    convert! this using 2
    cat_disch

end ModuleObj

end CategoryTheory

namespace Stacks.SheafOfModules

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory CategoryTheory.Sheaf Opposite
open scoped MonObj AddMonObj RingObj ModuleObj

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget CommRingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})] (O : Sheaf J CommRingCat.{w})

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The addition of the module object carried by a sheaf of modules is the addition of the sheaf,
read on its underlying sheaf of sets. -/
lemma sheafModuleObj_add (G : _root_.SheafOfModules.{w} (Tensor.ringSheaf O)) :
    letI := hasSheafCompose_forget₂_commRingCat.{w} J
    letI := sheafCommRingObj J O
    letI := sheafModuleObj J O G
    (σ : underlyingModuleSheaf J G ⊗ underlyingModuleSheaf J G ⟶ underlyingModuleSheaf J G) =
      moduleAddHom (Tensor.ringSheaf O) G :=
  rfl

/-- The action of the ring object on the module object carried by a sheaf of modules is the
scalar multiplication of the sheaf, read on the underlying sheaves of sets. -/
lemma sheafModuleObj_smul (G : _root_.SheafOfModules.{w} (Tensor.ringSheaf O)) :
    letI := hasSheafCompose_forget₂_commRingCat.{w} J
    letI := sheafCommRingObj J O
    letI := sheafModuleObj J O G
    (γ[underlyingRingSheaf J O, underlyingModuleSheaf J G] :
        underlyingRingSheaf J O ⊗ underlyingModuleSheaf J G ⟶ underlyingModuleSheaf J G) =
      moduleSMulHom (Tensor.ringSheaf O) G :=
  rfl

/-- **Bilinear maps of sheaves of modules are bilinear maps of module objects.** Let `O` be a sheaf
of commutative rings. Its underlying sheaf of sets is a ring object in the category of sheaves of
sets, and the underlying sheaves of sets of `O`-modules `A`, `B`, `N` are module objects over it.
A map `q : A × B → N` of sheaves of sets is a bilinear map of sheaves of `O`-modules if and only if
it is a bilinear map of these module objects. -/
@[stacks 0GIG "the fifth characterisation of the section: `O_X` is a ring object in the category
of sheaves of sets, `F`, `G`, `H` are module objects over it, and a bilinear map `F x G -> H` of
sheaves of modules is the same thing as a bilinear map of module objects over a ring object, the
notion `CategoryTheory.ModuleObj.IsBilinear` defined for module objects over a ring object in any
category with finite products (a cartesian monoidal category). The ring and module objects are
`Stacks.sheafCommRingObj` and `Stacks.sheafModuleObj`. Over an arbitrary site rather than only the
opens of a ringed space"]
theorem isBilinearPairing_iff_moduleObj_isBilinear
    {A B N : _root_.SheafOfModules.{w} (Tensor.ringSheaf O)}
    (q : moduleSheaf (Tensor.ringSheaf O) A ⨯ moduleSheaf (Tensor.ringSheaf O) B ⟶
      moduleSheaf (Tensor.ringSheaf O) N) :
    IsBilinearPairing (Tensor.ringSheaf O) q ↔
      letI := hasSheafCompose_forget₂_commRingCat.{w} J
      letI := sheafCommRingObj J O
      letI := sheafModuleObj J O A
      letI := sheafModuleObj J O B
      letI := sheafModuleObj J O N
      ModuleObj.IsBilinear (underlyingRingSheaf J O) (F := underlyingModuleSheaf J A)
        (G := underlyingModuleSheaf J B) (H := underlyingModuleSheaf J N) q := by
  let := hasSheafCompose_forget₂_commRingCat.{w} J
  let := sheafCommRingObj J O
  let := sheafModuleObj J O A
  let := sheafModuleObj J O B
  let := sheafModuleObj J O N
  refine (isBilinearPairing_iff_forall_coyoneda _ q).trans
    (Iff.trans ?_ (ModuleObj.isBilinear_iff _).symm)
  simp only [isBilinearPairingObj_iff, coyoneda_pairingObj, coyoneda_moduleAddObj,
    coyoneda_moduleSMulObj, forall_and]
  exact Iff.rfl

end Stacks.SheafOfModules
