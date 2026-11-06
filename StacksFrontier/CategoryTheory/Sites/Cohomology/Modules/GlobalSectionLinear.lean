module

public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.RingTheory.Ideal.Operations
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Homology.DerivedLinear

/-!
# Global sections as scalars: the linear structure on sheaves of modules, and the subsheaf `I F`

Let `(C, J)` be a site and `O` a sheaf of rings on it whose rings of sections are commutative.
Multiplying by a compatible family of local sections of `O` is an endomorphism of every sheaf of
`O`-modules, natural in the module
(`Stacks.SheafOfModules.globalSectionToEnd`); writing `a • f` for `globalSmul O a M ≫ f` therefore
makes every `Hom`-group a module over the ring `Γ(C, O)` of global sections and the whole
category `Γ(C, O)`-linear.  Global sections and, by `Stacks.DerivedLinear.rightDerived_linear`,
their right derived functors are then `Γ(C, O)`-linear functors: a scalar acts on
`Hᵖ(C, M)` by the cohomology of multiplication by that scalar on `M`.

For an ideal `I ⊆ Γ(C, O)` and a sheaf of modules `F`, the subsheaf `I F` is the image of the
single morphism `∐_{a ∈ I} F → F` assembled from multiplication by the elements of `I`.  Its
basic properties are those of an image: a morphism out of `I F` vanishes exactly when it kills
every `I`-multiple of `F`, and a morphism into `F` whose composite with the cokernel projection
of the generating morphism vanishes descends to `I F`.  The two induced maps are the
functoriality `I F → I G` in `F` and the degree-raising map `I F → L F` given by multiplication by
a scalar `a` with `I · a ⊆ L`.

Finally the long exact cohomology sequence of a short exact sequence of sheaves of `O`-modules is
recorded as a cohomological `δ`-functor, by transporting
`Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives` to the global-sections
functor.

## Main definitions

* `Stacks.Cohomology.SiteModules.globalSmul`: multiplication by a global section of `O` on a
  sheaf of `O`-modules.
* `Stacks.Cohomology.SiteModules.homModule` and `linearSheafOfModules`: the resulting
  `Γ(C, O)`-module structure on the `Hom`-groups, and the linear structure on the category.
* `Stacks.Cohomology.SiteModules.idealSmul` and `idealSmulι`: the subsheaf `I F` and its
  inclusion into `F`.
* `Stacks.Cohomology.SiteModules.idealSmulMap`: the map `I F → I G` induced by `F ⟶ G`.
* `Stacks.Cohomology.SiteModules.idealSmulScalarMap`: multiplication by a scalar as a map
  `I F → L F`.
* `Stacks.Cohomology.SiteModules.cohomologyDeltaFunctor`: the cohomology of sheaves of
  `O`-modules on the site, as a cohomological `δ`-functor.

## Main results

* `Stacks.Cohomology.SiteModules.globalSectionsFunctor_linear` and
  `globalModuleCohomology_linear`: global sections and their right derived functors are
  `Γ(C, O)`-linear.
* `Stacks.Cohomology.SiteModules.idealSmulι_comp_eq_zero_iff`: a morphism out of `I F` vanishes
  exactly when every `I`-multiple of `F` is killed.
* `Stacks.Cohomology.SiteModules.idealSmulLift_comp_ι`, `idealSmulMap_comp_ι` and
  `idealSmulScalarMap_comp_ι`: the defining equations of the three maps into `I F`, stated after
  composing with the inclusion, which is a monomorphism and therefore determines them.

## Implementation notes

Commutativity of the structure sheaf is assumed in the unbundled form
`∀ X, IsMulCommutative (O.obj.obj X)`, as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GlobalSectionSmul.lean`; the bundled
`CommRing Γ(C, O)` is then obtained from the scoped instance of the `IsMulCommutative`
namespace, which is what the `ModuleCat` linear structure over the coefficient ring needs.

The coproduct defining `I F` is indexed by `ULift ↥I` rather than by `↥I`: the ideal lives in the
universe `max u r` of the global sections, while the coproducts available in the module category
are those of the ambient module universe `max u v r w`.

## References

* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped IsMulCommutative

attribute [local instance] HasDerivedCategory.standard

universe u v r w

namespace Stacks.Cohomology.SiteModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{r}) [∀ X : Cᵒᵖ, IsMulCommutative (O.obj.obj X)]

/-- The ring of global sections of a sheaf of commutative rings is commutative. -/
instance globalIsMulComm : IsMulCommutative ↥(GlobalSectionRing O) where
  is_comm := ⟨fun a b => Subtype.ext (funext fun X => mul_comm (a.1 X) (b.1 X))⟩

example : CommRing ↥(GlobalSectionRing O) := inferInstance
example : Linear ↥(GlobalSectionRing O) (ModuleCat.{w} ↥(GlobalSectionRing O)) := inferInstance

/-- Multiplication by a global section of the structure sheaf. -/
def globalSmul (a : GlobalSectionRing O) (M : SheafOfModules.{w} O) : M ⟶ M :=
  (Stacks.SheafOfModules.globalSectionToEnd O ⟨a.1, a.2⟩).asHom.app M

/-- On sections over `X`, `globalSmul O a M` is multiplication by the section `a` over `X`. -/
theorem globalSmul_app (a : GlobalSectionRing O) (M : SheafOfModules.{w} O) (X : Cᵒᵖ)
    (x : M.val.obj X) : (globalSmul O a M).val.app X x = a.1 X • x := rfl

/-- Multiplication by a global section commutes with every morphism of sheaves of modules. -/
theorem comp_globalSmul (a : GlobalSectionRing O) {M N : SheafOfModules.{w} O} (f : M ⟶ N) :
    f ≫ globalSmul O a N = globalSmul O a M ≫ f :=
  (Stacks.SheafOfModules.globalSectionToEnd O ⟨a.1, a.2⟩).asHom.naturality f

/-- Multiplication by `1` is the identity. -/
theorem globalSmul_one (M : SheafOfModules.{w} O) : globalSmul O 1 M = 𝟙 M := by
  ext X x
  show (1 : O.obj.obj X) • x = x
  simp

/-- Multiplication by `a * b` is multiplication by `a` followed by multiplication by `b`. -/
theorem globalSmul_mul (a b : GlobalSectionRing O) (M : SheafOfModules.{w} O) :
    globalSmul O (a * b) M = globalSmul O a M ≫ globalSmul O b M := by
  ext X x
  show (a.1 X * b.1 X) • x = b.1 X • a.1 X • x
  rw [← mul_smul]
  exact congrArg (fun c => c • x) (mul_comm (a.1 X) (b.1 X))

/-- Multiplication by `a + b` is the sum of the multiplications by `a` and by `b`. -/
theorem globalSmul_add (a b : GlobalSectionRing O) (M : SheafOfModules.{w} O) :
    globalSmul O (a + b) M = globalSmul O a M + globalSmul O b M := by
  ext X x
  show (a.1 X + b.1 X) • x = _
  rw [add_smul]
  rfl

/-- Multiplication by `0` is the zero morphism. -/
theorem globalSmul_zero (M : SheafOfModules.{w} O) :
    globalSmul O (0 : GlobalSectionRing O) M = 0 := by
  ext X x
  show (0 : O.obj.obj X) • x = _
  rw [zero_smul]
  rfl


/-- Morphisms of sheaves of modules are a module over the ring of global sections. -/
instance homModule (M N : SheafOfModules.{w} O) :
    Module ↥(GlobalSectionRing O) (M ⟶ N) where
  smul a f := globalSmul O a M ≫ f
  one_smul f := by
    change globalSmul O 1 M ≫ f = f
    rw [globalSmul_one, Category.id_comp]
  mul_smul a b f := by
    change globalSmul O (a * b) M ≫ f = globalSmul O a M ≫ globalSmul O b M ≫ f
    rw [globalSmul_mul, Category.assoc]
  smul_zero a := by
    change globalSmul O a M ≫ (0 : M ⟶ N) = 0
    simp
  smul_add a f g := by
    change globalSmul O a M ≫ (f + g) = globalSmul O a M ≫ f + globalSmul O a M ≫ g
    simp
  add_smul a b f := by
    change globalSmul O (a + b) M ≫ f = globalSmul O a M ≫ f + globalSmul O b M ≫ f
    rw [globalSmul_add, Preadditive.add_comp]
  zero_smul f := by
    change globalSmul O (0 : GlobalSectionRing O) M ≫ f = 0
    rw [globalSmul_zero, Limits.zero_comp]

/-- The scalar action of a global section `a` on a morphism `f` is `globalSmul O a M ≫ f`. -/
theorem smul_def (a : GlobalSectionRing O) {M N : SheafOfModules.{w} O} (f : M ⟶ N) :
    a • f = globalSmul O a M ≫ f := rfl

/-- Sheaves of modules form a linear category over the ring of global sections. -/
instance linearSheafOfModules : Linear ↥(GlobalSectionRing O) (SheafOfModules.{w} O) where
  smul_comp M N P a f g := by
    change (globalSmul O a M ≫ f) ≫ g = globalSmul O a M ≫ f ≫ g
    rw [Category.assoc]
  comp_smul M N P f a g := by
    change f ≫ globalSmul O a N ≫ g = globalSmul O a M ≫ f ≫ g
    rw [← Category.assoc, comp_globalSmul, Category.assoc]

/-- Multiplication by `a` is the scalar `a` acting on the identity morphism. -/
theorem globalSmul_eq_smul_id (a : GlobalSectionRing O) (M : SheafOfModules.{w} O) :
    globalSmul O a M = a • 𝟙 M := by
  rw [smul_def, Category.comp_id]

/-- Global sections of a sheaf of modules, as a linear functor. -/
instance globalSectionsFunctor_linear :
    Functor.Linear ↥(GlobalSectionRing O) (globalSectionsFunctor.{u, v, r, w} O) where
  map_smul {M N} f a := by
    change (globalSectionsFunctor O).map (globalSmul O a M ≫ f) = _
    rw [Functor.map_comp]
    have h : (globalSectionsFunctor O).map (globalSmul O a M) = a • 𝟙 _ := by
      ext s
      exact Subtype.ext rfl
    rw [h, Linear.smul_comp, Category.id_comp]


/-- The cohomology of sheaves of modules is a linear functor over the ring of global sections. -/
instance globalModuleCohomology_linear (p : ℕ) :
    Functor.Linear ↥(GlobalSectionRing O) (globalModuleCohomology.{u, v, r, w} O p) :=
  Stacks.DerivedLinear.rightDerived_linear _ p


/-! ### The ideal-power subsheaf -/

section IdealSmul

variable (I : Ideal ↥(GlobalSectionRing O)) (F : SheafOfModules.{max u v r w} O)

/-- One morphism out of a coproduct whose image is the subsheaf generated by the
`I`-multiples of `F`. -/
def idealSmulHom : (∐ fun _ : ULift.{max v w} ↥I => F) ⟶ F :=
  Sigma.desc fun a => globalSmul O a.down.1 F

/-- The component of `idealSmulHom` at `a ∈ I` is multiplication by `a`. -/
theorem ι_idealSmulHom (a : ↥I) :
    Sigma.ι (fun _ : ULift.{max v w} ↥I => F) (ULift.up a) ≫ idealSmulHom O I F =
      globalSmul O a.1 F :=
  Sigma.ι_desc _ _

/-- The subsheaf `I F` of `F`: the image of multiplication by the elements of `I`. -/
def idealSmul : SheafOfModules.{max u v r w} O := image (idealSmulHom O I F)

/-- The inclusion of the subsheaf `I F` into `F`. -/
def idealSmulι : idealSmul O I F ⟶ F := image.ι (idealSmulHom O I F)

/-- The inclusion of `I F` into `F` is a monomorphism. -/
instance idealSmulι_mono : Mono (idealSmulι O I F) :=
  inferInstanceAs (Mono (image.ι (idealSmulHom O I F)))

/-- Multiplication by `a ∈ I` factors through the subsheaf `I F`. -/
def idealSmulFactor {a : ↥(GlobalSectionRing O)} (ha : a ∈ I) : F ⟶ idealSmul O I F :=
  Sigma.ι (fun _ : ULift.{max v w} ↥I => F) (ULift.up ⟨a, ha⟩) ≫
    factorThruImage (idealSmulHom O I F)

/-- The factorization of multiplication by `a ∈ I` through `I F`, followed by the inclusion of
`I F`, is multiplication by `a`. -/
@[reassoc]
theorem idealSmulFactor_comp_ι {a : ↥(GlobalSectionRing O)} (ha : a ∈ I) :
    idealSmulFactor O I F ha ≫ idealSmulι O I F = globalSmul O a F := by
  show (Sigma.ι (fun _ : ULift.{max v w} ↥I => F) (ULift.up ⟨a, ha⟩) ≫
      factorThruImage (idealSmulHom O I F)) ≫ image.ι (idealSmulHom O I F) = globalSmul O a F
  rw [Category.assoc, image.fac]
  exact ι_idealSmulHom O I F ⟨a, ha⟩

/-- The inclusion of `I F` followed by the cokernel projection of `idealSmulHom` is zero. -/
@[reassoc]
theorem idealSmulι_comp_cokernelπ :
    idealSmulι O I F ≫ cokernel.π (idealSmulHom O I F) = 0 := by
  exact image_ι_comp_eq_zero (cokernel.condition _)

/-- A morphism out of `I F` vanishes exactly when it kills every `I`-multiple of `F`. -/
theorem idealSmulι_comp_eq_zero_iff {X : SheafOfModules.{max u v r w} O} (f : F ⟶ X) :
    idealSmulι O I F ≫ f = 0 ↔ ∀ a ∈ I, globalSmul O a F ≫ f = 0 := by
  refine ⟨fun hf a ha => by rw [← idealSmulFactor_comp_ι O I F ha, Category.assoc, hf, comp_zero],
    fun hf => ?_⟩
  exact image_ι_comp_eq_zero (Sigma.hom_ext _ _ fun a => by
    rw [← Category.assoc, ι_idealSmulHom, hf a.down.1 a.down.2, comp_zero])

/-- Multiplication by `a ∈ I` followed by the cokernel projection of `idealSmulHom` is zero. -/
@[reassoc]
theorem globalSmul_comp_cokernelπ {a : ↥(GlobalSectionRing O)} (ha : a ∈ I) :
    globalSmul O a F ≫ cokernel.π (idealSmulHom O I F) = 0 := by
  rw [← idealSmulFactor_comp_ι O I F ha, Category.assoc, idealSmulι_comp_cokernelπ, comp_zero]

/-- A morphism into `F` landing in `I F` descends to the subsheaf. -/
def idealSmulLift {X : SheafOfModules.{max u v r w} O} (g : X ⟶ F)
    (hg : g ≫ cokernel.π (idealSmulHom O I F) = 0) : X ⟶ idealSmul O I F :=
  kernel.lift (cokernel.π (idealSmulHom O I F)) g hg ≫
    (Abelian.imageIsoImage (idealSmulHom O I F)).hom

/-- The lift of `g` to `I F`, followed by the inclusion of `I F`, is `g`. -/
@[reassoc]
theorem idealSmulLift_comp_ι {X : SheafOfModules.{max u v r w} O} (g : X ⟶ F)
    (hg : g ≫ cokernel.π (idealSmulHom O I F) = 0) :
    idealSmulLift O I F g hg ≫ idealSmulι O I F = g := by
  show (kernel.lift (cokernel.π (idealSmulHom O I F)) g hg ≫
    (Abelian.imageIsoImage (idealSmulHom O I F)).hom) ≫ image.ι (idealSmulHom O I F) = g
  rw [Category.assoc, Abelian.imageIsoImage_hom_comp_image_ι, kernel.lift_ι]

/-- A morphism out of `I F` all of whose `I`-multiples are killed by the cokernel projection
of `I G` descends to `I G`. -/
theorem comp_cokernelπ_eq_zero (K : Ideal ↥(GlobalSectionRing O))
    {G : SheafOfModules.{max u v r w} O} (f : F ⟶ G)
    (hf : ∀ a ∈ I, globalSmul O a F ≫ f ≫ cokernel.π (idealSmulHom O K G) = 0) :
    (idealSmulι O I F ≫ f) ≫ cokernel.π (idealSmulHom O K G) = 0 := by
  rw [Category.assoc]
  exact (idealSmulι_comp_eq_zero_iff O I F (f ≫ cokernel.π (idealSmulHom O K G))).mpr hf

/-- The map `I F → I G` induced by a morphism `F ⟶ G`. -/
def idealSmulMap {G : SheafOfModules.{max u v r w} O} (f : F ⟶ G) :
    idealSmul O I F ⟶ idealSmul O I G :=
  idealSmulLift O I G (idealSmulι O I F ≫ f) (comp_cokernelπ_eq_zero O I F I f (by
    intro a ha
    rw [← Category.assoc, ← comp_globalSmul, Category.assoc,
      globalSmul_comp_cokernelπ O I G ha, comp_zero]))

/-- The map `I F → I G` induced by `f`, followed by the inclusion of `I G`, is the inclusion of
`I F` followed by `f`. -/
@[reassoc]
theorem idealSmulMap_comp_ι {G : SheafOfModules.{max u v r w} O} (f : F ⟶ G) :
    idealSmulMap O I F f ≫ idealSmulι O I G = idealSmulι O I F ≫ f :=
  idealSmulLift_comp_ι O I G _ _

/-- The map `I F → I F` induced by the identity is the identity. -/
theorem idealSmulMap_id : idealSmulMap O I F (𝟙 F) = 𝟙 _ := by
  apply (cancel_mono (idealSmulι O I F)).1
  rw [idealSmulMap_comp_ι, Category.comp_id, Category.id_comp]

/-- The maps `I F → I G` induced by morphisms are compatible with composition. -/
theorem idealSmulMap_comp {G H : SheafOfModules.{max u v r w} O} (f : F ⟶ G) (g : G ⟶ H) :
    idealSmulMap O I F f ≫ idealSmulMap O I G g = idealSmulMap O I F (f ≫ g) := by
  apply (cancel_mono (idealSmulι O I H)).1
  rw [Category.assoc, idealSmulMap_comp_ι, idealSmulMap_comp_ι_assoc, idealSmulMap_comp_ι]


/-- Multiplication by a scalar `a` carrying the subsheaf `I F` into the subsheaf `L F`. -/
def idealSmulScalarMap (L : Ideal ↥(GlobalSectionRing O)) {a : ↥(GlobalSectionRing O)}
    (ha : ∀ b ∈ I, b * a ∈ L) : idealSmul O I F ⟶ idealSmul O L F :=
  idealSmulLift O L F (idealSmulι O I F ≫ globalSmul O a F)
    (comp_cokernelπ_eq_zero O I F L (globalSmul O a F) (by
      intro b hb
      rw [← Category.assoc, ← globalSmul_mul, globalSmul_comp_cokernelπ O L F (ha b hb)]))

/-- Multiplication by `a` from `I F` to `L F`, followed by the inclusion of `L F`, is the
inclusion of `I F` followed by multiplication by `a`. -/
@[reassoc]
theorem idealSmulScalarMap_comp_ι (L : Ideal ↥(GlobalSectionRing O))
    {a : ↥(GlobalSectionRing O)} (ha : ∀ b ∈ I, b * a ∈ L) :
    idealSmulScalarMap O I F L ha ≫ idealSmulι O L F =
      idealSmulι O I F ≫ globalSmul O a F :=
  idealSmulLift_comp_ι O L F _ _

/-- Multiplication by a scalar `I F → L F` is natural in `F`. -/
theorem idealSmulScalarMap_naturality (L : Ideal ↥(GlobalSectionRing O))
    {a : ↥(GlobalSectionRing O)} (ha : ∀ b ∈ I, b * a ∈ L)
    {G : SheafOfModules.{max u v r w} O} (f : F ⟶ G) :
    idealSmulScalarMap O I F L ha ≫ idealSmulMap O L F f =
      idealSmulMap O I F f ≫ idealSmulScalarMap O I G L ha := by
  apply (cancel_mono (idealSmulι O L G)).1
  rw [Category.assoc, idealSmulMap_comp_ι, idealSmulScalarMap_comp_ι_assoc, Category.assoc,
    idealSmulScalarMap_comp_ι, idealSmulMap_comp_ι_assoc, comp_globalSmul]

end IdealSmul


/-! ### The long exact cohomology sequence -/

/-- The cohomology of sheaves of `O`-modules on the site, as a cohomological `δ`-functor. -/
def cohomologyDeltaFunctor :
    DeltaFunctor (SheafOfModules.{max u v r w} O)
      (ModuleCat.{max u v r w} ↥(GlobalSectionRing O)) :=
  Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (globalSectionsFunctor.{u, v, r, max u v r w} O)

omit [∀ (X : Cᵒᵖ), IsMulCommutative ↑(O.obj.obj X)] in
/-- The `p`-th functor of `cohomologyDeltaFunctor` is the `p`-th cohomology functor. -/
theorem cohomologyDeltaFunctor_functor (p : ℕ) :
    (cohomologyDeltaFunctor.{u, v, r, w} O).functor p = globalModuleCohomology.{u, v, r, w} O p :=
  rfl

/-- The cohomology functors of sheaves of modules are additive. -/
instance globalModuleCohomology_additive (p : ℕ) :
    (globalModuleCohomology.{u, v, r, w} O p).Additive :=
  (cohomologyDeltaFunctor.{u, v, r, w} O).additive p

end Stacks.Cohomology.SiteModules

end
