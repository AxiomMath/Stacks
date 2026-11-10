module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomVariance
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.SheafTensorHom
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-!
# Left exactness of internal Hom in the first argument

Let `(C, O)` be a ringed site, with structure sheaf in `CommRingCat.{max u v}`, and let `G` be a
sheaf of `O`-modules. An exact sequence `F₁ → F₂ → F₃ → 0` of `O`-modules induces an exact sequence

`0 → Hom_O(F₃, G) → Hom_O(F₂, G) → Hom_O(F₁, G)`

of internal Hom sheaves.

## Main definitions

* `Stacks.SheafOfModules.InternalHom.sheafInternalHomMapLeft`: precomposition in the first
  variable of the internal Hom sheaf.
* `Stacks.SheafOfModules.InternalHom.siteInternalHomFirstFunctor`: internal Hom against a fixed
  sheaf of modules, as a functor to the opposite category of sheaves of modules.

## Main results

* `Stacks.SheafOfModules.InternalHom.siteInternalHomFirstFunctor_preservesColimitsOfShape`:
  internal Hom against a fixed sheaf of modules takes colimits in its first variable to limits.
* `Stacks.SheafOfModules.InternalHom.sheafInternalHomMapLeft_mono_of_epi`: precomposition
  along an epimorphism is a monomorphism of internal Hom sheaves.
* `Stacks.SheafOfModules.InternalHom.sheafInternalHomMapLeft_exact_of_exact_epi`: the induced
  sequence of internal Hom sheaves is exact at its middle term.
* `Stacks.SheafOfModules.InternalHom.ringedSite_sheafInternalHomMapLeft_mono_of_epi` and
  `Stacks.SheafOfModules.InternalHom.ringedSite_sheafInternalHomMapLeft_exact_of_exact_epi`:
  the same two statements over a `RingedSite.{u, v, max u v}`.

## References

* [Stacks Project, Tag 0GMY](https://stacks.math.columbia.edu/tag/0GMY)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules.InternalHom


universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable (O : Sheaf J CommRingCat.{max u v})

/-- Precomposition in the first variable of the internal Hom sheaf. -/
noncomputable def sheafInternalHomMapLeft
    {F F' G : _root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (f : F' ⟶ F) :
    siteSheafInternalHom J O F G ⟶ siteSheafInternalHom J O F' G :=
  ⟨Stacks.PresheafOfModules.InternalHom.internalHomMapLeft O.obj f.val⟩

/-- Internal Hom against a fixed sheaf of modules, as a functor to the opposite category of
sheaves of modules. -/
noncomputable def siteInternalHomFirstFunctor
    (G : _root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :
    _root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) ⥤
      (_root_.SheafOfModules.{max u v}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))ᵒᵖ where
  obj F := op (siteSheafInternalHom J O F G)
  map f := (sheafInternalHomMapLeft J O f).op
  map_id _ := Quiver.Hom.unop_inj (by ext; rfl)
  map_comp _ _ := Quiver.Hom.unop_inj (by ext; rfl)

private noncomputable def sheafTranspose
    {A B G : _root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (f : A ⟶ siteSheafInternalHom J O B G) : B ⟶ siteSheafInternalHom J O A G :=
  ⟨Stacks.PresheafOfModules.InternalHom.transposeHom O.obj f.val⟩

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
private lemma sheafTranspose_involutive
    {A B G : _root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (f : A ⟶ siteSheafInternalHom J O B G) :
    sheafTranspose J O (sheafTranspose J O f) = f :=
  _root_.SheafOfModules.hom_ext
    (Stacks.PresheafOfModules.InternalHom.transposeHom_involutive O.obj f.val)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
private lemma sheafTranspose_comp
    {A A' B G :
      _root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (f : A' ⟶ A) (g : A ⟶ siteSheafInternalHom J O B G) :
    sheafTranspose J O (f ≫ g) =
      sheafTranspose J O g ≫ sheafInternalHomMapLeft J O f := by
  ext; rfl

/-- Internal Hom in the first variable is left adjoint to its own opposite. -/
private noncomputable def internalHomFirstAdjunction
    (G : _root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :
    siteInternalHomFirstFunctor J O G ⊣ (siteInternalHomFirstFunctor J O G).leftOp :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun f => sheafTranspose J O f.unop
          invFun := fun f => (sheafTranspose J O f).op
          left_inv := fun f => Quiver.Hom.unop_inj (sheafTranspose_involutive J O f.unop)
          right_inv := sheafTranspose_involutive J O }
      homEquiv_naturality_left_symm := fun f g =>
        Quiver.Hom.unop_inj (sheafTranspose_comp J O f g)
      homEquiv_naturality_right := fun f g => sheafTranspose_comp J O g.unop f.unop }

/-- Internal Hom against a fixed sheaf of modules takes colimits in its first variable to
limits. -/
@[sga "4 IV 12.2" "partial, special case"]
noncomputable instance siteInternalHomFirstFunctor_preservesColimitsOfShape
    (G : _root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))
    (I : Type*) [Category I] :
    PreservesColimitsOfShape I (siteInternalHomFirstFunctor J O G) := by
  have := (internalHomFirstAdjunction J O G).leftAdjoint_preservesColimits
  infer_instance


omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
private theorem siteInternalHomFirstFunctor_preservesZeroMorphisms
    (G : _root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :
    (siteInternalHomFirstFunctor J O G).PreservesZeroMorphisms :=
  have := (internalHomFirstAdjunction J O G).isLeftAdjoint
  inferInstance

section LeftExact

/-- The site is essentially small in the universe `max u v`. -/
local instance essentiallySmall_of_module_universe : EssentiallySmall.{max u v} C :=
  essentiallySmallSelf.{max u v, v, u} C

/-- Abelian presheaves on the site with values in `AddCommGrpCat.{max u v}` can be
sheafified. -/
local instance hasSheafify_addCommGrpCat : HasSheafify J AddCommGrpCat.{max u v} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{max u v, v, u} J

/-- A morphism of presheaves with values in `AddCommGrpCat.{max u v}` becomes an isomorphism
after sheafification exactly when it is locally bijective. -/
local instance wEqualsLocallyBijective_addCommGrpCat :
    J.WEqualsLocallyBijective AddCommGrpCat.{max u v} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, max u v, u,
    max (u + 1) (v + 1), max u v} J

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Precomposition along an epimorphism is a monomorphism of internal Hom sheaves. -/
theorem sheafInternalHomMapLeft_mono_of_epi
    {F₁ F G : _root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (g : F₁ ⟶ F) [Epi g] :
    Mono (sheafInternalHomMapLeft J O (G := G) g) := by
  have := siteInternalHomFirstFunctor_preservesZeroMorphisms J O G
  have hepi : Epi ((siteInternalHomFirstFunctor J O G).map g) :=
    epi_of_isColimit_cofork <| (CokernelCofork.ofπ g (kernel.condition g)).mapIsColimit
      (Abelian.epiIsCokernelOfKernel (KernelFork.ofι _ (kernel.condition g)) (kernelIsKernel g))
      (siteInternalHomFirstFunctor J O G)
  exact (op_epi_iff _).1 hepi

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- If `S` is an exact sequence of sheaves of modules with `S.g` an epimorphism, then
precomposition with `S.g` and `S.f` gives a sequence of internal Hom sheaves with zero composite,
exact at its middle term. -/
theorem sheafInternalHomMapLeft_exact_of_exact_epi
    (S : ShortComplex
      (_root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)))
    (G : _root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))
    (hS : S.Exact) [Epi S.g] :
    ∃ h : sheafInternalHomMapLeft J O (G := G) S.g ≫
        sheafInternalHomMapLeft J O (G := G) S.f = 0,
      (ShortComplex.mk (sheafInternalHomMapLeft J O (G := G) S.g)
        (sheafInternalHomMapLeft J O (G := G) S.f) h).Exact := by
  let H := siteInternalHomFirstFunctor J O G
  have := siteInternalHomFirstFunctor_preservesZeroMorphisms J O G
  exact ⟨(S.map H).unop.zero,
    (hS.map_of_epi_of_preservesCokernel H inferInstance inferInstance).unop⟩

end LeftExact

end Stacks.SheafOfModules.InternalHom

namespace Stacks.SheafOfModules.InternalHom

open AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

universe v u

variable (X : RingedSite.{u, v, max u v})

/-- Over a ringed site, precomposition along an epimorphism is a monomorphism of internal Hom
sheaves. -/
theorem ringedSite_sheafInternalHomMapLeft_mono_of_epi
    {F₁ F G : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (g : F₁ ⟶ F) [Epi g] :
    Mono (sheafInternalHomMapLeft X.J X.O (G := G) g) :=
  sheafInternalHomMapLeft_mono_of_epi X.J X.O g

/-- Over a ringed site, if `S` is an exact sequence of sheaves of modules with `S.g` an
epimorphism, then precomposition with `S.g` and `S.f` gives a sequence of internal Hom sheaves
with zero composite, exact at its middle term. -/
theorem ringedSite_sheafInternalHomMapLeft_exact_of_exact_epi
    (S : ShortComplex
      (_root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (G : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hS : S.Exact) [Epi S.g] :
    ∃ h : sheafInternalHomMapLeft X.J X.O (G := G) S.g ≫
        sheafInternalHomMapLeft X.J X.O (G := G) S.f = 0,
      (ShortComplex.mk (sheafInternalHomMapLeft X.J X.O (G := G) S.g)
        (sheafInternalHomMapLeft X.J X.O (G := G) S.f) h).Exact :=
  sheafInternalHomMapLeft_exact_of_exact_epi X.J X.O S G hS

end Stacks.SheafOfModules.InternalHom

end
