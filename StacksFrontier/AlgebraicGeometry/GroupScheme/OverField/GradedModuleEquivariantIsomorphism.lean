module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GradedModuleEquivariantComparison
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GradedModuleEquivariantSheaf

/-!
# The equivariant module is the one attached to the grading of its global sections

Let `A` be an integer-graded commutative ring, let `X = Spec A` and let the multiplicative group
`𝐆ₘ` act on `X` through the grading.  Let `F` be a `𝐆ₘ`-equivariant quasi-coherent `𝒪_X`-module
and let `M = Γ(X, F)` carry its canonical grading.  Then the canonical comparison `M~ ⟶ F` of a
quasi-coherent module on an affine scheme with the module associated to its global sections is an
isomorphism of `𝐆ₘ`-equivariant modules, for the equivariant structure on `M~` attached to the
grading of `M`.

## Main definitions

* `AlgebraicGeometry.EquivariantModule.isoOfIsIsoHom` upgrades a morphism of equivariant modules
  whose underlying morphism of quasi-coherent modules is invertible to an isomorphism of
  equivariant modules.
* `AlgebraicGeometry.GmEquivariant.tildeHomogeneousHom` is the canonical comparison `M~ ⟶ F`, as
  a morphism of `𝐆ₘ`-equivariant modules.
* `AlgebraicGeometry.GmEquivariant.tildeHomogeneousIso` is that comparison, as an isomorphism of
  `𝐆ₘ`-equivariant modules.

## Main results

* `AlgebraicGeometry.GmEquivariant.fromTildeΓ_app_toOpen`: the canonical comparison recovers a
  global section of a module from the corresponding global section of the module associated to
  the global sections.
* `AlgebraicGeometry.GmEquivariant.comm_of_eigensections`: a morphism of the underlying modules
  intertwines two descent morphisms as soon as they scale the canonical pullback sections of a
  generating family, and of its image, by the same global functions.
* `AlgebraicGeometry.GmEquivariant.tildeHomogeneousIso_hom_hom`: the underlying morphism of
  quasi-coherent modules of that isomorphism is the canonical comparison.

## Implementation notes

The compatibility of the comparison with the two descent morphisms is checked on the canonical
pullback sections of the homogeneous global sections, which generate: on such a section the
descent morphism of `M~` is multiplication by the character `xⁿ` by construction, and the descent
morphism of `F` is multiplication by the same character because the section lies in the canonical
degree-`n` piece.  The two then agree once one knows that the comparison carries the canonical
global section of `M~` attached to `m` back to `m`, which is the triangle identity of the
tilde--Gamma adjunction.

That check is carried out in `AlgebraicGeometry.GmEquivariant.comm_of_eigensections`, over an
arbitrary action and an arbitrary generating family, rather than on the goal itself: rewriting the
descent morphism of the equivariant module attached to a graded module into the shape in which it
is computed leaves a goal which is not type-correct at the implicit transparency level, so no
further rewriting is possible there.  The group-object and action structures on the scheme of
arrows are not found by instance search, so the morphism and the isomorphism of equivariant
modules are built by applying the constructors with those two instances supplied explicitly, as
elsewhere for this action.

## References

* [Stacks Project, Tag 0EKL](https://stacks.math.columbia.edu/tag/0EKL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped DirectSum CategoryTheory.MonObj

universe u v w

namespace AlgebraicGeometry

/-! ### Invertibility of a morphism of equivariant modules -/

namespace EquivariantModule

variable {S : Scheme.{u}} {Y : Over S} {G X : Over Y.left} [GrpObj G] [ModObj G X]
  {M N : EquivariantModule Y G X}

/-- A morphism of equivariant modules whose underlying morphism of quasi-coherent modules is
invertible is an isomorphism of equivariant modules: the inverse morphism of modules
automatically intertwines the two descent morphisms. -/
noncomputable def isoOfIsIsoHom (f : M ⟶ N) [IsIso f.hom] : M ≅ N where
  hom := f
  inv :=
    { hom := inv f.hom
      comm := by
        rw [Functor.map_inv, Functor.map_inv, IsIso.comp_inv_eq, Category.assoc,
          IsIso.eq_inv_comp]
        exact f.comm.symm }
  hom_inv_id := by apply EquivariantModule.Hom.ext; exact IsIso.hom_inv_id f.hom
  inv_hom_id := by apply EquivariantModule.Hom.ext; exact IsIso.inv_hom_id f.hom

/-- The isomorphism of equivariant modules attached to a morphism with invertible underlying
morphism of modules is that morphism. -/
@[simp] theorem isoOfIsIsoHom_hom (f : M ⟶ N) [IsIso f.hom] : (isoOfIsIsoHom f).hom = f := rfl

end EquivariantModule

namespace GmEquivariant

attribute [local instance 100] ULift.algebra'

attribute [local implicit_reducible] CategoryTheory.OverClass.asOver

/-! ### The comparison on global sections -/

/-- The canonical comparison `Γ(F)~ ⟶ F` recovers a global section of `F` from the corresponding
global section of the module associated to the global sections of `F`.  This is the triangle
identity of the tilde--Gamma adjunction, read on global sections. -/
theorem fromTildeΓ_app_toOpen {R : CommRingCat.{u}} (F : (Spec R).Modules)
    (x : moduleSpecΓFunctor.obj F) :
    (Scheme.Modules.fromTildeΓNatTrans.app F).app ⊤
        (tilde.toOpen (moduleSpecΓFunctor.obj F) ⊤ x) = x :=
  congr(ModuleCat.Hom.hom $(tilde.adjunction.right_triangle_components F) x)

/-! ### Intertwining two descent morphisms -/

section Intertwine

variable {S : Scheme.{u}} (Y : Over S) (G X : Over Y.left) [GrpObj G] [ModObj G X]

/-- A morphism of the underlying modules intertwines two descent morphisms as soon as those scale
the canonical pullback sections of a generating family of sections, and of the image of that
family, by the same global functions on the scheme of arrows. -/
theorem comm_of_eigensections {E E' : X.left.Modules} (h : E ⟶ E')
    (α : (Scheme.Modules.pullback γ[G,X].left).obj E ⟶
      (Scheme.Modules.pullback (snd G X).left).obj E)
    (α' : (Scheme.Modules.pullback γ[G,X].left).obj E' ⟶
      (Scheme.Modules.pullback (snd G X).left).obj E')
    {Idx : Type w} (s : Idx → Γ(E, ⊤)) (s' : Idx → Γ(E', ⊤))
    (r : Idx → Γ((G ⊗ X).left, ⊤)) (hs : ∀ i, h.app ⊤ (s i) = s' i)
    (hext : ∀ {N : (G ⊗ X).left.Modules}
      (a b : (Scheme.Modules.pullback γ[G,X].left).obj E ⟶ N),
      (∀ i, a.app ⊤ (pullbackSection γ[G,X].left E (s i)) =
        b.app ⊤ (pullbackSection γ[G,X].left E (s i))) → a = b)
    (ha : ∀ i, α.app ⊤ (pullbackSection γ[G,X].left E (s i)) =
      r i • pullbackSection (snd G X).left E (s i))
    (ha' : ∀ i, α'.app ⊤ (pullbackSection γ[G,X].left E' (s' i)) =
      r i • pullbackSection (snd G X).left E' (s' i)) :
    α ≫ (Scheme.Modules.pullback (snd G X).left).map h =
      (Scheme.Modules.pullback γ[G,X].left).map h ≫ α' :=
  hext _ _ fun i => by
    simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.ConcreteCategory.comp_apply]
    rw [ha i, Scheme.Modules.Hom.app_smul, pullbackSection_naturality,
      pullbackSection_naturality, hs i, ha' i]

end Intertwine

/-! ### The comparison is an isomorphism of equivariant modules -/

section Isomorphism

variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ℤ → σ) [GradedRing 𝒜]

attribute [local instance] homogeneousPartDecomposition gradedSMul_homogeneousPart

variable (F : GradedEquivariantModule.{u} 𝒜)

/-- The global sections of the underlying module of a `𝐆ₘ`-equivariant module, read as a module
over the ring `A` itself. -/
noncomputable abbrev sectionsModuleOf : ModuleCat.{u} (CommRingCat.of A) :=
  moduleOf A ((moduleSpecΓFunctor (R := .of A)).obj (underlyingModule 𝒜 F))

/-- The canonical comparison recovers a global section of the underlying module of a
`𝐆ₘ`-equivariant module from the corresponding global section of the associated module. -/
theorem fromTildeΓ_app_toOpen_sectionsModuleOf (x : sectionsModuleOf 𝒜 F) :
    (Scheme.Modules.fromTildeΓNatTrans.app (underlyingModule 𝒜 F)).app ⊤
        (tilde.toOpen (sectionsModuleOf 𝒜 F) ⊤ x) = x :=
  fromTildeΓ_app_toOpen (underlyingModule 𝒜 F) x

/-- The canonical comparison `M~ ⟶ F`, for `M = Γ(X, F)` with its canonical grading, as a
morphism of `𝐆ₘ`-equivariant modules. -/
noncomputable def tildeHomogeneousHom :
    gradedModuleEquivariantSheaf 𝒜 (homogeneousPart 𝒜 F) ⟶ F :=
  @EquivariantModule.Hom.mk _ base.{u} gm.{u} (specAOver A)
    AlgebraicGeometry.instGrpObjSpecAsOverSpec (gradedGmAction 𝒜).action
    (gradedModuleEquivariantSheaf 𝒜 (homogeneousPart 𝒜 F)) F
    (Scheme.Modules.fromTildeΓNatTrans.app (underlyingModule 𝒜 F))
    (@comm_of_eigensections _ base.{u} gm.{u} (specAOver A)
      AlgebraicGeometry.instGrpObjSpecAsOverSpec (gradedGmAction 𝒜).action
      (tilde (sectionsModuleOf 𝒜 F)) (underlyingModule 𝒜 F)
      (Scheme.Modules.fromTildeΓNatTrans.app (underlyingModule 𝒜 F))
      (gradedDescentMorphism 𝒜 (homogeneousPart 𝒜 F)) (descentMorphism 𝒜 F)
      (Σ n : ℤ, homogeneousPart 𝒜 F n)
      (fun i => tilde.toOpen (sectionsModuleOf 𝒜 F) ⊤ (i.2 : sectionsModuleOf 𝒜 F))
      (fun i => (i.2 : sectionsModuleOf 𝒜 F))
      (fun i => laurentCoordinate A i.1)
      (fun i => fromTildeΓ_app_toOpen_sectionsModuleOf 𝒜 F (i.2 : sectionsModuleOf 𝒜 F))
      (fun _ _ hab => pullback_tilde_homogeneous_ext (homogeneousPart 𝒜 F)
        (gradedGmAction 𝒜).action.smul.left fun n m => hab ⟨n, m⟩)
      (fun i => gradedDescentMorphism_homogeneous 𝒜 (homogeneousPart 𝒜 F) i.2)
      (fun i => (mem_homogeneousPart_iff 𝒜 F i.1 (i.2 : sectionsModuleOf 𝒜 F)).mp i.2.2))

/-- **Stacks Project, Tag 0EKL.** For a `𝐆ₘ`-equivariant quasi-coherent module `F` on
`X = Spec A` and `M = Γ(X, F)` with its canonical grading, the canonical comparison `M~ ⟶ F` is
an isomorphism of `𝐆ₘ`-equivariant modules, the equivariant structure on `M~` being the one
attached to the grading of `M`. -/
@[stacks 0EKL "the comparison is an isomorphism of equivariant modules"]
noncomputable def tildeHomogeneousIso :
    gradedModuleEquivariantSheaf 𝒜 (homogeneousPart 𝒜 F) ≅ F :=
  @EquivariantModule.isoOfIsIsoHom _ base.{u} gm.{u} (specAOver A)
    AlgebraicGeometry.instGrpObjSpecAsOverSpec (gradedGmAction 𝒜).action
    (gradedModuleEquivariantSheaf 𝒜 (homogeneousPart 𝒜 F)) F (tildeHomogeneousHom 𝒜 F)
    (show IsIso (Scheme.Modules.fromTildeΓ (underlyingModule 𝒜 F)) from
      @Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (CommRingCat.of A)
        (underlyingModule 𝒜 F) (isQuasicoherent_underlyingModule 𝒜 F))

/-- **Stacks Project, Tag 0EKL.** The isomorphism of `𝐆ₘ`-equivariant modules above is the
canonical comparison of a quasi-coherent module on an affine scheme with the module associated to
its global sections. -/
@[stacks 0EKL "the equivariant isomorphism is the canonical comparison"]
theorem tildeHomogeneousIso_hom_hom :
    @EquivariantModule.Hom.hom _ base.{u} gm.{u} (specAOver A)
        AlgebraicGeometry.instGrpObjSpecAsOverSpec (gradedGmAction 𝒜).action
        (gradedModuleEquivariantSheaf 𝒜 (homogeneousPart 𝒜 F)) F
        (@CategoryTheory.Iso.hom _ _ _ _ (tildeHomogeneousIso 𝒜 F)) =
      Scheme.Modules.fromTildeΓNatTrans.app (underlyingModule 𝒜 F) :=
  rfl

end Isomorphism

end GmEquivariant

end AlgebraicGeometry

end
