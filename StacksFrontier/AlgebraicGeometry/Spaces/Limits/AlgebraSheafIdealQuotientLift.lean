module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KernelIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafIdealQuotient

/-!
# The universal property of the quotient of an algebra sheaf by a sheaf of ideals

Let `F` be an algebraic space over a scheme `S` and let `f : A ⟶ C` be a morphism of algebra
sheaves on `F`.  This file provides the two things that make the quotients of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafIdealQuotient` usable as the members of
a *system*:

* the **kernel ideal** of `f`, a sheaf of ideals of the sheaf of rings underlying `A`, so that
  the ideals one may divide by and still receive a map to `C` form a sublattice of the lattice
  of all sheaves of ideals;
* the **universal property** of `A/I`: a morphism out of `A` whose sections kill `I` factors
  through `A ⟶ A/I`, uniquely.

Together these give the image factorization `A ⟶ A/ker f ⟶ C` of a morphism of algebra sheaves
on an algebraic space.

## Main definitions

* `AlgebraicGeometry.Space.AlgebraSheaf.kerIdeal`: **the kernel ideal of a morphism of algebra
  sheaves**, as a sheaf of ideals of the sheaf of rings underlying the source.
* `AlgebraicGeometry.Space.AlgebraSheaf.idealQuotientLift`: **the factorization of a morphism
  killing `I` through `A/I`.**
* `AlgebraicGeometry.Space.AlgebraSheaf.imageFactorizationHom`: **the second half
  `A/ker f ⟶ C` of the image factorization of `f`.**

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.toIdealQuotient_comp_idealQuotientLift`: the
  factorization does factor the morphism.
* `AlgebraicGeometry.Space.AlgebraSheaf.idealQuotient_hom_ext`: **two morphisms out of `A/I`
  agreeing on `A` are equal**, i.e. `A ⟶ A/I` is an epimorphism for the purpose of extending
  identities.  This is what makes the quotients functorial in the ideal *and* in the algebra.
* `AlgebraicGeometry.Space.AlgebraSheaf.toIdealQuotient_comp_imageFactorizationHom`: the image
  factorization `A ⟶ A/ker f ⟶ C` of a morphism of algebra sheaves.
* `AlgebraicGeometry.Space.AlgebraSheaf.idealQuotientLift_comp` and
  `idealQuotientMapOfLE_comp_idealQuotientLift`: compatibility of the factorization with a
  further morphism and with an enlargement of the ideal, which are the two laws a system of
  quotients needs.

## Implementation notes

The kernel ideal is `SheafOfModules.kerIdeal` of the morphism of sheaves of *rings* underlying
`f`, obtained by composing with `CategoryTheory.forget₂ CommRingCat RingCat`; that is the
spelling in which `Stacks.Sites.IdealSubsheaf` is phrased, so no transport is needed and
`AlgebraicGeometry.Space.AlgebraSheaf.mem_kerIdeal` is `SheafOfModules.mem_kerIdeal`.

The universal property is the sheafification adjunction composed with the universal property of
a quotient ring: a morphism `A ⟶ C` killing `I` gives, over every étale chart, a ring
homomorphism out of `A(U)/I(U)` by `Ideal.Quotient.lift`; these assemble into a morphism of
*presheaves* out of `Stacks.Sites.quotientPresheaf I`, and `CategoryTheory.sheafifyLift` carries
it across the sheafification.  Uniqueness is the composite of two injectivities: a morphism out
of a sheafification is determined by its restriction along `CategoryTheory.toSheafify`
(the adjunction), and a morphism out of the objectwise quotient is determined by its composite
with the objectwise quotient map (surjectivity of `Ideal.Quotient.mk`).

Finite presentation and quasi-coherence of `A/I` are *not* addressed.  Both are conditions on
the sections of `A/I` over the affine étale charts, and the sections of a sheafification are
not the sections of the presheaf.

What that comparison takes is **not** first cohomology on the small étale site, and it is carried
out in `StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafIdealQuotientCokernel`.  The
passage from local surjectivity to surjectivity on the sections over an affine étale chart is
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isQuasicoherentOnSite`, which is
unconditional in this tree — faithfully flat descent along a finite affine étale refinement, with
no Čech cohomology — and the kernel half of the comparison is
`AlgebraicGeometry.Space.AlgebraSheaf.kerIdeal_toIdealQuotient` in
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafIdealQuotientKernel`.  Between the two
sits the identification of the underlying module of `A/I` with the cokernel of the inclusion of
`I`, `AlgebraicGeometry.Space.AlgebraSheaf.underlyingModuleIdealQuotientCokernelIso`, which is
what lets the quasi-coherence of a cokernel
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_unconditional`) be applied.

## References

* [Stacks Project, Tag 082A](https://stacks.math.columbia.edu/tag/082A)
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

namespace AlgebraSheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-! ### The morphism of sheaves of rings underlying a morphism of algebra sheaves -/

/-- The morphism of sheaves of *rings* underlying a morphism of algebra sheaves: the underlying
morphism of sheaves of commutative rings, composed with the forgetful functor. -/
def ringCatHom {A C : AlgebraSheaf.{u, u} B S hS F hF} (f : A ⟶ C) :
    (sheafCompose (SmallEtale.topology B S hS F)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj A.right ⟶
      (sheafCompose (SmallEtale.topology B S hS F)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj C.right :=
  (sheafCompose (SmallEtale.topology B S hS F)
    (forget₂ CommRingCat.{u} RingCat.{u})).map f.right

/-- On sections over an étale chart, `ringCatHom f` acts as `f` does. -/
theorem ringCatHom_app {A C : AlgebraSheaf.{u, u} B S hS F hF} (f : A ⟶ C)
    (U : (SmallEtale B S hS F)ᵒᵖ) (a : A.right.obj.obj U) :
    ((ringCatHom f).hom.app U).hom a = (f.right.hom.app U).hom a :=
  rfl

/-! ### The kernel ideal -/

/-- **The kernel ideal of a morphism of algebra sheaves on an algebraic space**: the sheaf of
ideals of the sheaf of rings underlying the source whose sections over an étale chart are the
kernel of the morphism on sections there. -/
def kerIdeal {A C : AlgebraSheaf.{u, u} B S hS F hF} (f : A ⟶ C) : A.IdealSheaf :=
  SheafOfModules.kerIdeal.{u, u, u + 1} (ringCatHom f)

/-- A section of `A` over an étale chart lies in the kernel ideal exactly when the morphism
kills it. -/
theorem mem_kerIdeal {A C : AlgebraSheaf.{u, u} B S hS F hF} (f : A ⟶ C)
    (U : (SmallEtale B S hS F)ᵒᵖ) (a : A.right.obj.obj U) :
    a ∈ (kerIdeal f).obj U ↔ (f.right.hom.app U).hom a = 0 :=
  (SheafOfModules.mem_kerIdeal (ringCatHom f) U a).trans RingHom.mem_ker

/-- The sections of an ideal contained in the kernel ideal are killed by the morphism. -/
theorem apply_eq_zero_of_le_kerIdeal {A C : AlgebraSheaf.{u, u} B S hS F hF} (f : A ⟶ C)
    {I : A.IdealSheaf} (hI : I ≤ kerIdeal f) (U : (SmallEtale B S hS F)ᵒᵖ)
    (a : A.right.obj.obj U) (ha : a ∈ I.obj U) :
    (f.right.hom.app U).hom a = 0 :=
  (mem_kerIdeal f U a).1 (SheafOfModules.Submodule.le_iff.1 hI U ha)

/-- **The quotient morphism kills the ideal it divides by.**  Over an étale chart the quotient
morphism is the class map followed by the comparison with the sheafification, and the class of a
section of `I` is zero. -/
theorem toIdealQuotient_apply_eq_zero (A : AlgebraSheaf.{u, u} B S hS F hF) (I : A.IdealSheaf)
    (U : (SmallEtale B S hS F)ᵒᵖ) (a : A.right.obj.obj U) (ha : a ∈ I.obj U) :
    ((A.toIdealQuotient I).right.hom.app U).hom a = 0 := by
  have h0 : ((Stacks.Sites.toQuotientPresheaf.{u, u + 1, u} I).app U).hom a = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 ha
  show ((toSheafify (SmallEtale.topology B S hS F)
      (Stacks.Sites.quotientPresheaf.{u, u + 1, u} I)).app U).hom
      (((Stacks.Sites.toQuotientPresheaf.{u, u + 1, u} I).app U).hom a) = 0
  rw [h0, map_zero]

/-- The ideal divided by is contained in the kernel ideal of the quotient morphism. -/
theorem le_kerIdeal_toIdealQuotient (A : AlgebraSheaf.{u, u} B S hS F hF) (I : A.IdealSheaf) :
    I ≤ kerIdeal (A.toIdealQuotient I) :=
  SheafOfModules.Submodule.le_iff.2 fun U _ ha =>
    (mem_kerIdeal (A.toIdealQuotient I) U _).2 (toIdealQuotient_apply_eq_zero A I U _ ha)

/-! ### The universal property of `A/I` -/

section Lift

variable {A C : AlgebraSheaf.{u, u} B S hS F hF} (f : A ⟶ C) (I : A.IdealSheaf)
    (hI : ∀ (U : (SmallEtale B S hS F)ᵒᵖ) (a : A.right.obj.obj U), a ∈ I.obj U →
      (f.right.hom.app U).hom a = 0)

/-- The factorization of `f` through the *objectwise* quotient `U ↦ A(U)/I(U)`, by the universal
property of a quotient ring over each étale chart. -/
def idealQuotientPresheafLift :
    Stacks.Sites.quotientPresheaf.{u, u + 1, u} I ⟶ C.right.obj where
  app U := CommRingCat.ofHom
    (Ideal.Quotient.lift (Stacks.Sites.sectionIdeal I U) (f.right.hom.app U).hom
      fun a ha => hI U a ha)
  naturality {U V} g := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ConcreteCategory.congr_hom (f.right.hom.naturality g) a

/-- The objectwise factorization takes the class of a section `a` of `A` to `f a`. -/
@[simp]
theorem idealQuotientPresheafLift_app_mk (U : (SmallEtale B S hS F)ᵒᵖ)
    (a : A.right.obj.obj U) :
    ((idealQuotientPresheafLift f I hI).app U).hom
        (Ideal.Quotient.mk (Stacks.Sites.sectionIdeal I U) a) =
      (f.right.hom.app U).hom a :=
  rfl

/-- **The sheafified factorization still takes the class of a section `a` of `A` to `f a`.**
This is `CategoryTheory.toSheafify_sheafifyLift` read on the sections over an étale chart. -/
theorem sheafifyLift_toQuotientRingSheaf_apply (U : (SmallEtale B S hS F)ᵒᵖ)
    (a : A.right.obj.obj U) :
    ((sheafifyLift (SmallEtale.topology B S hS F)
          (idealQuotientPresheafLift f I hI) C.right.property).app U).hom
        (((Stacks.Sites.toQuotientRingSheaf.{u, u + 1, u} I).hom.app U).hom a) =
      (f.right.hom.app U).hom a :=
  congrArg
    (fun η : Stacks.Sites.quotientPresheaf.{u, u + 1, u} I ⟶ C.right.obj =>
      (η.app U).hom ((Stacks.Sites.toQuotientPresheaf.{u, u + 1, u} I).app U a))
    (toSheafify_sheafifyLift (SmallEtale.topology B S hS F)
      (idealQuotientPresheafLift f I hI) C.right.property)

/-- **The factorization of a morphism killing `I` through `A/I`**, as a morphism of algebra
sheaves: the objectwise factorization carried across the sheafification. -/
def idealQuotientLift : A.idealQuotient I ⟶ C where
  right := ⟨sheafifyLift (SmallEtale.topology B S hS F)
    (idealQuotientPresheafLift f I hI) C.right.property⟩
  comm U r :=
    (sheafifyLift_toQuotientRingSheaf_apply f I hI U (A.algebraMap U r)).trans (f.comm U r)

/-- The underlying morphism of sheaves of rings of `idealQuotientLift f I hI` is the objectwise
factorization `idealQuotientPresheafLift f I hI` carried across the sheafification by
`CategoryTheory.sheafifyLift`. -/
@[simp]
theorem idealQuotientLift_right :
    (idealQuotientLift f I hI).right =
      ⟨sheafifyLift (SmallEtale.topology B S hS F)
        (idealQuotientPresheafLift f I hI) C.right.property⟩ :=
  rfl

/-- **The factorization does factor the morphism.** -/
theorem toIdealQuotient_comp_idealQuotientLift :
    A.toIdealQuotient I ≫ idealQuotientLift f I hI = f := by
  refine Hom.ext (Sheaf.hom_ext ?_)
  ext U : 2
  apply CommRingCat.hom_ext
  exact RingHom.ext fun a => sheafifyLift_toQuotientRingSheaf_apply f I hI U a

end Lift

/-! ### Uniqueness of the factorization -/

/-- **Two morphisms out of `A/I` which agree after composition with the quotient morphism are
equal.**  A morphism out of a sheafification is determined by its restriction along
`CategoryTheory.toSheafify`, and a morphism out of the objectwise quotient is determined by its
composite with the objectwise quotient map, which is surjective on sections. -/
theorem idealQuotient_hom_ext {A C : AlgebraSheaf.{u, u} B S hS F hF} {I : A.IdealSheaf}
    {g h : A.idealQuotient I ⟶ C}
    (e : A.toIdealQuotient I ≫ g = A.toIdealQuotient I ≫ h) : g = h := by
  refine Hom.ext (Sheaf.hom_ext ?_)
  have key : ∀ (U : (SmallEtale B S hS F)ᵒᵖ) (a : A.right.obj.obj U),
      (g.right.hom.app U).hom
          (((Stacks.Sites.toQuotientRingSheaf.{u, u + 1, u} I).hom.app U).hom a) =
        (h.right.hom.app U).hom
          (((Stacks.Sites.toQuotientRingSheaf.{u, u + 1, u} I).hom.app U).hom a) :=
    fun U a => congrArg (fun k : A ⟶ C => (k.right.hom.app U).hom a) e
  refine sheafify_hom_ext (SmallEtale.topology B S hS F) _ _ C.right.property ?_
  ext U : 2
  apply CommRingCat.hom_ext
  refine RingHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := Stacks.Sites.toQuotientPresheaf_app_surjective.{u, u + 1, u} I U x
  exact key U a

/-! ### The image factorization of a morphism of algebra sheaves -/

/-- **The second half `A/ker f ⟶ C` of the image factorization of a morphism of algebra sheaves
on an algebraic space.** -/
def imageFactorizationHom {A C : AlgebraSheaf.{u, u} B S hS F hF} (f : A ⟶ C) :
    A.idealQuotient (kerIdeal f) ⟶ C :=
  idealQuotientLift f (kerIdeal f) fun U a ha => (mem_kerIdeal f U a).1 ha

/-- **The image factorization `A ⟶ A/ker f ⟶ C`.** -/
theorem toIdealQuotient_comp_imageFactorizationHom
    {A C : AlgebraSheaf.{u, u} B S hS F hF} (f : A ⟶ C) :
    A.toIdealQuotient (kerIdeal f) ≫ imageFactorizationHom f = f :=
  toIdealQuotient_comp_idealQuotientLift f (kerIdeal f) _

/-! ### The two laws of a system of quotients -/

/-- The factorization is compatible with a further morphism out of the target. -/
theorem idealQuotientLift_comp {A C D : AlgebraSheaf.{u, u} B S hS F hF} (f : A ⟶ C) (g : C ⟶ D)
    (I : A.IdealSheaf)
    (hI : ∀ (U : (SmallEtale B S hS F)ᵒᵖ) (a : A.right.obj.obj U), a ∈ I.obj U →
      (f.right.hom.app U).hom a = 0)
    (hIg : ∀ (U : (SmallEtale B S hS F)ᵒᵖ) (a : A.right.obj.obj U), a ∈ I.obj U →
      ((f ≫ g).right.hom.app U).hom a = 0) :
    idealQuotientLift (f ≫ g) I hIg = idealQuotientLift f I hI ≫ g := by
  refine idealQuotient_hom_ext ?_
  rw [toIdealQuotient_comp_idealQuotientLift, ← Category.assoc,
    toIdealQuotient_comp_idealQuotientLift]

/-- The factorization is compatible with an enlargement of the ideal: dividing by the smaller
ideal and then comparing is dividing by the larger one. -/
theorem idealQuotientMapOfLE_comp_idealQuotientLift
    {A C : AlgebraSheaf.{u, u} B S hS F hF} (f : A ⟶ C) {I I' : A.IdealSheaf} (h : I ≤ I')
    (hI : ∀ (U : (SmallEtale B S hS F)ᵒᵖ) (a : A.right.obj.obj U), a ∈ I.obj U →
      (f.right.hom.app U).hom a = 0)
    (hI' : ∀ (U : (SmallEtale B S hS F)ᵒᵖ) (a : A.right.obj.obj U), a ∈ I'.obj U →
      (f.right.hom.app U).hom a = 0) :
    idealQuotientMapOfLE h ≫ idealQuotientLift f I' hI' = idealQuotientLift f I hI := by
  refine idealQuotient_hom_ext ?_
  rw [← Category.assoc, toIdealQuotient_comp_idealQuotientMapOfLE,
    toIdealQuotient_comp_idealQuotientLift, toIdealQuotient_comp_idealQuotientLift]

end AlgebraSheaf

end AlgebraicGeometry.Space

end
