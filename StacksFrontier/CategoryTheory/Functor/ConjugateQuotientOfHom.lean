module

public import StacksFrontier.CategoryTheory.Functor.ConjugateQuotient

/-!
# The image of a quotient under a comparison morphism

Let `P₁ : C ⥤ D₁` and `P₂ : C ⥤ D₂` be functors into abelian categories and let
`e : P₂ ⟶ P₁ ⋙ L` be a comparison *morphism* of `P₂` with `P₁` followed by `L : D₁ ⥤ D₂`.  A
quotient of `P₁ M`, recorded by its kernel `K`, has an image in `P₂ M`: the map
`P₂ M ⟶ L (P₁ M) ⟶ L (P₁ M / K)`, recorded by its kernel.  When `e` is an isomorphism this is
`CategoryTheory.Functor.conjSubobject`; the point of allowing a morphism is that in the geometric
applications `e` is a base change map, invertible only at some objects, and `L` is right exact
only on some objects, so whether the image is again a quotient is a property of `M` and `K`
rather than of `e` and `L`.

## Main definitions

* `CategoryTheory.Functor.conjQuotientProjectionOfHom`: the map `P₂ M ⟶ L (P₁ M / K)`.
* `CategoryTheory.Functor.conjSubobjectOfHom`: its kernel.
* `CategoryTheory.Functor.conjSubobjectOfHomCokernelIso`: when the map is an epimorphism, the
  quotient of `P₂ M` by its kernel is `L (P₁ M / K)`.

## Main results

* `CategoryTheory.Functor.conjSubobjectOfHom_conjSubobject`: compatibility with a further
  conjugation.  For comparison morphisms `b₁ : f ⋙ g ⟶ g' ⋙ f'`, `b₂ : f' ⋙ h ⟶ h' ⋙ f''` and
  `b : f ⋙ k ⟶ k' ⋙ f''` and comparison isomorphisms `t : k ≅ g ⋙ h`, `t' : k' ≅ g' ⋙ h'`
  satisfying the pasting identity, the image under `b` of the conjugate of `K` by `t'` is the
  conjugate by `t` of the image of `K` under `b₁`, provided the image under `b₁` is a quotient and
  `b₂` is invertible at `g' M / K`.

## Implementation notes

As in `StacksFrontier/CategoryTheory/Functor/ConjugateQuotient.lean`, every comparison of kernel
subobjects is made by `CategoryTheory.Limits.kernelSubobject_eq_of_comp_mono`: two maps out of the
same object differing by postcomposition with a monomorphism have the same kernel.
-/

@[expose] public section

open CategoryTheory.Limits

namespace CategoryTheory.Functor

section ConjOfHom

variable {C : Type*} {D₁ : Type*} {D₂ : Type*} [Category* C] [Category* D₁] [Category* D₂]
  [Abelian D₁] [Abelian D₂] {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂}

/-- The projection of `P₂ M` onto the image under `L` of the quotient of `P₁ M` by a subobject
`K`, read through a comparison *morphism* `e : P₂ ⟶ P₁ ⋙ L`. -/
noncomputable def conjQuotientProjectionOfHom (e : P₂ ⟶ P₁ ⋙ L) {M : C}
    (K : Subobject (P₁.obj M)) : P₂.obj M ⟶ L.obj (cokernel K.arrow) :=
  e.app M ≫ L.map (cokernel.π K.arrow)

/-- The image under `L` of a quotient of `P₁ M`, read through a comparison morphism
`e : P₂ ⟶ P₁ ⋙ L` and recorded by its kernel. When `e` is an isomorphism this is
`CategoryTheory.Functor.conjSubobject`. -/
noncomputable def conjSubobjectOfHom (e : P₂ ⟶ P₁ ⋙ L) {M : C} (K : Subobject (P₁.obj M)) :
    Subobject (P₂.obj M) :=
  kernelSubobject (conjQuotientProjectionOfHom e K)

/-- The quotient by `CategoryTheory.Functor.conjSubobjectOfHom` is the image under `L` of the
quotient, when the projection onto it is an epimorphism. -/
noncomputable def conjSubobjectOfHomCokernelIso (e : P₂ ⟶ P₁ ⋙ L) {M : C}
    (K : Subobject (P₁.obj M)) (h : Epi (conjQuotientProjectionOfHom e K)) :
    cokernel (conjSubobjectOfHom e K).arrow ≅ L.obj (cokernel K.arrow) :=
  Abelian.cokernelKernelSubobjectIso (conjQuotientProjectionOfHom e K)

/-- The projection onto the quotient by `CategoryTheory.Functor.conjSubobjectOfHom` is the
projection onto the image under `L` of the quotient, read through
`CategoryTheory.Functor.conjSubobjectOfHomCokernelIso`. -/
theorem cokernel_π_comp_conjSubobjectOfHomCokernelIso_hom (e : P₂ ⟶ P₁ ⋙ L) {M : C}
    (K : Subobject (P₁.obj M)) (h : Epi (conjQuotientProjectionOfHom e K)) :
    cokernel.π (conjSubobjectOfHom e K).arrow ≫ (conjSubobjectOfHomCokernelIso e K h).hom =
      conjQuotientProjectionOfHom e K := by
  dsimp only [conjSubobjectOfHomCokernelIso, conjSubobjectOfHom]
  rw [← Abelian.cokernelKernelSubobjectIso_inv_comp (conjQuotientProjectionOfHom e K),
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

end ConjOfHom

section BaseChange

variable {A : Type*} {A' : Type*} {A'' : Type*} {E : Type*} {E' : Type*} {E'' : Type*}
  [Category* A] [Category* A'] [Category* A''] [Category* E] [Category* E'] [Category* E'']
  [Abelian A'] [Abelian A''] [Abelian E'] [Abelian E'']

/-- **The image of quotients under a comparison morphism commutes with a further conjugation.**
Let `b₁ : f ⋙ g ⟶ g' ⋙ f'`, `b₂ : f' ⋙ h ⟶ h' ⋙ f''` and `b : f ⋙ k ⟶ k' ⋙ f''` be comparison
morphisms and `t : k ≅ g ⋙ h`, `t' : k' ≅ g' ⋙ h'` comparison isomorphisms satisfying the pasting
identity at `M`. For a subobject `K` of `g' M` whose image under `b₁` is a quotient and at whose
quotient `b₂` is invertible, transporting `K` along `t'` and then taking its image under `b` is
taking its image under `b₁` and then transporting along `t`. -/
theorem conjSubobjectOfHom_conjSubobject {f : A ⥤ E} {g : E ⥤ E'} {g' : A ⥤ A'} {f' : A' ⥤ E'}
    {h : E' ⥤ E''} {h' : A' ⥤ A''} {f'' : A'' ⥤ E''} {k : E ⥤ E''} {k' : A ⥤ A''}
    [h.PreservesEpimorphisms] [h'.PreservesEpimorphisms]
    (b₁ : f ⋙ g ⟶ g' ⋙ f') (b₂ : f' ⋙ h ⟶ h' ⋙ f'') (b : f ⋙ k ⟶ k' ⋙ f'')
    (t : k ≅ g ⋙ h) (t' : k' ≅ g' ⋙ h') (M : A)
    (hpaste : t.hom.app (f.obj M) ≫ h.map (b₁.app M) ≫ b₂.app (g'.obj M) =
      b.app M ≫ f''.map (t'.hom.app M))
    (K : Subobject (g'.obj M)) (hepi : Epi (conjQuotientProjectionOfHom b₁ K))
    (hiso : IsIso (b₂.app (cokernel K.arrow))) :
    conjSubobjectOfHom b (conjSubobject t' K) = conjSubobject t (conjSubobjectOfHom b₁ K) := by
  set W : (f ⋙ k).obj M ⟶ f''.obj (h'.obj (cokernel K.arrow)) :=
    b.app M ≫ f''.map (t'.hom.app M) ≫ f''.map (h'.map (cokernel.π K.arrow)) with hW
  have hleft : conjSubobjectOfHom b (conjSubobject t' K) = kernelSubobject W := by
    refine (kernelSubobject_eq_of_comp_mono _ W
      (f''.map (conjSubobjectCokernelIso t' K).hom) ?_).symm
    simp only [conjQuotientProjectionOfHom, hW, Category.assoc, ← Functor.map_comp,
      cokernel_π_comp_conjSubobjectCokernelIso_hom t' K, conjQuotientProjection]
  have hright : conjSubobject t (conjSubobjectOfHom b₁ K) = kernelSubobject W := by
    refine (kernelSubobject_eq_of_comp_mono _ W
      (h.map (conjSubobjectOfHomCokernelIso b₁ K hepi).hom ≫ b₂.app (cokernel K.arrow)) ?_).symm
    have hnat := b₂.naturality (cokernel.π K.arrow)
    simp only [Functor.comp_map] at hnat
    simp only [conjQuotientProjection, Category.assoc]
    rw [← Category.assoc (h.map (cokernel.π _)), ← Functor.map_comp,
      cokernel_π_comp_conjSubobjectOfHomCokernelIso_hom b₁ K hepi]
    simp only [conjQuotientProjectionOfHom, Functor.map_comp, Category.assoc, hnat, hW]
    rw [← Category.assoc (h.map (b₁.app M)), ← Category.assoc (t.hom.app _), hpaste]
    simp only [Category.assoc, Functor.comp_obj]
  rw [hleft, hright]

end BaseChange

end CategoryTheory.Functor

end
