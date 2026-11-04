module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Subobject.Limits
public import StacksFrontier.CategoryTheory.FilteredDerived.Category.Opposite

/-!
# Conjugating a quotient by a comparison of a functor with a composite

Let `P₁ : C ⥤ D₁` and `P₂ : C ⥤ D₂` be functors into abelian categories and let
`e : P₂ ≅ P₁ ⋙ L` compare `P₂` with `P₁` followed by a further functor `L : D₁ ⥤ D₂`.  A
quotient of `P₁ M`, recorded by its kernel as a subobject `K`, then has a *conjugate* quotient
of `P₂ M`: the image under `L` of the projection `P₁ M ⟶ P₁ M / K`, read through `e`, is a map
out of `P₂ M`, and the conjugate quotient is recorded by its kernel.

This is `CategoryTheory.Functor.conjHom` with quotients in place of homomorphisms, and is the
shape of every "base change of a quotient" construction indexed by a category of test objects,
where `P₂` is the pullback to the base change at `T'`, `P₁` the pullback at `T`, and `L` the
pullback along the induced map of base changes.  The two results below are what make such a
construction functorial in the test object.

## Main definitions

* `CategoryTheory.Functor.conjQuotientProjection`: the projection of `P₂ M` onto the image
  under `L` of the quotient.
* `CategoryTheory.Functor.conjSubobject`: the conjugate of a quotient, recorded by its kernel.
* `CategoryTheory.Functor.conjSubobjectCokernelIso`: the quotient by the conjugate subobject is
  the image under `L` of the original quotient.

## Main results

* `CategoryTheory.Limits.kernelSubobject_cokernel_π`: the kernel of the projection onto the
  quotient by a subobject is that subobject again.
* `CategoryTheory.Functor.conjSubobject_id`: the unit law.
* `CategoryTheory.Functor.conjSubobject_comp`: the composition law.

## Implementation notes

Both laws take the factorisation of the comparison as a hypothesis rather than rewriting with
it, as `CategoryTheory.Functor.conjHom_id` and `CategoryTheory.Functor.conjHom_comp` do and for
the same reason: a consumer applies them to a comparison it has already named, and the
conclusion then matches its goal with no unfolding.

A subobject does not pull back along `L`, because `L` need not preserve monomorphisms; what
pulls back is the *quotient*, and the conjugate subobject is recovered from it as a kernel.
This is why `L` is asked to preserve epimorphisms rather than to be exact: the conjugate of a
quotient is again a quotient, and nothing more is needed.  Reading off the conjugate subobject
from the conjugate quotient is `CategoryTheory.Abelian.cokernelKernelSubobjectIso`, and the
whole proof of both laws is that the two presentations of the conjugate quotient that each law
compares differ by an isomorphism of its target, which leaves the kernel subobject unchanged by
`CategoryTheory.Limits.kernelSubobject_comp_mono`.
-/

@[expose] public section

open CategoryTheory.Limits

namespace CategoryTheory

namespace Limits

variable {C : Type*} [Category* C]

/-- Postcomposing with a monomorphism that identifies the two targets does not change the
kernel subobject. -/
theorem kernelSubobject_eq_of_comp_mono [HasZeroMorphisms C] [HasKernels C] {A Q Q' : C}
    (p : A ⟶ Q) (p' : A ⟶ Q') (i : Q ⟶ Q') [Mono i] (h : p ≫ i = p') :
    kernelSubobject p' = kernelSubobject p := by
  rw [← h, kernelSubobject_comp_mono]

/-- **The kernel of the projection onto the quotient by a subobject is that subobject again.**
Together with surjectivity of the projection this says that the subobjects of an object list
its quotients once each. -/
theorem kernelSubobject_cokernel_π [Abelian C] {A : C} (K : Subobject A) :
    kernelSubobject (cokernel.π K.arrow) = K :=
  (Subobject.mk_eq_mk_of_comm K.arrow (kernel.ι (cokernel.π K.arrow))
    (Abelian.isoKernelCokernel K.arrow)
    (Abelian.isoKernelCokernel_hom_comp K.arrow)).symm.trans (Subobject.mk_arrow K)

/-- Precomposing the target of a cokernel projection with an epimorphism does not change the
kernel subobject of its composite with `a`. -/
private theorem kernelSubobject_comp_cokernel_π_eq_of_epi [Abelian C] {X Y Z W : C} (a : W ⟶ Z)
    (f : X ⟶ Z) (g : Y ⟶ Z) (ε : X ⟶ Y) [Epi ε] (h : ε ≫ g = f) :
    kernelSubobject (a ≫ cokernel.π g) = kernelSubobject (a ≫ cokernel.π f) := by
  refine kernelSubobject_eq_of_comp_mono _ _
    ((cokernelIsoOfEq h.symm).hom ≫ (cokernelEpiComp ε g).hom) ?_
  rw [Category.assoc, ← Category.assoc (cokernel.π f), π_comp_cokernelIsoOfEq_hom]
  simp

end Limits

namespace Functor

variable {C : Type*} {D₀ : Type*} {D₁ : Type*} {D₂ : Type*}
  [Category* C] [Category* D₀] [Category* D₁] [Category* D₂]
  [Abelian D₀] [Abelian D₁] [Abelian D₂]

section

variable {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂}

/-- The projection of `P₂ M` onto the image under `L` of the quotient of `P₁ M` by a subobject
`K`: the image under `L` of the projection onto the quotient, read through the comparison
`e : P₂ ≅ P₁ ⋙ L` at its source. -/
noncomputable def conjQuotientProjection (e : P₂ ≅ P₁ ⋙ L) {M : C} (K : Subobject (P₁.obj M)) :
    P₂.obj M ⟶ L.obj (cokernel K.arrow) :=
  e.hom.app M ≫ L.map (cokernel.π K.arrow)

/-- The conjugate of a quotient is a quotient: the projection onto it is an epimorphism. -/
instance epi_conjQuotientProjection (e : P₂ ≅ P₁ ⋙ L) [L.PreservesEpimorphisms] {M : C}
    (K : Subobject (P₁.obj M)) : Epi (conjQuotientProjection e K) := by
  rw [conjQuotientProjection]
  infer_instance

/-- **The conjugate of a quotient of `P₁ M` by a comparison `e : P₂ ≅ P₁ ⋙ L`**, recorded by
its kernel: the subobject of `P₂ M` which is the kernel of
`CategoryTheory.Functor.conjQuotientProjection`. -/
noncomputable def conjSubobject (e : P₂ ≅ P₁ ⋙ L) {M : C} (K : Subobject (P₁.obj M)) :
    Subobject (P₂.obj M) :=
  kernelSubobject (conjQuotientProjection e K)

/-- **The quotient by the conjugate subobject is the image under `L` of the quotient.** -/
noncomputable def conjSubobjectCokernelIso (e : P₂ ≅ P₁ ⋙ L) [L.PreservesEpimorphisms] {M : C}
    (K : Subobject (P₁.obj M)) :
    cokernel (conjSubobject e K).arrow ≅ L.obj (cokernel K.arrow) :=
  Abelian.cokernelKernelSubobjectIso (conjQuotientProjection e K)

/-- The projection onto the quotient by the conjugate subobject is the projection onto the
image under `L` of the quotient, read through
`CategoryTheory.Functor.conjSubobjectCokernelIso`. -/
theorem cokernel_π_comp_conjSubobjectCokernelIso_hom (e : P₂ ≅ P₁ ⋙ L)
    [L.PreservesEpimorphisms] {M : C} (K : Subobject (P₁.obj M)) :
    cokernel.π (conjSubobject e K).arrow ≫ (conjSubobjectCokernelIso e K).hom =
      conjQuotientProjection e K := by
  dsimp only [conjSubobjectCokernelIso, conjSubobject]
  rw [← Abelian.cokernelKernelSubobjectIso_inv_comp (conjQuotientProjection e K)]
  simp

/-- **The conjugate of a quotient, identified by a surjection onto a submodule.**  Let
`e : P₂ ≅ P₁ ⋙ L` be a comparison with `L` preserving finite colimits, let `K` be a subobject of
`P₁ M` and let `m : I ⟶ P₂ M` be a subobject of `P₂ M`.  If the image of `K` under `L`, read in
`P₂ M` through `e`, factors through `m` by an *epimorphism*, then the conjugate of the quotient
of `P₁ M` by `K` is the quotient of `P₂ M` by `m`.

This is the only form in which the conjugate subobject can be computed: `L` need not preserve
monomorphisms, so `L K` is not a subobject of `P₂ M` and the conjugate is its *image* — which,
`L` being right exact, is the kernel of `L` applied to the projection onto the quotient.  Given
the epimorphism, that image is the image of `m`, which is `m`.

The two side conditions are explicit arguments rather than instances: a consumer in a category of
sheaves of modules has to supply them by hand, instance search there failing to match either of
the two `rfl`-equal spellings of the ambient category. -/
theorem conjSubobject_eq_mk_of_epi (e : P₂ ≅ P₁ ⋙ L) [PreservesFiniteColimits L] {M : C}
    (K : Subobject (P₁.obj M)) {I : D₂} (m : I ⟶ P₂.obj M) (hm : Mono m)
    (ε : L.obj (K : D₁) ⟶ I) (he : Epi ε) (hε : ε ≫ m ≫ e.hom.app M = L.map K.arrow) :
    conjSubobject e K = @Subobject.mk _ _ _ _ m hm := by
  dsimp only [conjSubobject, conjQuotientProjection]
  have h1 : kernelSubobject (e.hom.app M ≫ cokernel.π (L.map K.arrow)) =
      kernelSubobject (e.hom.app M ≫ L.map (cokernel.π K.arrow)) := by
    refine kernelSubobject_eq_of_comp_mono _ _ (PreservesCokernel.iso L K.arrow).hom ?_
    rw [Category.assoc, PreservesCokernel.π_iso_hom]
  have h2 : kernelSubobject (e.hom.app M ≫ cokernel.π (m ≫ e.hom.app M)) =
      kernelSubobject (e.hom.app M ≫ cokernel.π (L.map K.arrow)) :=
    kernelSubobject_comp_cokernel_π_eq_of_epi _ _ _ ε hε
  have h3 : kernelSubobject (cokernel.π m) =
      kernelSubobject (e.hom.app M ≫ cokernel.π (m ≫ e.hom.app M)) := by
    refine kernelSubobject_eq_of_comp_mono _ _ (cokernelCompIsIso m (e.hom.app M)).hom ?_
    rw [Category.assoc]
    simp
  have h4 : kernelSubobject (cokernel.π (Subobject.mk m).arrow) =
      kernelSubobject (cokernel.π m) := by
    simpa using kernelSubobject_comp_cokernel_π_eq_of_epi (𝟙 _) m (Subobject.mk m).arrow
      (Subobject.underlyingIso m).inv (Subobject.underlyingIso_arrow m).symm.symm
  rw [← h1, ← h2, ← h3, ← h4, kernelSubobject_cokernel_π]

end

/-- **The unit law for conjugation of quotients.**  Conjugating by a comparison that is
whiskering `P` with an isomorphism `𝟭 ≅ L` leaves the subobject unchanged. -/
theorem conjSubobject_id {P : C ⥤ D₁} {L : D₁ ⥤ D₁} (γ : 𝟭 D₁ ≅ L) (e : P ≅ P ⋙ L)
    (hfac : e = (rightUnitor P).symm ≪≫ isoWhiskerLeft P γ) {M : C}
    (K : Subobject (P.obj M)) : conjSubobject e K = K := by
  subst hfac
  refine (kernelSubobject_eq_of_comp_mono (cokernel.π K.arrow)
    (conjQuotientProjection _ K) (γ.hom.app (cokernel K.arrow)) ?_).trans
    (kernelSubobject_cokernel_π K)
  simp only [conjQuotientProjection, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, whiskerLeft_app, rightUnitor_inv_app, Category.id_comp]
  exact γ.hom.naturality (cokernel.π K.arrow)

/-- **The composition law for conjugation of quotients.**  If the comparison `c : P₂ ≅ P₀ ⋙ L`
factors through comparisons `c₁ : P₁ ≅ P₀ ⋙ L₁` and `c₂ : P₂ ≅ P₁ ⋙ L₂` and an identification
`τ : L ≅ L₁ ⋙ L₂`, then conjugating by `c` is conjugating by `c₁` and then by `c₂`. -/
theorem conjSubobject_comp {P₀ : C ⥤ D₀} {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂}
    {L₁ : D₀ ⥤ D₁} {L₂ : D₁ ⥤ D₂} {L : D₀ ⥤ D₂} [L₁.PreservesEpimorphisms]
    (c₁ : P₁ ≅ P₀ ⋙ L₁) (c₂ : P₂ ≅ P₁ ⋙ L₂) (c : P₂ ≅ P₀ ⋙ L) (τ : L ≅ L₁ ⋙ L₂)
    (hfac : c = (c₂ ≪≫ isoWhiskerRight c₁ L₂ ≪≫ associator P₀ L₁ L₂) ≪≫
      (isoWhiskerLeft P₀ τ).symm)
    {M : C} (K : Subobject (P₀.obj M)) :
    conjSubobject c K = conjSubobject c₂ (conjSubobject c₁ K) := by
  set W : P₂.obj M ⟶ L₂.obj (L₁.obj (cokernel K.arrow)) :=
    c₂.hom.app M ≫ L₂.map (c₁.hom.app M) ≫ L₂.map (L₁.map (cokernel.π K.arrow)) with hW
  have hleft : conjSubobject c K = kernelSubobject W := by
    refine kernelSubobject_eq_of_comp_mono W (conjQuotientProjection c K)
      (τ.inv.app (cokernel K.arrow)) ?_
    subst hfac
    simp only [conjQuotientProjection, hW, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      isoWhiskerRight_hom, whiskerRight_app, isoWhiskerLeft_inv, whiskerLeft_app,
      associator_hom_app, Category.id_comp, Category.assoc]
    have hnat := τ.inv.naturality (cokernel.π K.arrow)
    simp only [Functor.comp_map] at hnat
    rw [hnat]
  have hright : conjSubobject c₂ (conjSubobject c₁ K) = kernelSubobject W := by
    refine (kernelSubobject_eq_of_comp_mono (conjQuotientProjection c₂ (conjSubobject c₁ K)) W
      (L₂.map (conjSubobjectCokernelIso c₁ K).hom) ?_).symm
    simp only [conjQuotientProjection, hW, Category.assoc, ← Functor.map_comp]
    rw [cokernel_π_comp_conjSubobjectCokernelIso_hom c₁ K]
    simp [conjQuotientProjection]
  rw [hleft, hright]

end Functor

end CategoryTheory

end
