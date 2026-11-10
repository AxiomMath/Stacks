module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomMapLeftConjugate
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportSheafHomComplex
public import StacksFrontier.Topology.Sheaves.Functors.Module.ExactSupportInternalHom

/-!
# The underived Stacks 0E2I identification, with its naturality as precomposition

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces.  The underived form of
[Stacks, Tag 0E2I] is the isomorphism of functors of the `𝒪_X`-module variable

`SheafHom_{𝒪_X}(i_* N, -) ≅ i_* SheafHom_{𝒪_Z}(N, ℰom(𝒪_Z, -))`,

`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.sheafHomPushforwardNatIso`,
and its naturality in `N` is available in *conjugate* form: both induced maps are
`CategoryTheory.conjugateEquiv` of the maps induced on the left adjoints.  The complex-level
constructions need the naturality in the other form, with the induced maps spelled as
precomposition on internal Hom sheaves.  This file carries the conjugates across, and so
constructs the datum
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.PushforwardInternalHom`
outright.

Both identifications rest on the same statement about the tensor--internal-Hom adjunction of
[Stacks, Tag 03EO]: the conjugate of `k ⊗_O -` is precomposition by `k`, the contravariant
functoriality of [Stacks, Tag 03EN] in the first variable.  On the left-hand side of 0E2I that
is the whole content.  On the right-hand side the adjunction is a threefold composite — pullback
along `i`, then tensoring by `N` on `Z`, then pushforward, against sheaf Hom with exact support,
then internal Hom out of `N`, then pushforward — and the conjugate of a transformation which is
whiskered into a composite adjunction is the whiskering of its conjugate, so the same statement
applies after stripping the outer two factors.

## Main definitions

* `Stacks.SheafOfModules.InternalHom.internalHomPrecompNatTrans`: precomposition in the first
  variable of the internal Hom sheaf, as a natural transformation of the internal-Hom functors
  of [Stacks, Tag 03EN], with the precomposition maps
  `Stacks.SheafOfModules.InternalHom.internalHomPrecomp` as its components.
* `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.pushforwardInternalHom`:
  **the underived form of [Stacks, Tag 0E2I] together with its naturality in `N` as
  precomposition on internal Hom sheaves**, so that the complex-level identification of
  `StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportSheafHomComplex` and the
  derived identifications depending on it are unconditional.

## Main results

* `CategoryTheory.conjugateEquiv_comp_left` and `CategoryTheory.conjugateEquiv_comp_right`:
  conjugation commutes with composing an adjunction on either side.  Whiskering a
  transformation of left adjoints into a composite adjunction whiskers its conjugate, on the
  left of the outer right adjoint and on the right of the inner one respectively.
* `CategoryTheory.Adjunction.comp_homEquiv_apply`: the hom-equivalence of a composite
  adjunction, applied.
* `CategoryTheory.isoInvCompCancel`: cancelling a pair of isomorphisms across a commuting
  square.
* `CategoryTheory.whiskerRight_whiskerLeft_app`: the component of a transformation whiskered on
  both sides.
* `Stacks.SheafOfModules.InternalHom.homEquiv_comp_sheafInternalHomMapLeft_sheafTensor`,
  `conjugateEquiv_sheafTensor_map` and `conjugateEquiv_sheafTensor_map_precomp`: the
  identification of the conjugate of `k ⊗_O -` with precomposition by `k`, for the adjunction of
  [Stacks, Tag 03EO] whose left adjoint is `Stacks.SheafOfModules.Tensor.sheafTensor`.
* `ClosedQuotientMorphismOfRingedSpaces.sheafHomPushforwardMap_eq` and
  `pushforwardSheafHomExactSupportMap_eq`, with their component forms
  `sheafHomPushforwardMap_app` and `pushforwardSheafHomExactSupportMap_app`: the two maps
  induced in `N` on the sides of the underived 0E2I isomorphism are precomposition by `i_* g`
  on `X` and the pushforward of precomposition by `g` on `Z`.  The second is reached in the two
  steps `pushforwardSheafHomExactSupportMap_eq_whiskerRight` and
  `conjugateEquiv_tensorPushforwardExactSupport`, which strip the two outer factors of the
  composite adjunction one at a time.

## Implementation notes

The identification for [Stacks, Tag 03EO] is available for the adjunction `tensorLeftAdjunction`,
whose left adjoint is the `tensorLeft` of the localized monoidal structure on sheaves of modules
(`Stacks.SheafOfModules.InternalHom.conjugateEquiv_tensoringLeft_map`), whereas the two
adjunctions assembled into the underived 0E2I isomorphism are stated for
`Stacks.SheafOfModules.Tensor.sheafTensor`.  The two differ by re-seating the left adjoint along
`SheafOfModules.sheafTensorIsoApp`, and that is undone on hom-equivalences by
`CategoryTheory.Adjunction.homEquiv_ofNatIsoLeft_apply` together with the naturality of
`SheafOfModules.sheafTensorNatIso` in the fixed tensor factor: no further comparison enters, and
in particular nothing about either tensor product is computed on sections.

`CategoryTheory.conjugateEquiv_comp_left` and `conjugateEquiv_comp_right` are proved by the
uniqueness criterion `CategoryTheory.conjugateEquiv_eq_of_homEquiv`: the hom-equivalence of
`CategoryTheory.Adjunction.comp` is the composite of the two hom-equivalences, so the
compatibility to be checked factors as the compatibility for the inner adjunction followed by
naturality of the outer one.  Only units are involved, never counits, which matters because the
counit of the tensor--internal-Hom adjunction is built from sheafification and is described on
sections nowhere in this chain.

The naturality in `N` recorded in `PushforwardInternalHom` is the naturality of the underived
isomorphism read at a fixed `𝒪_X`-module, which is why the two identifications are also given in
component form; the isomorphism's naturality in the `𝒪_X`-module variable is already part of its
being an isomorphism of functors.

Every component is read off either by instantiating a statement whose functors are abstract
(`CategoryTheory.whiskerRight_whiskerLeft_app`,
`Stacks.SheafOfModules.InternalHom.internalHomPrecompNatTrans_app`) or by `congrArg` at a fixed
spelling of the objects involved, and never by asking for a reduction underneath
`RingedSpaceModuleAdjunction.modulePushforward`.  This is why the precomposition transformation
is reassembled as `internalHomPrecompNatTrans`, whose component at `G` *is*
`internalHomPrecomp`, rather than used in the form
`Stacks.SheafOfModules.InternalHom.internalHomMapLeftNatTrans` the conjugation identification
produces it in: the two agree by `internalHomMapLeftNatTrans_eq`, but their components are the
same morphism in two spellings, and identifying those spellings inside the argument of a
pushforward functor forces that functor — a composite of sheafification, restriction of scalars
and the descent equivalence — to be unfolded, which exhausts the kernel's budget at these
universes.

## References

* [Stacks Project, Tag 0E2I](https://stacks.math.columbia.edu/tag/0E2I)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public section

open CategoryTheory MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry
open RingedSpaceModuleAdjunction

noncomputable section

/- The monoidal structure on sheaves of modules is stated at a sections universe `w` free of the
two site universes, so the instance term these proofs unfold is large. -/


namespace CategoryTheory

section Composition

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

/-- **Cancelling a pair of isomorphisms across a commuting square.**  Given a square
`a ≫ e₂.hom = e.hom ≫ b`, conjugating `a` by the two isomorphisms and then composing with
`f` is composing `b` with `f`.

Stated with the five objects abstract so that the cancellation can be performed by rewriting
even where the objects of interest are only definitionally the ones the isomorphisms are
spelled over. -/
theorem isoInvCompCancel {A A' B B' Z : D} (e : A' ≅ B') (e₂ : A ≅ B) (a : A' ⟶ A)
    (b : B' ⟶ B) (hab : a ≫ e₂.hom = e.hom ≫ b) (f : B ⟶ Z) :
    e.inv ≫ a ≫ e₂.hom ≫ f = b ≫ f := by
  rw [← Category.assoc a, hab, Category.assoc, Iso.inv_hom_id_assoc]

/-- **The hom-equivalence of a composite adjunction, applied.**  Transposing a morphism out of
`L₁ ⋙ L₂` is transposing it across the outer adjunction and then across the inner one. -/
theorem Adjunction.comp_homEquiv_apply {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (c : C) (Z : E) (f : (L₁ ⋙ L₂).obj c ⟶ Z) :
    (adj₁.comp adj₂).homEquiv c Z f =
      adj₁.homEquiv c (R₂.obj Z) (adj₂.homEquiv (L₁.obj c) Z f) := by
  rw [Adjunction.comp_homEquiv]
  rfl

/-- **Conjugation commutes with composing an adjunction on the outside.**  For a fixed
adjunction `L₁ ⊣ R₁` and two adjunctions `LA ⊣ RA`, `LB ⊣ RB` out of its target, the conjugate
of `α : LB ⟶ LA` whiskered into `L₁` is the conjugate of `α` whiskered by `R₁`. -/
theorem conjugateEquiv_comp_left {L₁ : C ⥤ D} {R₁ : D ⥤ C} {LA LB : D ⥤ E} {RA RB : E ⥤ D}
    (adj₁ : L₁ ⊣ R₁) (adjA : LA ⊣ RA) (adjB : LB ⊣ RB) (α : LB ⟶ LA) :
    conjugateEquiv (adj₁.comp adjA) (adj₁.comp adjB) (Functor.whiskerLeft L₁ α) =
      Functor.whiskerRight (conjugateEquiv adjA adjB α) R₁ := by
  refine conjugateEquiv_eq_of_homEquiv _ _ _ _ (fun c Z f ↦ ?_)
  rw [Adjunction.comp_homEquiv_apply, Adjunction.comp_homEquiv_apply]
  change adj₁.homEquiv c (RA.obj Z) (adjA.homEquiv (L₁.obj c) Z f) ≫
      R₁.map ((conjugateEquiv adjA adjB α).app Z) = _
  rw [← Adjunction.homEquiv_naturality_right]
  exact congrArg (adj₁.homEquiv c (RB.obj Z))
    (homEquiv_comp_conjugateEquiv adjA adjB α (L₁.obj c) Z f)

/-- **Conjugation commutes with composing an adjunction on the inside.**  For two adjunctions
`LA ⊣ RA`, `LB ⊣ RB` and a fixed adjunction `L₂ ⊣ R₂` out of their target, the conjugate of
`α : LB ⟶ LA` whiskered by `L₂` is the conjugate of `α` whiskered into `R₂`. -/
theorem conjugateEquiv_comp_right {LA LB : C ⥤ D} {RA RB : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    (adjA : LA ⊣ RA) (adjB : LB ⊣ RB) (adj₂ : L₂ ⊣ R₂) (α : LB ⟶ LA) :
    conjugateEquiv (adjA.comp adj₂) (adjB.comp adj₂) (Functor.whiskerRight α L₂) =
      Functor.whiskerLeft R₂ (conjugateEquiv adjA adjB α) := by
  refine conjugateEquiv_eq_of_homEquiv _ _ _ _ (fun c Z f ↦ ?_)
  rw [Adjunction.comp_homEquiv_apply, Adjunction.comp_homEquiv_apply]
  change adjA.homEquiv c (R₂.obj Z) (adj₂.homEquiv (LA.obj c) Z f) ≫
      (conjugateEquiv adjA adjB α).app (R₂.obj Z) = _
  rw [homEquiv_comp_conjugateEquiv adjA adjB α c (R₂.obj Z) (adj₂.homEquiv (LA.obj c) Z f)]
  exact congrArg (adjB.homEquiv c (R₂.obj Z))
    (Adjunction.homEquiv_naturality_left adj₂ (α.app c) f).symm

/-- **The component of a transformation whiskered on both sides.**  Stated with the three
functors abstract, so that reading the component off involves no reduction of any particular
functor. -/
theorem whiskerRight_whiskerLeft_app (A : C ⥤ D) {B B' : D ⥤ E} (γ : B ⟶ B') (P : E ⥤ C)
    (X : C) :
    (Functor.whiskerRight (Functor.whiskerLeft A γ) P).app X = P.map (γ.app (A.obj X)) :=
  rfl

end Composition

end CategoryTheory

namespace Stacks.SheafOfModules.InternalHom

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (R : Sheaf J CommRingCat.{max u v})
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

attribute [local instance] _root_.SheafOfModules.monoidalCategory
  _root_.SheafOfModules.monoidalClosed
  Stacks.SheafOfModules.Tensor.ringSheafPresheafMonoidalCategory

/-- **Re-seating the left adjoint, on hom-equivalences.**  The hom-equivalence of
`tensorLeftAdjunction` is the hom-equivalence of `sheafTensorHomAdjunction` applied after
`SheafOfModules.sheafTensorIso`, the two adjunctions differing exactly by re-seating the left
adjoint along `SheafOfModules.sheafTensorIsoApp`.

This is carried in a declaration of its own because the re-seating is checked definitionally
against the two spellings of the tensor product, and that check is the single most expensive
step of the identification below; given its own declaration it is paid for once. -/
private theorem homEquiv_tensorLeftAdjunction
    (F₀ G H : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf R))
    (f₀ : (tensorLeft F₀).obj G ⟶ H) :
    (tensorLeftAdjunction R F₀).homEquiv G H f₀ =
      (sheafTensorHomAdjunction R F₀).homEquiv G H
        ((_root_.SheafOfModules.sheafTensorIso R F₀ G).inv ≫ f₀) :=
  Adjunction.homEquiv_ofNatIsoLeft_apply (sheafTensorHomAdjunction R F₀)
    (_root_.SheafOfModules.sheafTensorIsoApp R F₀).symm f₀

/-- **Currying commutes with precomposition on the internal Hom sheaf**, for the adjunction of
Stacks 03EO whose left adjoint is `Stacks.SheafOfModules.Tensor.sheafTensor`.  For `k : F' ⟶ F`,
transposing `f : F ⊗_O G ⟶ H` across the adjunction for `F` and then precomposing by `k` on the
internal Hom sheaf is transposing `(k ⊗_O G) ≫ f` across the adjunction for `F'`.

This is `homEquiv_comp_sheafInternalHomMapLeft`, which is stated for the adjunction with its
left adjoint re-seated along `SheafOfModules.sheafTensorIsoApp`, read back through
`CategoryTheory.Adjunction.homEquiv_ofNatIsoLeft_apply` and the naturality of
`SheafOfModules.sheafTensorNatIso` in the fixed tensor factor. -/
theorem homEquiv_comp_sheafInternalHomMapLeft_sheafTensor
    {F F' : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf R)}
    (k : F' ⟶ F)
    (G H : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf R))
    (f : ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj F).obj G ⟶ H) :
    (sheafTensorHomAdjunction R F).homEquiv G H f ≫ sheafInternalHomMapLeft J R k =
      (sheafTensorHomAdjunction R F').homEquiv G H
        (((Stacks.SheafOfModules.Tensor.sheafTensor R).map k).app G ≫ f) := by
  have hnat : ((tensoringLeft _).map k).app G ≫
        (_root_.SheafOfModules.sheafTensorIso R F G).hom =
      (_root_.SheafOfModules.sheafTensorIso R F' G).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor R).map k).app G :=
    NatTrans.congr_app ((_root_.SheafOfModules.sheafTensorNatIso R).hom.naturality k) G
  have hA : ∀ (E : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf R))
      (g : ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj E).obj G ⟶ H),
      (sheafTensorHomAdjunction R E).homEquiv G H g =
        (tensorLeftAdjunction R E).homEquiv G H
          ((_root_.SheafOfModules.sheafTensorIso R E G).hom ≫ g) :=
    fun E g ↦ ((homEquiv_tensorLeftAdjunction R E G H _).trans
      (congrArg (fun z ↦ (sheafTensorHomAdjunction R E).homEquiv G H z)
        (Iso.inv_hom_id_assoc (_root_.SheafOfModules.sheafTensorIso R E G) g))).symm
  rw [hA F f, hA F', homEquiv_comp_sheafInternalHomMapLeft]
  exact congrArg (fun z ↦ (tensorLeftAdjunction R F').homEquiv G H z)
    ((Category.assoc _ _ f).symm.trans ((hnat =≫ f).trans (Category.assoc _ _ f)))

/-- **The conjugate of the tensor whiskering is precomposition on the internal Hom sheaf**, for
the adjunction of Stacks 03EO whose left adjoint is
`Stacks.SheafOfModules.Tensor.sheafTensor`.  This is
`conjugateEquiv_tensoringLeft_map` for that adjunction rather than for its re-seated form. -/
theorem conjugateEquiv_sheafTensor_map
    {F F' : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf R)}
    (k : F' ⟶ F) :
    conjugateEquiv (sheafTensorHomAdjunction R F) (sheafTensorHomAdjunction R F')
        ((Stacks.SheafOfModules.Tensor.sheafTensor R).map k) =
      internalHomMapLeftNatTrans R k :=
  conjugateEquiv_eq_of_homEquiv _ _ _ _
    (fun G H f ↦ homEquiv_comp_sheafInternalHomMapLeft_sheafTensor R k G H f)

section Precomp

variable {D : Type u} [Category.{u} D] (K : GrothendieckTopology D)
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (O : Sheaf K CommRingCat.{u})

/-- **Precomposition in the first variable of the internal Hom sheaf, as a natural
transformation.**  The components are the precomposition maps
`Stacks.SheafOfModules.InternalHom.internalHomPrecomp` *on the nose*; naturality is
associativity of composition on sections.

This duplicates `Stacks.SheafOfModules.InternalHom.internalHomMapLeftNatTrans` at the single
universe, with components spelled by `internalHomPrecomp`; the point of the duplicate is that
its component at `G` is the precomposition map syntactically, which is what lets a component be
read off under a pushforward functor without unfolding that functor. -/
def internalHomPrecompNatTrans
    {F F' : _root_.SheafOfModules.{u} (Tensor.ringSheaf O)} (f : F ⟶ F') :
    internalHomSecondFunctor.{u, u, u, u} K O F' ⟶
      internalHomSecondFunctor.{u, u, u, u} K O F where
  app G := internalHomPrecomp K O f G
  naturality {G H} h := by
    apply _root_.SheafOfModules.hom_ext
    apply _root_.PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    rfl

omit [K.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The component of `internalHomPrecompNatTrans` at `G` is the precomposition map. -/
theorem internalHomPrecompNatTrans_app
    {F F' : _root_.SheafOfModules.{u} (Tensor.ringSheaf O)} (f : F ⟶ F')
    (G : _root_.SheafOfModules.{u} (Tensor.ringSheaf O)) :
    (internalHomPrecompNatTrans K O f).app G = internalHomPrecomp K O f G :=
  rfl

section Conjugate

variable [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [K.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasWeakSheafify K AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The two assemblies of precomposition into a natural transformation agree. -/
theorem internalHomMapLeftNatTrans_eq
    {F F' : _root_.SheafOfModules.{u} (Tensor.ringSheaf O)} (f : F ⟶ F') :
    internalHomMapLeftNatTrans O f = internalHomPrecompNatTrans K O f :=
  NatTrans.ext (funext fun _ ↦ rfl)

omit [K.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The conjugate of the tensor whiskering is precomposition on the internal Hom sheaf**, with
the precomposition transformation spelled by `internalHomPrecompNatTrans`. -/
theorem conjugateEquiv_sheafTensor_map_precomp
    {F F' : _root_.SheafOfModules.{u} (Tensor.ringSheaf O)} (k : F' ⟶ F) :
    conjugateEquiv (sheafTensorHomAdjunction O F) (sheafTensorHomAdjunction O F')
        ((Stacks.SheafOfModules.Tensor.sheafTensor O).map k) =
      internalHomPrecompNatTrans K O k :=
  Eq.trans (conjugateEquiv_sheafTensor_map O k) (internalHomMapLeftNatTrans_eq K O k)

end Conjugate

end Precomp

end Stacks.SheafOfModules.InternalHom

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

open Stacks.SheafOfModules.InternalHom

universe u

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- **The map induced in `N` on the left-hand side of the underived Stacks 0E2I isomorphism is
precomposition with `i_* g`.**  Its conjugate description is the conjugate of `i_* g ⊗_{𝒪_X} -`,
and the conjugate of a tensor whiskering is precomposition on the internal Hom sheaf. -/
theorem sheafHomPushforwardMap_eq {N N' : SheafOfModules.{u} (structureSheafRing S.Z)}
    (g : N ⟶ N') :
    S.sheafHomPushforwardMap g =
      internalHomPrecompNatTrans (Opens.grothendieckTopology S.X.carrier) S.X.sheaf
        ((modulePushforward S.i).map g) :=
  conjugateEquiv_sheafTensor_map_precomp (Opens.grothendieckTopology S.X.carrier) S.X.sheaf
    ((modulePushforward S.i).map g)

/-- The same identification at a fixed `𝒪_X`-module `F`. -/
theorem sheafHomPushforwardMap_app {N N' : SheafOfModules.{u} (structureSheafRing S.Z)} (g : N ⟶ N')
    (F : SheafOfModules.{u} (structureSheafRing S.X)) :
    (S.sheafHomPushforwardMap g).app F =
      internalHomPrecomp (Opens.grothendieckTopology S.X.carrier) S.X.sheaf
        ((modulePushforward S.i).map g) F :=
  Eq.trans (NatTrans.congr_app (S.sheafHomPushforwardMap_eq g) F)
    (internalHomPrecompNatTrans_app (Opens.grothendieckTopology S.X.carrier) S.X.sheaf
      ((modulePushforward S.i).map g) F)

/-- **Stripping the pullback factor from the right-hand side of the underived Stacks 0E2I
isomorphism.**  The map induced in `N` is the conjugate, for the composite of the pullback
adjunction with the tensor--exact-support adjunction, of a transformation whiskered into the
pullback; so it is the conjugate for the inner adjunction alone, whiskered by pushforward. -/
theorem pushforwardSheafHomExactSupportMap_eq_whiskerRight
    {N N' : SheafOfModules.{u} (structureSheafRing S.Z)} (g : N ⟶ N') :
    S.pushforwardSheafHomExactSupportMap g =
      Functor.whiskerRight
        (conjugateEquiv (S.tensorPushforwardExactSupportAdjunction N')
          (S.tensorPushforwardExactSupportAdjunction N)
          (Functor.whiskerRight
            ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(S.Z).presheaf, (S.Z).IsSheaf⟩).map g)
            (modulePushforward S.i)))
        (modulePushforward S.i) :=
  conjugateEquiv_comp_left (modulePullbackPushforwardAdjunction S.i)
    (S.tensorPushforwardExactSupportAdjunction N')
    (S.tensorPushforwardExactSupportAdjunction N)
    (Functor.whiskerRight
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(S.Z).presheaf, (S.Z).IsSheaf⟩).map g)
      (modulePushforward S.i))

/-- **Stripping the pushforward factor as well.**  The conjugate for the composite of the
tensor--internal-Hom adjunction on `Z` with the exact-support adjunction, of the tensor
whiskering by `g` whiskered by pushforward, is the conjugate of the tensor whiskering itself
whiskered into sheaf Hom with exact support — and that conjugate is precomposition by `g`. -/
theorem conjugateEquiv_tensorPushforwardExactSupport
    {N N' : SheafOfModules.{u} (structureSheafRing S.Z)} (g : N ⟶ N') :
    conjugateEquiv (S.tensorPushforwardExactSupportAdjunction N')
        (S.tensorPushforwardExactSupportAdjunction N)
        (Functor.whiskerRight
          ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(S.Z).presheaf, (S.Z).IsSheaf⟩).map g)
          (modulePushforward S.i)) =
      Functor.whiskerLeft S.sheafHomExactSupport
        (internalHomPrecompNatTrans (Opens.grothendieckTopology S.Z.carrier) S.Z.sheaf g) :=
  Eq.trans
    (conjugateEquiv_comp_right (sheafTensorHomAdjunction S.Z.sheaf N')
      (sheafTensorHomAdjunction S.Z.sheaf N) S.modulePushforwardSheafHomExactSupportAdjunction
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(S.Z).presheaf, (S.Z).IsSheaf⟩).map g))
    (congrArg (fun γ ↦ Functor.whiskerLeft S.sheafHomExactSupport γ)
      (conjugateEquiv_sheafTensor_map_precomp (Opens.grothendieckTopology S.Z.carrier)
        S.Z.sheaf g))

/-- **The map induced in `N` on the right-hand side of the underived Stacks 0E2I isomorphism is
the pushforward of precomposition with `g`.**  Its conjugate description is the conjugate of
`i_*(g ⊗_{𝒪_Z} i^* -)`, which is the tensor whiskering by `g` whiskered into the threefold
composite adjunction; conjugation commutes with composing an adjunction on either side, so the
conjugate is the conjugate of the tensor whiskering, whiskered the same way. -/
theorem pushforwardSheafHomExactSupportMap_eq {N N' : SheafOfModules.{u} (structureSheafRing S.Z)}
    (g : N ⟶ N') :
    S.pushforwardSheafHomExactSupportMap g =
      Functor.whiskerRight
        (Functor.whiskerLeft S.sheafHomExactSupport
          (internalHomPrecompNatTrans (Opens.grothendieckTopology S.Z.carrier) S.Z.sheaf g))
        (modulePushforward S.i) :=
  Eq.trans (S.pushforwardSheafHomExactSupportMap_eq_whiskerRight g)
    (congrArg (fun γ ↦ Functor.whiskerRight γ (modulePushforward S.i))
      (S.conjugateEquiv_tensorPushforwardExactSupport g))

/-- The same identification at a fixed `𝒪_X`-module `F`. -/
theorem pushforwardSheafHomExactSupportMap_app {N N' : SheafOfModules.{u} (structureSheafRing S.Z)}
    (g : N ⟶ N') (F : SheafOfModules.{u} (structureSheafRing S.X)) :
    (S.pushforwardSheafHomExactSupportMap g).app F =
      (modulePushforward S.i).map
        (internalHomPrecomp (Opens.grothendieckTopology S.Z.carrier) S.Z.sheaf g
          (S.sheafHomExactSupport.obj F)) :=
  Eq.trans (NatTrans.congr_app (S.pushforwardSheafHomExactSupportMap_eq g) F)
    (Eq.trans
      (whiskerRight_whiskerLeft_app S.sheafHomExactSupport
        (internalHomPrecompNatTrans (Opens.grothendieckTopology S.Z.carrier) S.Z.sheaf g)
        (modulePushforward S.i) F)
      (congrArg (CategoryTheory.Functor.map (modulePushforward S.i))
        (internalHomPrecompNatTrans_app (Opens.grothendieckTopology S.Z.carrier) S.Z.sheaf g
          (S.sheafHomExactSupport.obj F))))

/-- **Stacks 0E2I, underived form, with its naturality in `N` as precomposition.**  The
isomorphism is `sheafHomPushforwardNatIso`, and its naturality in `N` is the conjugate
naturality `sheafHomPushforwardNatIso_natural` with the two induced maps identified as
precomposition on internal Hom sheaves. -/
noncomputable def pushforwardInternalHom : S.PushforwardInternalHom where
  iso N := S.sheafHomPushforwardNatIso N
  natural {N N'} g F := by
    have key : (S.sheafHomPushforwardNatIso N').hom.app F ≫
          (S.pushforwardSheafHomExactSupportMap g).app F =
        (S.sheafHomPushforwardMap g).app F ≫ (S.sheafHomPushforwardNatIso N).hom.app F :=
      NatTrans.congr_app (S.sheafHomPushforwardNatIso_natural g) F
    rw [S.pushforwardSheafHomExactSupportMap_app g F, S.sheafHomPushforwardMap_app g F] at key
    exact key.symm

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end

end
