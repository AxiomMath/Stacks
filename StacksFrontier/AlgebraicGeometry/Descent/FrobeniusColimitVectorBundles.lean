module

public import Mathlib.CategoryTheory.Category.Cat.AsSmall
public import Mathlib.CategoryTheory.Category.Cat.Colimit
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Frobenius
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Pullback
public import StacksCore.Tactic.StacksAttribute

/-!
# Vector bundles along the Frobenius colimit

Let `p` be a prime and let `X` be a scheme in characteristic `p`. Write `Vect(X)` for the
category of finite locally free `𝒪_X`-modules. The absolute Frobenius `F : X ⟶ X` acts on
`Vect(X)` by pullback, and the category appearing in Stacks Tag 0EXA is the colimit

`colim_F Vect(X) = colim (Vect(X) →F* Vect(X) →F* Vect(X) →F* ⋯)`

of the sequential diagram all of whose transition functors are `F^*`. This file constructs
that category, the category of finite locally free modules over the sheaf of rings
`colim_F 𝒪_X`, and the coprojections `𝒪_X ⟶ colim_F 𝒪_X` which relate the two.

## Main definitions

* `AlgebraicGeometry.Scheme.Vect`: the category `Vect(X)` of finite locally free
  `𝒪_X`-modules on a scheme `X`.
* `AlgebraicGeometry.frobeniusPullback`: pullback along the absolute Frobenius, as an
  endofunctor of `Vect(X)`.
* `AlgebraicGeometry.frobeniusVectDiagram`: the sequential diagram in `Cat` all of whose
  transition functors are `F^*`.
* `AlgebraicGeometry.frobeniusColimitVect`: the category `colim_F Vect(X)`.
* `AlgebraicGeometry.frobeniusColimitVectorBundles`: the category of finite locally free
  modules over the sheaf of rings `colim_F 𝒪_X`.
* `AlgebraicGeometry.frobeniusStructureSheafι`: the coprojection of `𝒪_X` into
  `colim_F 𝒪_X` at a stage of the diagram.
* `AlgebraicGeometry.frobeniusStageExtendScalars` and
  `AlgebraicGeometry.frobeniusStageFunctor`: extension of scalars along that coprojection,
  on all sheaves of modules and on the finite locally free ones.
* `AlgebraicGeometry.frobeniusExtendScalars`: extension of scalars along the Frobenius
  endomorphism of the structure sheaf.
* `AlgebraicGeometry.frobeniusColimitVectMap`: the endofunctor of `colim_F Vect(X)` induced by
  pullback along the absolute Frobenius.
* `AlgebraicGeometry.frobeniusPullbackIter`: the `k`-fold pullback along the absolute
  Frobenius, the transition functor from stage `n` to stage `n + k` of the diagram.
* `AlgebraicGeometry.frobeniusStageHomMap`: the comparison of Tag 0EXB on Hom-sets, at one
  stage of the colimit.

## Main results

* `AlgebraicGeometry.frobenius_comp_frobeniusStructureSheafι`: the coprojection at stage
  `n + 1` absorbs one Frobenius and becomes the coprojection at stage `n`. This is the
  compatibility which makes extension of scalars along the coprojections a cocone, up to
  isomorphism, on the diagram of vector bundle categories.
* `AlgebraicGeometry.isFiniteLocallyFree_frobeniusStageExtendScalars`: extension of scalars
  along a coprojection carries finite locally free `𝒪_X`-modules to finite locally free
  `colim_F 𝒪_X`-modules, so the stage functors land where Tag 0EXB says they do.
* `AlgebraicGeometry.toRingCatSheafHom_absoluteFrobenius` and
  `AlgebraicGeometry.pullback_absoluteFrobenius_eq`: **pullback along the absolute Frobenius
  is extension of scalars along the `p`-th power endomorphism of the structure sheaf.** The
  absolute Frobenius is the identity on the space, so its comorphism is a morphism of sheaves
  of rings on `X` itself, and on sections both maps are `g ↦ g ^ p`.
* `AlgebraicGeometry.frobeniusExtendScalarsStageIso` and
  `AlgebraicGeometry.frobeniusStageFunctorIso`: **the stage functors form a cocone, up to
  isomorphism, on the diagram whose colimit is `colim_F Vect(X)`** — first on all sheaves of
  modules, then on the finite locally free ones. Both stage functors are left adjoint to one
  and the same restriction of scalars, by the Frobenius compatibility of the coprojections,
  and uniqueness of left adjoints supplies the isomorphism.
* `AlgebraicGeometry.isIso_frobeniusColimitVectMap`: **Frobenius becomes invertible on
  `colim_F Vect(X)`**, which is the isomorphism `(ℰ, n) ≅ (F^*ℰ, n + 1)` of Tag 0EXA read on
  the colimit.
* `AlgebraicGeometry.frobeniusStageFunctorIterIso`: **the stage functors are compatible with
  arbitrarily many Frobenius pullbacks**, `F^{k,*} ⋙ (stage n + k) ≅ stage n`. This is
  `frobeniusStageFunctorIso` iterated, and it is what makes the comparison of Tag 0EXB
  independent of the stage at which an object of `colim_F Vect(X)` is presented.
* `AlgebraicGeometry.frobeniusStageHomMap_succ`: **the comparison on Hom-sets is compatible
  with the transition maps of the colimit.** Together with `frobeniusStageHomMap` this is the
  cocone, on the diagram `Hom_X(ℰ, 𝒢) → Hom_X(F^*ℰ, F^*𝒢) → ⋯` of Hom-sets, whose induced map
  out of `colim_k Hom_X(F^{k,*}ℰ, F^{k,*}𝒢)` the full faithfulness half of Tag 0EXB asserts to
  be bijective.
* `AlgebraicGeometry.frobeniusStageHomMap_id` and
  `AlgebraicGeometry.frobeniusStageHomMap_comp`: **the comparison on Hom-sets is functorial**,
  taking identities to identities and composites to composites.

## Implementation notes

`Vect(X)` is the full subcategory of `X.Modules` on the finite locally free modules; pullback
along the absolute Frobenius restricts to it by
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme`.

Extension of scalars along a morphism `α` of sheaves of rings on `X` is taken to be pullback
of sheaves of modules along the morphism of ringed spaces whose continuous map is the
identity of `X` and whose structure map is `α`; this is the form in which
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback` applies, and it agrees with
`Stacks.SheafOfModules.ChangeOfRings.extendScalars` by
`Stacks.SheafOfModules.ChangeOfRings.extendScalarsIsoPullback`, both being left adjoints of
restriction of scalars along `α`.

`AlgebraicGeometry.Scheme.ringSheafOnOpens` and
`AlgebraicGeometry.frobeniusColimitRingSheaf` only re-type the structure sheaf and the
Frobenius colimit of it. Instance resolution works at reducible transparency and so does not
unfold `TopCat.Sheaf`, which hides the site and its topology; without these re-typings the
category of modules over `colim_F 𝒪_X` has no `Category` instance that can be found, and the
pullback functor along a coprojection cannot be formed.

Colimits in `Cat` are available for small categories whose object and morphism universes
agree, so the diagram of vector bundle categories is pushed through
`CategoryTheory.Cat.asSmallFunctor` before the colimit is taken; this replaces each category
by an equivalent one and so does not change the colimit's equivalence type. The diagram
itself is `CategoryTheory.Limits.endoSequence` applied to the Frobenius pullback read as an
endomorphism of an object of `Cat`, the same construction which produces `colim_F 𝒪_X` from
the Frobenius endomorphism of the structure sheaf, so the two colimits of Tag 0EXB are formed
by one and the same device.

What Tag 0EXB asserts — that the comparison functor is an equivalence — is not proved here; it
is `AlgebraicGeometry.frobeniusColimitVectEquivalence` of
`StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectEssSurj`. What is here is all the data
a cocone needs except its strictness, and the Hom-level half of the comparison at a single
stage.

The comparison functor itself is built in
`StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitComparison`, as
`AlgebraicGeometry.frobeniusColimitVectComparison`. It cannot be obtained from
`AlgebraicGeometry.frobeniusColimitVect`: `Cat` is a 1-category, so a cocone in `Cat` on the
diagram of vector bundle categories asks for `F^* ⋙ (stage n + 1) = stage n` as an equality of
functors, whereas `AlgebraicGeometry.frobeniusStageFunctorIso` gives only a natural
isomorphism, which is all that is true — extension of scalars is a sheafified tensor product
and composes with itself only up to isomorphism. It is built instead out of
`AlgebraicGeometry.frobeniusColimitVectModel`, in
`StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitCategory`, which is `colim_F Vect(X)` in
the down-to-earth form of Tag 0EXA — objects the pairs `(ℰ, n)`, Hom-sets the colimits
`colim_N Hom_X(F^{N - n, *}ℰ, F^{N - m, *}𝒢)` — and out of which a functor asks only for the
data the stage functors have.

The three inputs to Tag 0EXB are supplied elsewhere:

1. **Full faithfulness** of the comparison functor, which is where the quasi-compactness and
   quasi-separatedness of `X` enter, is
   `AlgebraicGeometry.faithful_frobeniusColimitVectComparison` and
   `AlgebraicGeometry.full_frobeniusColimitVectComparison` of
   `StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectFullyFaithful`.
2. **Essential surjectivity** — the approximation argument putting the trivializing data of a
   finite locally free `colim_F 𝒪_X`-module, a finite cover of the quasi-compact `X` and the
   transition matrices over the quasi-compact intersections, at a finite stage of the colimit —
   is `AlgebraicGeometry.exists_frobeniusStageFunctor_obj_iso` of
   `StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectEssSurj`, which also concludes the
   tag as `AlgebraicGeometry.frobeniusColimitVectEquivalence`.
3. **The comparison with the strict colimit** — the equivalence of
   `AlgebraicGeometry.frobeniusColimitVectModel` with
   `AlgebraicGeometry.frobeniusColimitVect`, whose objects are the quotient of the pairs
   identifying `(ℰ, n)` with `(F^*ℰ, n + 1)` — is
   `AlgebraicGeometry.frobeniusColimitVectModelEquivalence` of
   `StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectExplicit`.

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Frobenius

universe u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {S : Sheaf J RingCat.{u}}

/-- The coprojection of a sheaf of rings into the colimit along one of its endomorphisms, at
stage `n` of the diagram of iterates. -/
noncomputable def ringSheafEndoColimitι (ψ : S ⟶ S) (n : ℕ) : S ⟶ ringSheafEndoColimit ψ :=
  endoColimitι ψ n

/-- The coprojection at stage `n + 1` absorbs one copy of the endomorphism and becomes the
coprojection at stage `n`. -/
lemma comp_ringSheafEndoColimitι_succ (ψ : S ⟶ S) (n : ℕ) :
    ψ ≫ ringSheafEndoColimitι ψ (n + 1) = ringSheafEndoColimitι ψ n :=
  comp_endoColimitι_succ ψ n

variable (S) in
/-- The category of finite locally free modules over a sheaf of rings. -/
abbrev FiniteLocallyFreeModules
    [∀ Y, HasWeakSheafify (J.over Y) AddCommGrpCat.{u}]
    [∀ Y, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}] : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (fun M : SheafOfModules.{u} S ↦
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M)

end CategoryTheory.Limits

namespace CategoryTheory

/-- The `k`-fold iterate `F^k = F ⋙ ⋯ ⋙ F` of an endofunctor, with `F^0` the identity. -/
def Functor.endoIter {A : Type*} [Category A] (F : A ⥤ A) : ℕ → (A ⥤ A)
  | 0 => 𝟭 A
  | k + 1 => F.endoIter k ⋙ F

/-- No iterate at all is the identity functor. -/
@[simp]
lemma Functor.endoIter_zero {A : Type*} [Category A] (F : A ⥤ A) : F.endoIter 0 = 𝟭 A := rfl

/-- One more iterate than `k` is `k` of them followed by one. -/
@[simp]
lemma Functor.endoIter_succ {A : Type*} [Category A] (F : A ⥤ A) (k : ℕ) :
    F.endoIter (k + 1) = F.endoIter k ⋙ F := rfl

/-- **Conjugating a morphism by a whiskered isomorphism.** Let `α : Q ⋙ W ≅ V` and
`β : P ⋙ V ≅ T` be natural isomorphisms. The isomorphism `(P ⋙ Q) ⋙ W ≅ T` assembled from
them carries `W.map (Q.map f)` to `V.map f`, conjugated by `β`, for every morphism
`f : P.obj E ⟶ P.obj G`. This is one step of the induction which compares the stage functors of
a sequential colimit along an endofunctor at two consecutive stages. -/
lemma inv_app_comp_map_comp_hom_app_whiskerLeft {A : Type*} [Category A] {B : Type*} [Category B]
    {P Q : A ⥤ A} {V W T : A ⥤ B} (α : Q ⋙ W ≅ V) (β : P ⋙ V ≅ T) {E G : A}
    (f : P.obj E ⟶ P.obj G) :
    (Functor.associator P Q W ≪≫ Functor.isoWhiskerLeft P α ≪≫ β).inv.app E ≫
        W.map (Q.map f) ≫
          (Functor.associator P Q W ≪≫ Functor.isoWhiskerLeft P α ≪≫ β).hom.app G =
      β.inv.app E ≫ V.map f ≫ β.hom.app G := by
  have hnat : W.map (Q.map f) ≫ α.hom.app (P.obj G) = α.hom.app (P.obj E) ≫ V.map f :=
    α.hom.naturality f
  simp only [Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Category.assoc, Category.comp_id, Category.id_comp]
  rw [reassoc_of% hnat, Iso.inv_hom_id_app_assoc]

/-- **Conjugating by a natural isomorphism preserves identities.** -/
lemma inv_app_comp_map_id_comp_hom_app {A : Type*} [Category A] {B : Type*} [Category B]
    {P : A ⥤ A} {V T : A ⥤ B} (β : P ⋙ V ≅ T) (E : A) :
    β.inv.app E ≫ V.map (𝟙 (P.obj E)) ≫ β.hom.app E = 𝟙 (T.obj E) := by
  simp

/-- **Conjugating by a natural isomorphism preserves composition.** -/
lemma inv_app_comp_map_comp_hom_app_comp {A : Type*} [Category A] {B : Type*} [Category B]
    {P : A ⥤ A} {V T : A ⥤ B} (β : P ⋙ V ≅ T) {E G H : A} (f : P.obj E ⟶ P.obj G)
    (g : P.obj G ⟶ P.obj H) :
    (β.inv.app E ≫ V.map f ≫ β.hom.app G) ≫ (β.inv.app G ≫ V.map g ≫ β.hom.app H) =
      β.inv.app E ≫ V.map (f ≫ g) ≫ β.hom.app H := by
  simp

end CategoryTheory

namespace AlgebraicGeometry

/-- `Vect(X)`, the category of finite locally free `𝒪_X`-modules on a scheme `X`. -/
abbrev Scheme.Vect (X : Scheme.{u}) : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (fun M : X.Modules ↦ SheafOfModules.IsFiniteLocallyFree.{u, u, u} M)

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-- Pullback along the absolute Frobenius of a scheme in characteristic `p`, as an endofunctor
of the category of finite locally free modules. -/
noncomputable def frobeniusPullback : X.Vect ⥤ X.Vect :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ Scheme.Modules.pullback (absoluteFrobenius X p hX))
    (fun M ↦ SheafOfModules.IsFiniteLocallyFree.pullback_scheme
      (absoluteFrobenius X p hX) M.1 M.2)

/-- The sequential diagram `Vect(X) →F* Vect(X) →F* ⋯` whose colimit is `colim_F Vect(X)`,
formed in the category of small categories. -/
noncomputable def frobeniusVectDiagram : ℕ ⥤ Cat.{u + 1, u + 1} :=
  endoSequence (Cat.asSmallFunctor.{u + 1, u, u + 1}.map (frobeniusPullback X p hX).toCatHom)

/-- The sequential diagram `Vect(X) →F* Vect(X) →F* ⋯` has a colimit in `Cat`. -/
instance : HasColimit (frobeniusVectDiagram X p hX) :=
  inferInstanceAs (HasColimit (endoSequence _))

/-- **The category `colim_F Vect(X)` of Stacks Tag 0EXA.** It is the colimit of the sequential
diagram of categories of finite locally free `𝒪_X`-modules whose transition functors are all
pullback along the absolute Frobenius. -/
@[stacks 0EXA]
noncomputable def frobeniusColimitVect : Cat.{u + 1, u + 1} :=
  colimit (frobeniusVectDiagram X p hX)

/-- The structure sheaf of `X`, read as a sheaf of rings on the site of opens of `X`. This is
`AlgebraicGeometry.Scheme.ringCatSheaf`; only its type is spelled differently, so that
instance resolution, which does not unfold `TopCat.Sheaf`, can see the site and its
topology. -/
noncomputable def Scheme.ringSheafOnOpens (X : Scheme.{u}) :
    Sheaf (Opens.grothendieckTopology (X : TopCat)) RingCat.{u} :=
  X.ringCatSheaf

/-- The sheaf of rings `colim_F 𝒪_X`, read as a sheaf of rings on the site of opens of `X`.
This is `AlgebraicGeometry.frobeniusColimitStructureSheaf`; only its type is spelled
differently, so that instance resolution, which does not unfold `TopCat.Sheaf`, can see the
site and its topology. -/
noncomputable def frobeniusColimitRingSheaf :
    Sheaf (Opens.grothendieckTopology (X : TopCat)) RingCat.{u} :=
  frobeniusColimitStructureSheaf X p hX

/-- The category of finite locally free modules over the sheaf of rings `colim_F 𝒪_X`. -/
abbrev frobeniusColimitVectorBundles : Type (u + 1) :=
  FiniteLocallyFreeModules (frobeniusColimitRingSheaf X p hX)

/-- The coprojection of the structure sheaf into `colim_F 𝒪_X` at stage `n` of the
diagram. -/
noncomputable def frobeniusStructureSheafι (n : ℕ) :
    X.ringCatSheaf ⟶ frobeniusColimitRingSheaf X p hX :=
  ringSheafEndoColimitι (frobeniusRingCatSheafHom X p hX) n

/-- The coprojection at stage `n + 1` absorbs one Frobenius and becomes the coprojection at
stage `n`. -/
lemma frobenius_comp_frobeniusStructureSheafι (n : ℕ) :
    frobeniusRingCatSheafHom X p hX ≫ frobeniusStructureSheafι X p hX (n + 1) =
      frobeniusStructureSheafι X p hX n :=
  comp_ringSheafEndoColimitι_succ (frobeniusRingCatSheafHom X p hX) n

/-- The stage-`n` coprojection `𝒪_X ⟶ colim_F 𝒪_X`, read as the structure map of a morphism
of ringed spaces whose underlying continuous map is the identity of `X`. -/
noncomputable def frobeniusStageStructureMap (n : ℕ) :
    X.ringSheafOnOpens ⟶
      ((Opens.map (𝟙 (X : TopCat))).sheafPushforwardContinuous RingCat.{u} _ _).obj
        (frobeniusColimitRingSheaf X p hX) :=
  frobeniusStructureSheafι X p hX n

/-- Extension of scalars along the stage-`n` coprojection, on all sheaves of modules.
Informally it is `ℳ ↦ ℳ ⊗_{𝒪_X} colim_F 𝒪_X`, the scalars being extended along the `n`-th
coprojection. -/
noncomputable def frobeniusStageExtendScalars (n : ℕ) :
    _root_.SheafOfModules.{u} X.ringSheafOnOpens ⥤
      _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX) :=
  _root_.SheafOfModules.pullback.{u} (frobeniusStageStructureMap X p hX n)

/-- **Extension of scalars along a coprojection preserves finite local freeness.** -/
theorem isFiniteLocallyFree_frobeniusStageExtendScalars (n : ℕ) (M : X.Modules)
    (h : SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((frobeniusStageExtendScalars X p hX n).obj M) :=
  SheafOfModules.IsFiniteLocallyFree.pullback (𝟙 (X : TopCat)) _ M h

/-- **Extension of scalars along the stage-`n` coprojection**, as a functor from `Vect(X)` to
the finite locally free modules over `colim_F 𝒪_X`. This is the functor out of the stage `n`
of the diagram whose colimit is `colim_F Vect(X)`; the comparison functor of Stacks Tag 0EXB
is assembled from these. -/
noncomputable def frobeniusStageFunctor (n : ℕ) :
    X.Vect ⥤ frobeniusColimitVectorBundles X p hX :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ frobeniusStageExtendScalars X p hX n)
    (fun M ↦ isFiniteLocallyFree_frobeniusStageExtendScalars X p hX n M.1 M.2)

/-- The Frobenius endomorphism of the structure sheaf, read as the structure map of a
morphism of ringed spaces whose underlying continuous map is the identity of `X`. -/
noncomputable def frobeniusSelfStructureMap :
    X.ringSheafOnOpens ⟶
      ((Opens.map (𝟙 (X : TopCat))).sheafPushforwardContinuous RingCat.{u} _ _).obj
        X.ringSheafOnOpens :=
  frobeniusRingCatSheafHom X p hX

/-- Extension of scalars along the Frobenius endomorphism of the structure sheaf. -/
@[sga "3 VIIA 4.3.3" "partial"]
noncomputable def frobeniusExtendScalars :
    _root_.SheafOfModules.{u} X.ringSheafOnOpens ⥤
      _root_.SheafOfModules.{u} X.ringSheafOnOpens :=
  _root_.SheafOfModules.pullback.{u} (frobeniusSelfStructureMap X p hX)

/-- **The comorphism of the absolute Frobenius is the `p`-th power endomorphism of the
structure sheaf.** Both are the identity on the underlying space, so they are morphisms of
sheaves of rings of the same shape, and on sections both are `g ↦ g ^ p`. -/
@[sga "4½ Rapport 1.1" "q = p"]
lemma toRingCatSheafHom_absoluteFrobenius :
    (absoluteFrobenius X p hX).toRingCatSheafHom = frobeniusSelfStructureMap X p hX := by
  apply Sheaf.hom_ext
  ext U g
  have h₁ : (RingCat.Hom.hom
      ((Scheme.Hom.toRingCatSheafHom (absoluteFrobenius X p hX)).hom.app U)) g = g ^ p :=
    absoluteFrobenius_app_apply X p hX U.unop g
  have h₂ : (RingCat.Hom.hom ((frobeniusSelfStructureMap X p hX).hom.app U)) g = g ^ p :=
    frobeniusPresheafHom_app_apply X p hX U.unop g
  exact h₁.trans h₂.symm

/-- **Pullback along the absolute Frobenius is extension of scalars along the `p`-th power
endomorphism of the structure sheaf.** -/
lemma pullback_absoluteFrobenius_eq :
    Scheme.Modules.pullback (absoluteFrobenius X p hX) = frobeniusExtendScalars X p hX :=
  congrArg (fun φ ↦ _root_.SheafOfModules.pullback.{u} φ)
    (toRingCatSheafHom_absoluteFrobenius X p hX)

/-- Restriction of scalars along the stage-`n + 1` coprojection followed by restriction of
scalars along Frobenius is restriction of scalars along the stage-`n` coprojection. -/
lemma pushforward_frobeniusStage_comp (n : ℕ) :
    _root_.SheafOfModules.pushforward.{u} (frobeniusStageStructureMap X p hX (n + 1)) ⋙
        _root_.SheafOfModules.pushforward.{u} (frobeniusSelfStructureMap X p hX) =
      _root_.SheafOfModules.pushforward.{u} (frobeniusStageStructureMap X p hX n) :=
  congrArg _root_.SheafOfModules.restrictScalars.{u}
    (frobenius_comp_frobeniusStructureSheafι X p hX n)

/-- **The cocone compatibility of the stage functors, on all sheaves of modules.** Extending
scalars along Frobenius and then along the stage-`n + 1` coprojection is extending scalars
along the stage-`n` coprojection: both are left adjoint to one and the same restriction of
scalars. -/
noncomputable def frobeniusExtendScalarsStageIso (n : ℕ) :
    frobeniusExtendScalars X p hX ⋙ frobeniusStageExtendScalars X p hX (n + 1) ≅
      frobeniusStageExtendScalars X p hX n :=
  Adjunction.leftAdjointUniq
    ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
      (frobeniusSelfStructureMap X p hX)).comp
        (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
          (frobeniusStageStructureMap X p hX (n + 1))))
    ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
      (frobeniusStageStructureMap X p hX n)).ofNatIsoRight
        (eqToIso (pushforward_frobeniusStage_comp X p hX n).symm))

/-- **The cocone compatibility of the stage functors**, in the form the diagram of Tag 0EXA
asks for: pulling back along the absolute Frobenius and then extending scalars along the
stage-`n + 1` coprojection is extending scalars along the stage-`n` coprojection. -/
noncomputable def frobeniusPullbackStageIso (n : ℕ) :
    Scheme.Modules.pullback (absoluteFrobenius X p hX) ⋙
        frobeniusStageExtendScalars X p hX (n + 1) ≅
      frobeniusStageExtendScalars X p hX n :=
  eqToIso (congrArg (fun G ↦ G ⋙ frobeniusStageExtendScalars X p hX (n + 1))
    (pullback_absoluteFrobenius_eq X p hX)) ≪≫ frobeniusExtendScalarsStageIso X p hX n

/-- **The stage functors form a cocone, up to isomorphism, on the diagram of Tag 0EXA.**
Pulling a finite locally free `𝒪_X`-module back along the absolute Frobenius and then
extending scalars along the stage-`n + 1` coprojection gives the same finite locally free
`colim_F 𝒪_X`-module as extending scalars along the stage-`n` coprojection. This is the datum
from which the comparison functor `colim_F Vect(X) ⟶ Vect(colim_F 𝒪_X)` of Tag 0EXB is to be
assembled. -/
noncomputable def frobeniusStageFunctorIso (n : ℕ) :
    frobeniusPullback X p hX ⋙ frobeniusStageFunctor X p hX (n + 1) ≅
      frobeniusStageFunctor X p hX n :=
  NatIso.ofComponents
    (fun E ↦ ObjectProperty.isoMk _ ((frobeniusPullbackStageIso X p hX n).app E.1))
    (fun f ↦ (ObjectProperty.ι _).map_injective
      ((frobeniusPullbackStageIso X p hX n).hom.naturality f.hom))

/-! ### Frobenius on the colimit category -/

/-- The endofunctor of `colim_F Vect(X)` induced by pullback along the absolute Frobenius at
every stage of the diagram. -/
noncomputable def frobeniusColimitVectMap :
    frobeniusColimitVect X p hX ⟶ frobeniusColimitVect X p hX :=
  endoColimitMap (Cat.asSmallFunctor.{u + 1, u, u + 1}.map (frobeniusPullback X p hX).toCatHom)

/-- **Frobenius pullback becomes invertible on `colim_F Vect(X)`.** This is the statement that
the object `(ℰ, n)` of Tag 0EXA is isomorphic to the object `(F^*ℰ, n + 1)`, read as the
invertibility of the endofunctor the Frobenius induces on the colimit. -/
theorem isIso_frobeniusColimitVectMap : IsIso (frobeniusColimitVectMap X p hX) :=
  isIso_endoColimitMap _

/-! ### Iterated Frobenius pullback and the stage functors -/

/-- The `k`-fold pullback along the absolute Frobenius, `F^{k,*}`, as an endofunctor of
`Vect(X)`. This is the transition functor from stage `n` to stage `n + k` of the diagram whose
colimit is `colim_F Vect(X)`. -/
noncomputable def frobeniusPullbackIter : ℕ → (X.Vect ⥤ X.Vect) :=
  (frobeniusPullback X p hX).endoIter

/-- No Frobenius pullback at all is the identity functor. -/
@[simp]
lemma frobeniusPullbackIter_zero : frobeniusPullbackIter X p hX 0 = 𝟭 _ := rfl

/-- One more Frobenius pullback than `k` of them is `k` of them followed by one. -/
@[simp]
lemma frobeniusPullbackIter_succ (k : ℕ) :
    frobeniusPullbackIter X p hX (k + 1) =
      frobeniusPullbackIter X p hX k ⋙ frobeniusPullback X p hX :=
  rfl

/-- **The stage functors are compatible with arbitrarily many Frobenius pullbacks.** Extending
scalars along the stage-`n + k` coprojection after pulling back `k` times along the absolute
Frobenius is extending scalars along the stage-`n` coprojection. For `k = 1` this is
`AlgebraicGeometry.frobeniusStageFunctorIso`; the general case is that isomorphism iterated, and
it is what makes the comparison of Tag 0EXB independent of the stage at which an object of
`colim_F Vect(X)` is presented. -/
noncomputable def frobeniusStageFunctorIterIso (n : ℕ) : ∀ k : ℕ,
    frobeniusPullbackIter X p hX k ⋙ frobeniusStageFunctor X p hX (n + k) ≅
      frobeniusStageFunctor X p hX n
  | 0 => Iso.refl _
  | k + 1 =>
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (frobeniusPullbackIter X p hX k)
            (frobeniusStageFunctorIso X p hX (n + k)) ≪≫
          frobeniusStageFunctorIterIso n k

/-- The compatibility isomorphism for `k + 1` Frobenius pullbacks is the one for `k` of them
preceded by the one-step compatibility, whiskered by the `k`-fold pullback. -/
lemma frobeniusStageFunctorIterIso_succ (n k : ℕ) :
    frobeniusStageFunctorIterIso X p hX n (k + 1) =
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (frobeniusPullbackIter X p hX k)
            (frobeniusStageFunctorIso X p hX (n + k)) ≪≫
          frobeniusStageFunctorIterIso X p hX n k :=
  rfl

/-- **The comparison on Hom-sets, at one stage of the colimit.** A morphism
`F^{k,*}ℰ ⟶ F^{k,*}𝒢` of finite locally free `𝒪_X`-modules — that is, an element of the
Hom-set of `colim_F Vect(X)` from `(ℰ, n)` to `(𝒢, n)` presented at level `n + k` — gives a
morphism of finite locally free `colim_F 𝒪_X`-modules between the images of `ℰ` and `𝒢` under
the stage-`n` functor. It is the stage-`n + k` functor applied to the morphism, conjugated by
`AlgebraicGeometry.frobeniusStageFunctorIterIso`. -/
noncomputable def frobeniusStageHomMap (n k : ℕ) {E G : X.Vect}
    (f : (frobeniusPullbackIter X p hX k).obj E ⟶ (frobeniusPullbackIter X p hX k).obj G) :
    (frobeniusStageFunctor X p hX n).obj E ⟶ (frobeniusStageFunctor X p hX n).obj G :=
  (frobeniusStageFunctorIterIso X p hX n k).inv.app E ≫
    (frobeniusStageFunctor X p hX (n + k)).map f ≫
      (frobeniusStageFunctorIterIso X p hX n k).hom.app G

/-- **The comparison on Hom-sets is compatible with the transition maps of the colimit.** A
morphism presented at level `n + k` and the same morphism presented at level `n + k + 1`, that
is pulled back once more along the absolute Frobenius, have the same image. This is the
well-definedness of the action of the comparison of Tag 0EXB on
`Hom_{colim_F Vect(X)}((ℰ, n), (𝒢, n)) = colim_k Hom_X(F^{k,*}ℰ, F^{k,*}𝒢)`. -/
lemma frobeniusStageHomMap_succ (n k : ℕ) {E G : X.Vect}
    (f : (frobeniusPullbackIter X p hX k).obj E ⟶ (frobeniusPullbackIter X p hX k).obj G) :
    frobeniusStageHomMap X p hX n (k + 1) ((frobeniusPullback X p hX).map f) =
      frobeniusStageHomMap X p hX n k f := by
  simp only [frobeniusStageHomMap, frobeniusStageFunctorIterIso_succ]
  exact inv_app_comp_map_comp_hom_app_whiskerLeft (frobeniusStageFunctorIso X p hX (n + k))
    (frobeniusStageFunctorIterIso X p hX n k) f

/-- **The comparison on Hom-sets takes an identity to an identity.** -/
@[simp]
lemma frobeniusStageHomMap_id (n k : ℕ) (E : X.Vect) :
    frobeniusStageHomMap X p hX n k (𝟙 ((frobeniusPullbackIter X p hX k).obj E)) =
      𝟙 ((frobeniusStageFunctor X p hX n).obj E) :=
  inv_app_comp_map_id_comp_hom_app (frobeniusStageFunctorIterIso X p hX n k) E

/-- **The comparison on Hom-sets is compatible with composition.** With
`AlgebraicGeometry.frobeniusStageHomMap_id` and
`AlgebraicGeometry.frobeniusStageHomMap_succ`, this is the whole of the functoriality of the
comparison of Tag 0EXB on morphisms presented at a fixed level. -/
lemma frobeniusStageHomMap_comp (n k : ℕ) {E G H : X.Vect}
    (f : (frobeniusPullbackIter X p hX k).obj E ⟶ (frobeniusPullbackIter X p hX k).obj G)
    (g : (frobeniusPullbackIter X p hX k).obj G ⟶ (frobeniusPullbackIter X p hX k).obj H) :
    frobeniusStageHomMap X p hX n k f ≫ frobeniusStageHomMap X p hX n k g =
      frobeniusStageHomMap X p hX n k (f ≫ g) :=
  inv_app_comp_map_comp_hom_app_comp (frobeniusStageFunctorIterIso X p hX n k) f g

end AlgebraicGeometry

end
