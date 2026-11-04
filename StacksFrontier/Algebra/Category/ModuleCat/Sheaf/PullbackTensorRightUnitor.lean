module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorChainSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorUnitSections
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCompMonoidal

/-! # The right-unitor coherence of Stacks 03EL for a morphism of ringed topoi

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi — four fields, a morphism
of topoi together with the two forms of the structure map, as in
`Stacks.Sheaves.RingedToposModules.RingedToposHom`, with no presentation of the morphism of topoi
by a functor of the underlying sites. The comparison of **Stacks 03EL**

`f^*(F ⊗_{O_D} G) ≅ f^*F ⊗_{O_C} f^*G`

is `Stacks.SheafOfModules.pullbackTensorIso`, and the only things known about it are that the
six-step chain of bijections `Stacks.SheafOfModules.pullbackTensorHomEquiv` carries it to the
identity and that it is natural. This file proves the **right-unitor coherence**: at `G = O_D`,
the comparison followed by `𝟙 ⊗ ν` for the unit comparison `ν : f^*O_D ⟶ O_C` and by the right
unitor of `f^*A` is the pullback of the right unitor of `A`.

That coherence is the one missing module-level input of the right-unitor coherence of Stacks 07A4,
hence of the base case of Stacks 0944 at `K = O_D[n]`. What is proved here is the mathematics of
it; transporting it to the *site-presented* pullback of
`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos` — along the identification
`Stacks.Sheaves.DerivedPullback.pullbackModulesSiteIso` of the two pullbacks, and from the unit
comparison used here to Mathlib's `SheafOfModules.pullbackObjUnitToUnit` — is bookkeeping this file
does not do; see
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposUnitorCoherence`, whose
`PullbackToposRightUnitorCoherence` is that transported statement.

## Main results

* `Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp_rightUnitor`: **the right-unitor
  coherence of Stacks 03EL for an arbitrary morphism of ringed topoi.** The unit comparison `ν` is
  an argument, pinned down by the hypothesis that its composite with the unit of extension of
  scalars of Stacks 03CZ is the inverse-image form `f⁻¹O_D ⟶ O_C` of the structure map, on local
  sections; that is exactly the adjoint characterisation of `ν`, in the form in which the
  computation uses it and a consumer with a concrete `ν` can check it.

## Implementation notes

**How the coherence is proved.** Both sides are morphisms out of `f^*(A ⊗_{O_D} O_D)` and the
left-hand side begins with the comparison of Stacks 03EL, so the chain of bijections — which is
injective — turns the identity into one about the preimage of `𝟙 ⊗ ν` followed by the right
unitor. Step 1 of the chain is the adjunction of Stacks 03D7, and peeling it off moves the
identity to the *target* topos, where the source `A ⊗_{O_D} O_D` is a tensor product sheaf of two
sheaves on `D` and therefore has local sections: `Stacks.SheafOfModules.tensorSheaf_hom_ext` then
reduces everything to the unit image of a pure tensor `a ⊗ₜ r`. There the right-hand side is
`η_A(r · a)` for the unit `η` of Stacks 03D7, and the left-hand side is read off the chain by
`Stacks.SheafOfModules.pullbackTensorStep2_symm_step3_symm_val_app_unit_tmul` and
`Stacks.SheafOfModules.pairingApp_pullbackTensorBottom`: the bottom of the chain pairs two local
sections of the inverse images by the pure tensor of their images under the unit of extension of
scalars, `ν` turns the second factor into `f♯`, the right unitor turns the pure tensor into
`f♯(r) · η(a)`, and that is `η(r · a)` because the unit of extension of scalars is a map of
`f⁻¹O_D`-modules. The two sides then agree by the naturality of the unit of `f⁻¹ ⊣ f_*`.

The direct image is never described on sections, and it has no description for an abstract
`CategoryTheory.Sheaf.MorphismOfTopoi`: every statement below keeps the sections of `f_*N` opaque
and rewrites only the *morphism* inside, which is why the computation goes through without a site
presentation.

**Seams, and the two cures used.** Four pairs of definitionally equal but not syntactically equal
spellings are crossed: `(f.pullbackModules).obj F` against extension of scalars applied to the
inverse image;
`((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor (J := X.J) _))).obj (F, G)`
against `Stacks.SheafOfModules.TensorSheafification.tensorSheaf`; the underlying sheaf of sets of
`O` read as a module over itself against `AlgebraicGeometry.Sheaf.ringSheaf`; and the sections of a
restriction of scalars against the sections of the sheaf restricted. Across such a seam a term is
not type-correct at `implicit` transparency, so `rw` reports patterns it cannot find and `unfold`
produces goals no later tactic can touch.

Both cures this development prescribes are used. *Declare the crossing once, at one spelling*:
`swapHom` is the swap of a binary product over abstract objects, so that the composite of a swap
with a scalar action has its endpoints fixed by a declared type; `invSmulRightHom` and
`rightUnitorFactor` are a pairing and a composite declared once at the spelling their consumer
needs; and `extendUnitSection` is that move applied to an *element* — the image of a local section
under the unit of extension of scalars, declared as a section of `O_C ⊗_{f⁻¹O_D} M` rather than of
its restriction of scalars, because the scalar action instance search finds on the two differs.
*State the bookkeeping over abstract morphisms and apply it by `exact`*: `comp_id_comp`,
`assoc_symm` and `prodComparison_swapHom` are reassociations whose unification therefore runs at
default transparency and never under a rewrite's motive. Every proof below that crosses a seam is
a term built from `Eq.trans` and `congrArg` for the same reason.

**No enlarged heartbeat budget.** Naming the endpoint objects is what keeps the value formulas
inside the default budget: `pullbackObj` and `rightUnitorFactor` exist because writing their
expansions inline exhausts it at `whnf` before the statement has elaborated.

**No `@[stacks 03EL]` attribute.** Stacks 03EL asserts the comparison and its functoriality in the
two modules, and nothing else; the unitor compatibility is not part of it. The tag is carried by
`Stacks.SheafOfModules.pullbackTensorIso`.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.PresheafOfModules.ChangeOfRings
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open scoped TensorProduct

universe w v u w' v' u' t

namespace Stacks.SheafOfModules

/-! ## Bookkeeping over abstract objects

Each statement of this section is about abstract objects and morphisms, so that it can be applied
by `exact` and its unification runs at default transparency, never under the motive of a rewrite.
At the objects of this file the seams carry two spellings of the structure sheaf of the source, of
the tensor product of the two pullbacks and of the underlying sheaf of sets of the structure
sheaf, and `rw [Category.assoc]` and `rw [Category.comp_id]` report patterns they cannot find. -/

section Bookkeeping

variable {D : Type*} [Category D]

/-- Appending a morphism to one followed by an identity. -/
private lemma comp_id_comp {A B E : D} (a : A ⟶ B) (k : B ⟶ E) :
    a ≫ k = (a ≫ 𝟙 B) ≫ k := by
  rw [Category.comp_id]

/-- Reassociating a triple composite. -/
private lemma assoc_symm {A B E F : D} (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ F) :
    a ≫ b ≫ c = (a ≫ b) ≫ c :=
  (Category.assoc a b c).symm

variable [HasBinaryProducts D]

/-- The swap of the two factors of a binary product, declared once over abstract objects. The
scalar action of a sheaf of rings on a sheaf of modules is a morphism out of `O ⨯ M`, while the
right unitor pairs a section of `M` with a section of `O`; naming the swap is what keeps the
composite of the two type-correct below default transparency, since its two endpoints are then
fixed by a declared type. -/
private def swapHom (P Q : D) : P ⨯ Q ⟶ Q ⨯ P := prod.lift prod.snd prod.fst

/-- The first component of the swap. -/
private lemma swapHom_comp_fst (P Q : D) : swapHom P Q ≫ prod.fst = prod.snd :=
  prod.lift_fst _ _

/-- The second component of the swap. -/
private lemma swapHom_comp_snd (P Q : D) : swapHom P Q ≫ prod.snd = prod.fst :=
  prod.lift_snd _ _

/-- The swap on a pair of elements. -/
private lemma map_swapHom [HasFiniteProducts D] {F : D ⥤ Type t} [PreservesFiniteProducts F]
    (P Q : D) (a : F.obj P) (b : F.obj Q) :
    F.map (swapHom P Q) (Functor.prodObjMk (P := F) a b) =
      Functor.prodObjMk (P := F) b a := by
  rw [swapHom, Functor.map_lift_apply, Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk]

/-- **The product comparison of a functor commutes with the swap of the two factors.** Both sides
are determined by their two components, and each component is the functor applied to a
projection. -/
private lemma prodComparison_swapHom {E : Type*} [Category E] [HasBinaryProducts E] (Φ : D ⥤ E)
    (P Q : D) :
    prodComparison Φ P Q ≫ swapHom (Φ.obj P) (Φ.obj Q) =
      Φ.map (swapHom P Q) ≫ prodComparison Φ Q P := by
  refine prod.hom_ext ?_ ?_
  · rw [Category.assoc, swapHom_comp_fst, prodComparison_snd, Category.assoc,
      prodComparison_fst, ← Φ.map_comp, swapHom_comp_fst]
  · rw [Category.assoc, swapHom_comp_snd, prodComparison_fst, Category.assoc,
      prodComparison_snd, ← Φ.map_comp, swapHom_comp_snd]

end Bookkeeping

/-! ## The right scalar action of the structure sheaf -/

section Generic

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (R : Sheaf J RingCat.{w})

/-- **The right scalar action of the structure sheaf on a sheaf of modules**, as a pairing
`M ⨯ O ⟶ M` of the underlying sheaves of sets: swap the two factors and multiply. Its source is
declared with the second factor spelled as the underlying sheaf of sets of `O` *read as a module
over itself*, which is the spelling in which the right unitor of Tag 01CA presents it. -/
private def smulRightUnitHom (M : SheafOfModules.{w} R) :
    Sheaf.moduleSheaf R M ⨯ Sheaf.moduleSheaf R (SheafOfModules.unit R) ⟶
      Sheaf.moduleSheaf R M :=
  swapHom (Sheaf.moduleSheaf R M) (Sheaf.ringSheaf R) ≫ Sheaf.moduleSMulHom R M

/-- The right scalar action on a pair of local sections. -/
private lemma sectionsFunctor_map_smulRightUnitHom (M : SheafOfModules.{w} R) (U : Cᵒᵖ)
    (a : (Sheaf.sectionsFunctor J U).obj (Sheaf.moduleSheaf R M))
    (r : (Sheaf.sectionsFunctor J U).obj (Sheaf.ringSheaf R)) :
    (Sheaf.sectionsFunctor J U).map (smulRightUnitHom R M)
        (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w} J U)
          (A := Sheaf.moduleSheaf R M) (B := Sheaf.ringSheaf R) a r) = r • a := by
  refine Eq.trans ((Sheaf.sectionsFunctor J U).map_comp_apply
    (swapHom (Sheaf.moduleSheaf R M) (Sheaf.ringSheaf R)) (Sheaf.moduleSMulHom R M) _) ?_
  refine Eq.trans (congrArg ((Sheaf.sectionsFunctor J U).map (Sheaf.moduleSMulHom R M))
    (map_swapHom (F := Sheaf.sectionsFunctor.{w} J U) (Sheaf.moduleSheaf R M)
      (Sheaf.ringSheaf R) a r)) ?_
  exact Sheaf.sectionsFunctor_map_moduleSMulHom R M U r a

/-- Scalar multiplication on local sections is the transported scalar multiplication of
`Stacks.Sheaves.ToposPullback`. True by construction of the module structure; stated so that a
goal written with `•` can be brought to the shape the transport lemmas are stated in. -/
private lemma smul_eq_moduleSMulObj (M : SheafOfModules.{w} R) (U : Cᵒᵖ)
    (r : (Sheaf.sectionsFunctor J U).obj (Sheaf.ringSheaf R))
    (y : (Sheaf.sectionsFunctor J U).obj (Sheaf.moduleSheaf R M)) :
    r • y = Sheaf.moduleSMulObj R M (Sheaf.sectionsFunctor J U) r y :=
  (Sheaf.sectionsFunctor_map_moduleSMulHom R M U r y).symm

end Generic

/-! ## The coherence -/

section RightUnitor

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (A : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- The pullback of a sheaf of `O_D`-modules, spelled as extension of scalars along the
inverse-image form of the structure map, applied to the inverse image. This is
`Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules` on objects, at the spelling in
which the value formulas of the chain of Tag 03EL are stated; naming it is what keeps the
statements below inside the elaborator's budget. -/
private abbrev pullbackObj (F : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (extendScalarsFSharp f).obj
    ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)

/-! ### The bottom two steps of the chain at an arbitrary value -/

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- Step 6 of the chain of Tag 03EL at an arbitrary value is step 6 at the identity followed by
that value. -/
private lemma step6_symm_eq
    (F G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (k : pullbackTensorTarget f F G ⟶ N) :
    (pullbackTensorStep6 f F G N).symm k =
      (pullbackTensorStep6 f F G (pullbackTensorTarget f F G)).symm
        (𝟙 (pullbackTensorTarget f F G)) ≫ k := by
  show _ ≫ k = (_ ≫ 𝟙 _) ≫ k
  exact comp_id_comp _ k

/-- Steps 5 and 6 of the chain of Tag 03EL at an arbitrary value are
`Stacks.SheafOfModules.pullbackTensorBottomHom` followed by that value. -/
private alias step5_symm_step6_symm_eq :=
  Stacks.SheafOfModules.pullbackTensorStep5_symm_step6_symm

/-! ### Scalars across the inverse-image form of the structure map -/

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- Scalars for a sheaf of modules obtained by restriction of scalars along the inverse-image form
of the structure map, on local sections. -/
private lemma smul_restrictScalars_sections
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (V : X.Cᵒᵖ)
    (σ : (Sheaf.sectionsFunctor X.J V).obj (Sheaf.ringSheaf
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
    (y : (Sheaf.sectionsFunctor X.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)) :
    Sheaf.moduleSMulObj
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj M)
        (Sheaf.sectionsFunctor X.J V) σ y =
      ((Sheaf.sectionsFunctor X.J V).map
          ((sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImage) σ) • y :=
  (moduleSMulObj_restrictScalars f.fSharpInverseImage M (Sheaf.sectionsFunctor X.J V) σ y).trans
    (Sheaf.sectionsFunctor_map_moduleSMulHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M V _ y)

/-! ### The element-level seam at the unit of extension of scalars -/

/-- **The unit of extension of scalars on a local section, declared at the target spelling.**
The image of a local section `x` of a sheaf of `f⁻¹O_D`-modules `M` under the unit of the
adjunction of Stacks 03CZ, read as a section of `O_C ⊗_{f⁻¹O_D} M` rather than as a section of the
restriction of scalars of that sheaf.

The two are the same element and the two types are definitionally equal, but they are not
syntactically equal, and the scalar actions instance search finds on them are the one of `O_C` and
the one of `f⁻¹O_D` respectively. Declaring the element once at the target spelling absorbs that
definitional equality into a declared type — the move this development prescribes for the seams of
a composite, applied to an element rather than to a morphism — and it is what lets the two sides
of the pairing identity below be written down at all. -/
private def extendUnitSection
    (M : SheafOfModules.{w}
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (V : X.Cᵒᵖ) (x : M.val.obj V) : ((extendScalarsFSharp f).obj M).val.obj V :=
  ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app M).val.app V x

/-! ### The right scalar action upstairs is the inverse image of the one downstairs -/

/-- **The right scalar action of `f⁻¹O_D` on `f⁻¹A`**, as a pairing of the underlying sheaves of
sets, declared with its second factor spelled as the inverse image of the structure sheaf of the
target: that is the spelling the chain of Tag 03EL produces, and it is not the spelling
`smulRightUnitHom` would give. -/
private def invSmulRightHom :
    Sheaf.moduleSheaf
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A) ⨯
        Sheaf.moduleSheaf
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ⟶
      Sheaf.moduleSheaf
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A) :=
  swapHom
      (Sheaf.moduleSheaf
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A))
      (Sheaf.ringSheaf
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ≫
    Sheaf.moduleSMulHom
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A)

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- The right scalar action upstairs on a pair of local sections. -/
private lemma sectionsFunctor_map_invSmulRightHom (V : X.Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor X.J V).obj (Sheaf.moduleSheaf
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A)))
    (s : (Sheaf.sectionsFunctor X.J V).obj (Sheaf.ringSheaf
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))) :
    (Sheaf.sectionsFunctor X.J V).map (invSmulRightHom f A)
        (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w} X.J V)
          (A := Sheaf.moduleSheaf
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A))
          (B := Sheaf.ringSheaf
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
          x s) = s • x := by
  exact sectionsFunctor_map_smulRightUnitHom
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A) V x s

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- **The right scalar action of `f⁻¹O_D` on `f⁻¹A` is the inverse image of the right scalar
action of `O_D` on `A`**, once the product comparison of the inverse image is inserted. This is
the left exactness of the inverse image transporting the scalar action of Stacks 03D2, composed
with the commutation of the product comparison with the swap of the two factors. -/
private lemma prodComparison_comp_invSmulRightHom :
    prodComparison f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A)
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ≫
        invSmulRightHom f A =
      f.toToposHom.inverseImage.map
        (smulRightUnitHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A) := by
  refine Eq.trans (assoc_symm
    (prodComparison f.toToposHom.inverseImage
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A)
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
    (swapHom
      (Sheaf.moduleSheaf
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A))
      (Sheaf.ringSheaf
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
    (Sheaf.moduleSMulHom
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A))) ?_
  refine Eq.trans (congrArg (fun z ↦ z ≫
      Sheaf.moduleSMulHom
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A))
    (prodComparison_swapHom f.toToposHom.inverseImage
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A)
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg
    (fun z ↦ f.toToposHom.inverseImage.map
      (swapHom (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))) ≫ z)
    (moduleSMul_map_aux' X.J f.toToposHom.inverseImage
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A).symm) ?_
  exact (f.toToposHom.inverseImage.map_comp _ _).symm

/-! ### The second factor of the coherence -/

/-- **The second factor of the left-hand side of the coherence**, declared once with its source at
the spelling of the tensor bifunctor of Tag 0GMW: the tensor of the identity of `f^*A` with the
unit comparison `ν`, followed by the right unitor of `f^*A`. -/
private def rightUnitorFactor
    (ν : pullbackObj f (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        (pullbackObj f A,
          pullbackObj f (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ⟶
      pullbackObj f A :=
  ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).map
      ((𝟙 (pullbackObj f A), ν) :
        (pullbackObj f A,
          pullbackObj f (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ⟶
        (pullbackObj f A, SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ≫
    (tensorSheafUnitRightIso X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
      (pullbackObj f A)).hom

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- **The second factor of the coherence on a pure tensor**: tensoring the identity with the unit
comparison and then applying the right unitor carries the sheafification-unit image of `u ⊗ₜ t` to
`ν(t) · u`. -/
private lemma rightUnitorFactor_val_app_unit_tmul
    (ν : pullbackObj f (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (V : X.Cᵒᵖ) (u : (pullbackObj f A).val.obj V)
    (t : (pullbackObj f
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).val.obj V)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V) (hr : ν.val.app V t = r) :
    (rightUnitorFactor f A ν).val.app V
        (((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf X.J X.O.obj
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) (𝟙 _)).unit.app
            ((pullbackObj f A).val ⊗
              (pullbackObj f
                (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).val)).app V
          (u ⊗ₜ[(ringPresheaf X.O.obj).obj V] t)) =
      r • u := by
  subst hr
  unfold rightUnitorFactor
  rw [Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map]
  refine Eq.trans (CategoryTheory.comp_apply _ _ _) ?_
  refine Eq.trans (congrArg ((tensorSheafUnitRightIso X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
      (pullbackObj f A)).hom.val.app V)
    (TensorSheafification.sheafification_map_val_app_unit X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
      (PresheafOfModules.tensorHom (O := X.O.obj)
        (SheafOfModules.Hom.val (𝟙 (pullbackObj f A))) ν.val) V
      (u ⊗ₜ[(ringPresheaf X.O.obj).obj V] t))) ?_
  exact tensorSheafUnitRightIso_hom_toSheafify_tmul X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
    (pullbackObj f A) V u (ν.val.app V t)

/-! ### The pairing identity upstairs -/

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- **The bottom of the chain of Tag 03EL, followed by `𝟙 ⊗ ν` and the right unitor, is the right
scalar action followed by the unit of extension of scalars.**

This is the whole mathematical content of the right-unitor coherence of Stacks 03EL, read on local
sections of the inverse images: the bottom of the chain pairs `x` and `s` by the pure tensor
`η(x) ⊗ₜ η(s)`, the unit comparison turns `η(s)` into `f♯(s)` and the right unitor turns the pure
tensor into `f♯(s) · η(x)`, which is `η(s · x)` because `η` is a map of `f⁻¹O_D`-modules. -/
private lemma bottomPairing_comp_rightUnitorFactor
    (ν : pullbackObj f (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hν : ∀ (V : X.Cᵒᵖ)
        (s : ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).val.obj V),
        ν.val.app V
            (extendUnitSection f
              ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
                (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) V s) =
          f.fSharpInverseImage.hom.app V s) :
    ((pullbackTensorStep4 f A (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            (pullbackTensorTarget f A
              (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).symm
          (pullbackTensorBottomHom f A
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).1 ≫
        (Sheaf.moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
          ((SheafOfModules.restrictScalars f.fSharpInverseImage).map
            (rightUnitorFactor f A ν)) =
      invSmulRightHom f A ≫
        (Sheaf.moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
          ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
            (inverseImageRingSheaf f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A)) := by
  refine pairing_ext
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    fun V x s ↦ ?_
  have hL : pairingApp
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (((pullbackTensorStep4 f A
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
                (pullbackTensorTarget f A
                  (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).symm
              (pullbackTensorBottomHom f A
                (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).1 ≫
            (Sheaf.moduleSheafFunctor
                (inverseImageRingSheaf f.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
              ((SheafOfModules.restrictScalars f.fSharpInverseImage).map
                (rightUnitorFactor f A ν))) V x s =
      f.fSharpInverseImage.hom.app V s •
        extendUnitSection f
          ((inverseImageModules f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A) V x := by
    rw [pairingApp_comp, pairingApp_pullbackTensorBottom f A
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) V x s]
    exact rightUnitorFactor_val_app_unit_tmul f A ν V
      (extendUnitSection f
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A) V x)
      (extendUnitSection f
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) V s)
      _ (hν V s)
  have hR : pairingApp
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (invSmulRightHom f A ≫
            (Sheaf.moduleSheafFunctor
                (inverseImageRingSheaf f.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
              ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
                (inverseImageRingSheaf f.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
                ((inverseImageModules f.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A))) V x s =
      f.fSharpInverseImage.hom.app V s •
        extendUnitSection f
          ((inverseImageModules f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A) V x := by
    refine Eq.trans (pairingApp_comp (invSmulRightHom f A)
      ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
        ((inverseImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A)) V x s) ?_
    refine Eq.trans (congrArg ((Sheaf.sectionsFunctor X.J V).map
        ((Sheaf.moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
          ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
            (inverseImageRingSheaf f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A))))
      (sectionsFunctor_map_invSmulRightHom f A V x s)) ?_
    refine Eq.trans (Sheaf.sectionsFunctor_map_moduleSheafFunctor_map_smul
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
        ((inverseImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A)) V s x) ?_
    refine Eq.trans (smul_eq_moduleSMulObj
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj (pullbackObj f A)) V s
      (extendUnitSection f
        ((inverseImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A) V x)) ?_
    exact smul_restrictScalars_sections f (pullbackObj f A) V s
      (extendUnitSection f
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A) V x)
  exact hL.trans hR.symm

/-! ### The unit of Stacks 03D7 on underlying sheaves of sets -/

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- **The unit of the adjunction of Stacks 03D7, on underlying sheaves of sets**: the unit of
`f⁻¹ ⊣ f_*` followed by the direct image of the unit of extension of scalars. This is
`Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules_unit_app` with each of its two
factors read on underlying sheaves of sets. -/
private lemma moduleSheafFunctor_map_pullbackAdj_unit_app :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((pullbackAdjPushforwardModules f).unit.app A) =
      f.toToposHom.adj.unit.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A) ≫
        f.toToposHom.pushforward.map
          ((Sheaf.moduleSheafFunctor
              (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
            ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
              (inverseImageRingSheaf f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
              ((inverseImageModules f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A))) := by
  refine Eq.trans (congrArg (Sheaf.moduleSheafFunctor
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
    (pullbackAdjPushforwardModules_unit_app f A)) ?_
  refine Eq.trans ((Sheaf.moduleSheafFunctor
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map_comp _ _) ?_
  refine Eq.trans (congrArg (fun z ↦ z ≫
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((directImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
            (inverseImageRingSheaf f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A))))
    (moduleSheafFunctor_map_inverseImageAdjDirectImageModules_unit_app' f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A)) ?_
  exact congrArg
    (fun z ↦ f.toToposHom.adj.unit.app
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A) ≫ z)
    (moduleSheafFunctor_map_directImageModules_map f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A)))

/-! ### The chain of Tag 03EL, expanded -/

/-- The inverse of the chain of bijections of Tag 03EL, written as the six steps. True by
definition. -/
private lemma pullbackTensorHomEquiv_symm_eq
    (F G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (k : (Functor.prod (f.pullbackModules) (f.pullbackModules) ⋙
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj (F, G) ⟶ N) :
    (pullbackTensorHomEquiv f F G N).symm k =
      (pullbackTensorStep1 f F G N).symm ((pullbackTensorStep2 f F G N).symm
        ((pullbackTensorStep3 f F G N).symm ((pullbackTensorStep4 f F G N).symm
          ((pullbackTensorStep5 f F G N).symm
            ((pullbackTensorStep6 f F G N).symm k))))) := rfl

/-! ### The coherence, transposed to the target topos -/

/-- **Steps 2 to 6 of the chain of Tag 03EL carry the second factor of the coherence to the right
unitor followed by the unit of Stacks 03D7.**

This is the coherence itself, moved to the target topos by the adjunction of Stacks 03D7 — where
the source `A ⊗_{O_D} O_D` is a tensor product sheaf of two sheaves on `D` and therefore has local
sections. On the unit image of `a ⊗ₜ r` the right-hand side is `η_A(r · a)`, and the left-hand side
is the pair `(a, r)` carried through the topos unit and then through the direct image of the
pairing upstairs, which `bottomPairing_comp_rightUnitorFactor` identifies with the inverse image of
the right scalar action followed by the unit of extension of scalars; the two agree by the
naturality of the topos unit. -/
private lemma transposedComparison_eq
    (ν : pullbackObj f (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hν : ∀ (V : X.Cᵒᵖ)
        (s : ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).val.obj V),
        ν.val.app V
            (extendUnitSection f
              ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
                (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) V s) =
          f.fSharpInverseImage.hom.app V s) :
    (pullbackTensorStep2 f A (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (pullbackObj f A)).symm
        ((pullbackTensorStep3 f A (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            (pullbackObj f A)).symm
          ((pullbackTensorStep4 f A
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
              (pullbackObj f A)).symm
            ((pullbackTensorStep5 f A
              (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
                (pullbackObj f A)).symm
              ((pullbackTensorStep6 f A
                (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
                  (pullbackObj f A)).symm (rightUnitorFactor f A ν))))) =
      (tensorSheafUnitRightIso Y.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property A).hom ≫
        (pullbackAdjPushforwardModules f).unit.app A := by
  have h4 : (pullbackTensorStep4 f A
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (pullbackObj f A)).symm
        (pullbackTensorBottomHom f A
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫
          (SheafOfModules.restrictScalars f.fSharpInverseImage).map
            (rightUnitorFactor f A ν)) =
      ⟨((pullbackTensorStep4 f A (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
              (pullbackTensorTarget f A
                (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).symm
            (pullbackTensorBottomHom f A
              (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).1 ≫
          (Sheaf.moduleSheafFunctor
              (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
            ((SheafOfModules.restrictScalars f.fSharpInverseImage).map
              (rightUnitorFactor f A ν)),
        ((pullbackTensorStep4 f A (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
              (pullbackTensorTarget f A
                (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).symm
            (pullbackTensorBottomHom f A
              (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).2.comp
          ((SheafOfModules.restrictScalars f.fSharpInverseImage).map
            (rightUnitorFactor f A ν))⟩ := by
    refine (Equiv.symm_apply_eq _).mpr ?_
    refine Eq.trans ?_ (pullbackTensorStep4_naturality f A
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        _ (rightUnitorFactor f A ν)).symm
    exact congrArg (fun m ↦ m ≫ (SheafOfModules.restrictScalars f.fSharpInverseImage).map
        (rightUnitorFactor f A ν))
      (Equiv.apply_symm_apply (pullbackTensorStep4 f A
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (pullbackTensorTarget f A
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
        (pullbackTensorBottomHom f A
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).symm
  rw [step5_symm_step6_symm_eq f A
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (pullbackObj f A) (rightUnitorFactor f A ν), h4]
  refine tensorSheaf_hom_ext fun U a r ↦ ?_
  refine Eq.trans (pullbackTensorStep2_symm_step3_symm_val_app_unit_tmul f A
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (pullbackObj f A) _ U a r) ?_
  refine Eq.trans (congrArg (fun m ↦ (Sheaf.sectionsFunctor Y.J U).map
      (f.toToposHom.pushforward.map
        (prodComparison f.toToposHom.inverseImage
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A)
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ≫ m))
      ((Sheaf.sectionsFunctor Y.J U).map
        (f.toToposHom.adj.unit.app
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A ⨯
            Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
        (Functor.prodObjMk a r)))
    (bottomPairing_comp_rightUnitorFactor f A ν hν)) ?_
  refine Eq.trans (congrArg (fun m ↦ (Sheaf.sectionsFunctor Y.J U).map
      (f.toToposHom.pushforward.map m)
      ((Sheaf.sectionsFunctor Y.J U).map
        (f.toToposHom.adj.unit.app
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A ⨯
            Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
        (Functor.prodObjMk a r)))
    (assoc_symm _ _ _)) ?_
  refine Eq.trans (congrArg (fun m ↦ (Sheaf.sectionsFunctor Y.J U).map
      (f.toToposHom.pushforward.map (m ≫
        (Sheaf.moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
          ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
            (inverseImageRingSheaf f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A))))
      ((Sheaf.sectionsFunctor Y.J U).map
        (f.toToposHom.adj.unit.app
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A ⨯
            Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
        (Functor.prodObjMk a r)))
    (prodComparison_comp_invSmulRightHom f A)) ?_
  have hnat : (Sheaf.sectionsFunctor Y.J U).map
        (f.toToposHom.pushforward.map
          (f.toToposHom.inverseImage.map
            (smulRightUnitHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A)))
        ((Sheaf.sectionsFunctor Y.J U).map
          (f.toToposHom.adj.unit.app
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A ⨯
              Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
                (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
          (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J U)
            (A := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A)
            (B := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) a r)) =
      (Sheaf.sectionsFunctor Y.J U).map
        (f.toToposHom.adj.unit.app
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A))
        ((Sheaf.sectionsFunctor Y.J U).map
          (smulRightUnitHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A)
          (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J U)
            (A := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A)
            (B := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) a r)) := by
    refine Eq.trans ((Sheaf.sectionsFunctor Y.J U).map_comp_apply
      (f.toToposHom.adj.unit.app
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A ⨯
          Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
      (f.toToposHom.pushforward.map
        (f.toToposHom.inverseImage.map
          (smulRightUnitHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A))) _).symm ?_
    refine Eq.trans (congrArg (fun m ↦ (Sheaf.sectionsFunctor Y.J U).map m
        (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J U)
          (A := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A)
          (B := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) a r))
      (f.toToposHom.adj.unit.naturality
        (smulRightUnitHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A)).symm) ?_
    exact (Sheaf.sectionsFunctor Y.J U).map_comp_apply
      (smulRightUnitHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A)
      (f.toToposHom.adj.unit.app
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A)) _
  have hRHS : ((tensorSheafUnitRightIso Y.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property A).hom ≫
        (pullbackAdjPushforwardModules f).unit.app A).val.app U
        (((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf Y.J Y.O.obj
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property) (𝟙 _)).unit.app
            (A.val ⊗ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).val)).app U
          (a ⊗ₜ[(ringPresheaf Y.O.obj).obj U] r)) =
      (Sheaf.sectionsFunctor Y.J U).map
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          ((pullbackAdjPushforwardModules f).unit.app A))
        ((Sheaf.sectionsFunctor Y.J U).map
          (smulRightUnitHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A)
          (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J U)
            (A := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A)
            (B := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) a r)) := by
    refine Eq.trans (CategoryTheory.comp_apply _ _ _) ?_
    exact congrArg ((Sheaf.sectionsFunctor Y.J U).map
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          ((pullbackAdjPushforwardModules f).unit.app A)))
      ((tensorSheafUnitRightIso_hom_toSheafify_tmul Y.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property A U
          a r).trans
        (sectionsFunctor_map_smulRightUnitHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A U a r).symm)
  refine Eq.trans (congrArg (fun m ↦ (Sheaf.sectionsFunctor Y.J U).map m
      ((Sheaf.sectionsFunctor Y.J U).map
        (f.toToposHom.adj.unit.app
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A ⨯
            Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
        (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J U)
          (A := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A)
          (B := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) a r)))
    (f.toToposHom.pushforward.map_comp
      (f.toToposHom.inverseImage.map
        (smulRightUnitHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A))
      ((Sheaf.moduleSheafFunctor
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
        ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
          ((inverseImageModules f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A))))) ?_
  refine Eq.trans ((Sheaf.sectionsFunctor Y.J U).map_comp_apply _ _ _) ?_
  refine Eq.trans (congrArg ((Sheaf.sectionsFunctor Y.J U).map
      (f.toToposHom.pushforward.map
        ((Sheaf.moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
          ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
            (inverseImageRingSheaf f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A))))) hnat) ?_
  refine Eq.trans ((Sheaf.sectionsFunctor Y.J U).map_comp_apply
    (f.toToposHom.adj.unit.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A))
    (f.toToposHom.pushforward.map
      ((Sheaf.moduleSheafFunctor
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
        ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
          ((inverseImageModules f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj A)))) _).symm ?_
  refine Eq.trans (congrArg (fun m ↦ (Sheaf.sectionsFunctor Y.J U).map m
      ((Sheaf.sectionsFunctor Y.J U).map
        (smulRightUnitHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A)
        (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J U)
          (A := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) A)
          (B := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) a r)))
    (moduleSheafFunctor_map_pullbackAdj_unit_app f A).symm) ?_
  exact hRHS.symm

/-! ### The coherence -/

/-- **The right-unitor coherence of Stacks 03EL for an arbitrary morphism of ringed topoi.**

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi in the sense of
`Stacks.Sheaves.RingedToposModules.RingedToposHom` — four fields, no presentation of the morphism
of topoi by a functor of sites — let `A` be a sheaf of `O_D`-modules and let `ν : f^*O_D ⟶ O_C` be
the unit comparison, characterised by `hν`: its composite with the unit of extension of scalars is
the inverse-image form `f⁻¹O_D ⟶ O_C` of the structure map, on local sections. Then the comparison
of Stacks 03EL at `B = O_D`

`f^*(A ⊗_{O_D} O_D) ⟶ f^*A ⊗_{O_C} f^*O_D`,

followed by `𝟙 ⊗ ν` and by the right unitor of `f^*A`, is the pullback of the right unitor of `A`.

The hypothesis `hν` pins `ν` down: by the adjunction of Stacks 03CZ a morphism
`f^*O_D ⟶ O_C` is the same thing as a morphism `f⁻¹O_D ⟶ O_C|_{f⁻¹O_D}`, and `hν` says that `ν`
is the one belonging to `f♯`. It is stated on local sections rather than as an identity of
adjuncts because that is the form in which the computation uses it, and the form a consumer with a
concrete `ν` can check.

The proof is the chain of bijections of Stacks 03EL, evaluated. The universal property of the
comparison turns the identity into one about the preimage of `𝟙 ⊗ ν` followed by the right unitor
under the chain; the first step of the chain is the adjunction of Stacks 03D7, and transposing
along it moves the identity to the target topos, where the source `A ⊗_{O_D} O_D` has local
sections; and on the unit image of a pure tensor `a ⊗ₜ r` both sides are `η_A(r · a)`, the
left-hand side because the bottom of the chain pairs two sections by the pure tensor of their
images under the unit of extension of scalars, because `ν` turns the second of those into `f♯(r)`
and because that unit is a map of `f⁻¹O_D`-modules. -/
theorem pullbackTensorIso_hom_app_comp_rightUnitor
    (ν : (f.pullbackModules).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hν : ∀ (V : X.Cᵒᵖ)
        (s : ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).val.obj V),
        ν.val.app V
            (((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
                (inverseImageRingSheaf f.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
              ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
                (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).val.app V s) =
          f.fSharpInverseImage.hom.app V s) :
    (pullbackTensorIso f).hom.app
      (A, SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).map
            ((𝟙 ((f.pullbackModules).obj A), ν) :
              ((f.pullbackModules).obj A,
                (f.pullbackModules).obj
                  (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ⟶
              ((f.pullbackModules).obj A,
                SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ≫
          (tensorSheafUnitRightIso X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
            ((f.pullbackModules).obj A)).hom =
      (f.pullbackModules).map
        (tensorSheafUnitRightIso Y.O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property A).hom := by
  show (pullbackTensorIso f).hom.app
      (A, SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫
      rightUnitorFactor f A ν = _
  refine Eq.trans (congrArg (fun m ↦ m ≫ rightUnitorFactor f A ν)
    (pullbackTensorIso_hom_app f A
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))) ?_
  refine Eq.trans (pullbackTensorHomEquiv_symm_naturality f A
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (𝟙 _) (rightUnitorFactor f A ν)).symm ?_
  refine Eq.trans (congrArg (pullbackTensorHomEquiv f A
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (pullbackObj f A)).symm
    (Category.id_comp (rightUnitorFactor f A ν))) ?_
  refine Eq.trans (pullbackTensorHomEquiv_symm_eq f A
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (pullbackObj f A)
    (rightUnitorFactor f A ν)) ?_
  refine (Equiv.symm_apply_eq (pullbackTensorStep1 f A
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (pullbackObj f A))).mpr ?_
  refine Eq.trans (transposedComparison_eq f A ν hν) ?_
  refine Eq.trans ?_ (congrArg (pullbackTensorStep1 f A
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (pullbackObj f A))
    (Category.comp_id ((f.pullbackModules).map
      (tensorSheafUnitRightIso Y.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property A).hom)))
  refine Eq.trans ?_ ((pullbackAdjPushforwardModules f).homEquiv_naturality_left
    (tensorSheafUnitRightIso Y.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property A).hom
    (𝟙 ((f.pullbackModules).obj A))).symm
  exact congrArg
    (fun m ↦ (tensorSheafUnitRightIso Y.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property A).hom ≫ m)
    ((pullbackAdjPushforwardModules f).homEquiv_id A).symm

end RightUnitor

end Stacks.SheafOfModules

end
