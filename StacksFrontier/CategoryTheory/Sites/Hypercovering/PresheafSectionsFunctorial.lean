module

public import StacksFrontier.CategoryTheory.Limits.FormalCoproductAdditive
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.HomComplexAugmentation

/-!
# The sections of a hypercovering of a presheaf, functorially in the coefficient sheaf

Let `C` be a site and let `K` be a simplicial semi-representable object of `C`.  Evaluating a
sheaf `F` of abelian groups on the levels of `K` gives the complex `s(F(K))`, and
[Stacks, Tag 01GX] identifies it with the complex `Hom(s(**Z**_{F(K)}^♯), F)` of morphisms out of
the associated complex of free abelian sheaves.  The identification in the library is made at a
fixed `F`; this file supplies the ingredients that make it an isomorphism of *functors* of `F`,
which is what the comparison map of [Stacks, Tag 09VX] is built out of.

## Main definitions

* `SemiRepresentable.sectionsComplexFunctor`: the complex `s(-(K))`, as a functor of the
  coefficient sheaf.
* `SemiRepresentable.sectionsComplexIntFunctor`: the same, extended by zero to integer degrees,
  which is the shape the construction of the comparison map consumes.
* `ChainComplex.homComplexFunctorIsoOfIso`: an isomorphism of chain complexes induces an
  isomorphism of the functors of morphisms out of them.

## Main results

* `SemiRepresentable.yonedaEquiv_comp`: the Yoneda identification for the lifted representable
  presheaves is compatible with postcomposition.
* `SemiRepresentable.sectionsEquiv_comp`: the identification of the morphisms out of the free
  abelian sheaf of a semi-representable object with a product of groups of sections is
  compatible with postcomposition in the coefficient sheaf.  This is the computational content
  of the naturality of [Stacks, Tag 01GX] in the coefficient sheaf.
* `SemiRepresentable.isZero_sectionsComplexIntFunctor_obj_X`: the extended complex vanishes in
  negative degrees.

## Implementation notes

`ChainComplex.homComplexFunctorIsoOfIso` is needed because the complex of free abelian sheaves
attached to a hypercovering of a presheaf is written two ways in the library: as
`CategoryTheory.SimplicialObject.Augmented.freeAbelianSheafHomCx` at the augmented simplicial
presheaf `HypercoveringOf.toAugmentedULift`, which is the spelling the comparison map of
[Stacks, Tag 09VX] consumes, and through
`Stacks.CategoryTheory.Hypercovering.SemiRepresentable.associatedSimplicialPresheaf`, which is
the spelling [Stacks, Tag 01GX] is stated at.  The two differ by
`HypercoveringOf.toAugmentedULiftLeftIso`, and the transport has to pass through the Hom complex,
contravariantly.

The naturality computations are element-level rather than diagrammatic: `sectionsEquiv` is an
`Equiv.trans` of three bijections — the sheafification adjunction, the free-abelian-presheaf
adjunction and the Yoneda identification — none of which is `simp`-normal, and each is natural in
its right variable, so the compatibility is proved by rewriting with the three naturality
statements in turn.

## References

* [Stacks Project, Tag 01GX](https://stacks.math.columbia.edu/tag/01GX)
* [Stacks Project, Tag 09VX](https://stacks.math.columbia.edu/tag/09VX)
-/

@[expose] public section

universe q w v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace ChainComplex

variable {W : Type u} [Category.{v} W] [Preadditive W]

/-- **An isomorphism of chain complexes induces an isomorphism of the functors of morphisms out
of them**, contravariantly.  This is what transports [Stacks, Tag 01GX] between the two spellings
of the complex of free abelian sheaves of a hypercovering. -/
noncomputable def homComplexFunctorIsoOfIso {R R' : ChainComplex W ℕ} (e : R ≅ R') :
    homComplexFunctor R' ≅ homComplexFunctor R :=
  NatIso.ofComponents
    (fun F ↦ ((preadditiveYoneda.obj F).mapHomologicalComplex (ComplexShape.down ℕ).symm).mapIso
      ((HomologicalComplex.opFunctor W (ComplexShape.down ℕ)).mapIso e.op))
    (fun {_ _} g ↦ ((NatTrans.mapHomologicalComplex (preadditiveYoneda.map g)
      (ComplexShape.down ℕ).symm).naturality
      ((HomologicalComplex.opFunctor W (ComplexShape.down ℕ)).map e.op.hom)).symm)

/-- **Precomposition on Hom complexes is compatible with the transport along an isomorphism of
chain complexes.**  Given a commuting square of chain complexes whose vertical edges are
isomorphisms, the two Hom complexes transport the two precomposition maps into one another.  This
is what lets the comparison of [Stacks, Tag 01GX] be read through the two spellings of the complex
of free abelian sheaves of a hypercovering of a presheaf. -/
theorem homComplexFunctorPrecomp_comp_homComplexFunctorIsoOfIso
    {R R' S S' : ChainComplex W ℕ} (c : R ⟶ S) (c' : R' ⟶ S') (e : R ≅ R') (e' : S ≅ S')
    (h : c ≫ e'.hom = e.hom ≫ c') :
    (homComplexFunctorIsoOfIso e').hom ≫ homComplexFunctorPrecomp c =
      homComplexFunctorPrecomp c' ≫ (homComplexFunctorIsoOfIso e).hom := by
  refine NatTrans.ext (funext fun F ↦ HomologicalComplex.hom_ext _ _ fun n ↦ ?_)
  have hn : c.f n ≫ e'.hom.f n = e.hom.f n ≫ c'.f n :=
    congrArg (fun t ↦ HomologicalComplex.Hom.f t n) h
  have key : (e'.hom.f n).op ≫ (c.f n).op = (c'.f n).op ≫ (e.hom.f n).op := by
    rw [← op_comp, ← op_comp, hn]
  exact ((preadditiveYoneda.obj F).map_comp (e'.hom.f n).op (c.f n).op).symm.trans
    ((congrArg ((preadditiveYoneda.obj F).map) key).trans
      ((preadditiveYoneda.obj F).map_comp (c'.f n).op (e.hom.f n).op))


end ChainComplex

namespace Stacks.CategoryTheory.Hypercovering.SemiRepresentable

variable {C : Type u} [Category.{v} C]

/-- **The Yoneda identification for the lifted representable presheaves is compatible with
postcomposition.**  It is `uliftYonedaEquiv` precomposed with a fixed isomorphism, and
`uliftYonedaEquiv` has this property. -/
lemma yonedaEquiv_comp (X : C) {P Q : Cᵒᵖ ⥤ Type (max (max u v) (max q w))} (m : P ⟶ Q)
    (k : (presheafULift.{q, w, v, u} (C := C)).obj (uliftYoneda.{w}.obj X) ⟶ P) :
    yonedaEquiv.{q, w, v, u} (C := C) X Q (k ≫ m) =
      m.app (op X) (yonedaEquiv.{q, w, v, u} (C := C) X P k) := by
  show uliftYonedaEquiv.{max (max u v) (max q w)}
      ((nestedYonedaIso.{q, w, v, u} (C := C) X).inv ≫ k ≫ m) = _
  rw [← Category.assoc, uliftYonedaEquiv_comp]
  rfl

/-- **Postcomposition in the coefficient sheaf, read through the identification of the morphisms
out of the free abelian sheaf of a semi-representable object with a product of groups of
sections.**  Each of the three bijections composing `sectionsEquiv` is natural in its right
variable, so the identification is too.  This is the computational content of the naturality of
[Stacks, Tag 01GX] in the coefficient sheaf. -/
lemma sectionsEquiv_comp (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max (max u v) (max q w)}] (T : FormalCoproduct.{w} C)
    {F G : Sheaf J AddCommGrpCat.{max (max u v) (max q w)}} (g : F ⟶ G)
    (f : freeAbelianSheaf.{q, w, v, u} (C := C) J T ⟶ F) (i : T.I) :
    ConcreteCategory.hom (Pi.π (fun i ↦ G.obj.obj (op (T.obj i))) i)
        ((sectionsEquiv.{q, w, v, u} (C := C) J T G).toFun (f ≫ g)) =
      g.hom.app (op (T.obj i))
        (ConcreteCategory.hom (Pi.π (fun i ↦ F.obj.obj (op (T.obj i))) i)
          ((sectionsEquiv.{q, w, v, u} (C := C) J T F).toFun f)) := by
  rw [sectionsEquiv_π.{q, w, v, u} (C := C) J T G (f ≫ g) i,
    sectionsEquiv_π.{q, w, v, u} (C := C) J T F f i,
    (sheafificationAdjunction J AddCommGrpCat.{max (max u v) (max q w)}).homEquiv_naturality_right,
    (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv_naturality_right, ← Category.assoc,
    yonedaEquiv_comp.{q, w, v, u} (C := C)]
  rfl

/-- **The complex of sections `s(-(K))` of a simplicial semi-representable object, as a functor
of the coefficient sheaf.**  Its value at `F` is
`Stacks.CategoryTheory.Hypercovering.SemiRepresentable.sectionsComplex J K F`, the complex whose
cohomology is the Čech cohomology of [Stacks, Tag 09VX]. -/
noncomputable def sectionsComplexFunctor (J : GrothendieckTopology C)
    (K : SimplicialObject (FormalCoproduct.{w} C)) :
    Sheaf J AddCommGrpCat.{max (max u v) (max q w)} ⥤
      CochainComplex AddCommGrpCat.{max (max u v) (max q w)} ℕ :=
  sheafToPresheaf J AddCommGrpCat.{max (max u v) (max q w)} ⋙
    FormalCoproduct.cochainComplexFunctor K

/-- The value of `sectionsComplexFunctor J K` at a sheaf `F` is `sectionsComplex J K F`. -/
lemma sectionsComplexFunctor_obj (J : GrothendieckTopology C)
    (K : SimplicialObject (FormalCoproduct.{w} C))
    (F : Sheaf J AddCommGrpCat.{max (max u v) (max q w)}) :
    (sectionsComplexFunctor.{q, w, v, u} J K).obj F =
      sectionsComplex.{q, w, v, u} J K F := rfl

/-- The Čech cohomology of [Stacks, Tag 09VX] is the cohomology of `sectionsComplexFunctor`. -/
lemma homology_sectionsComplexFunctor_obj (J : GrothendieckTopology C)
    (K : SimplicialObject (FormalCoproduct.{w} C))
    (F : Sheaf J AddCommGrpCat.{max (max u v) (max q w)}) (p : ℕ) :
    ((sectionsComplexFunctor.{q, w, v, u} J K).obj F).homology p =
      (sectionsComplex.{q, w, v, u} J K F).homology p := rfl

/-- The functor of complexes of sections `sectionsComplexFunctor J K` is additive. -/
instance sectionsComplexFunctor_additive (J : GrothendieckTopology C)
    (K : SimplicialObject (FormalCoproduct.{w} C)) :
    (sectionsComplexFunctor.{q, w, v, u} J K).Additive := by
  dsimp only [sectionsComplexFunctor]
  infer_instance

/-- **The complex of sections `s(-(K))`, extended by zero to integer degrees.**  This is the
shape in which the construction of the comparison map of [Stacks, Tag 09VX] consumes it: that
construction asks for a functor into `CochainComplex _ ℤ` vanishing in negative degrees. -/
noncomputable def sectionsComplexIntFunctor (J : GrothendieckTopology C)
    (K : SimplicialObject (FormalCoproduct.{w} C)) :
    Sheaf J AddCommGrpCat.{max (max u v) (max q w)} ⥤
      CochainComplex AddCommGrpCat.{max (max u v) (max q w)} ℤ :=
  sectionsComplexFunctor.{q, w, v, u} J K ⋙
    ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max (max u v) (max q w)}

/-- The functor of integer-graded complexes of sections `sectionsComplexIntFunctor J K` is
additive. -/
instance sectionsComplexIntFunctor_additive (J : GrothendieckTopology C)
    (K : SimplicialObject (FormalCoproduct.{w} C)) :
    (sectionsComplexIntFunctor.{q, w, v, u} J K).Additive := by
  dsimp only [sectionsComplexIntFunctor, sectionsComplexFunctor]
  infer_instance

/-- **The extended complex of sections vanishes in negative degrees.**  This is the hypothesis
`hT0` of the construction of the comparison map of [Stacks, Tag 09VX]. -/
lemma isZero_sectionsComplexIntFunctor_obj_X (J : GrothendieckTopology C)
    (K : SimplicialObject (FormalCoproduct.{w} C))
    (F : Sheaf J AddCommGrpCat.{max (max u v) (max q w)}) (n : ℤ) (hn : n < 0) :
    IsZero (((sectionsComplexIntFunctor.{q, w, v, u} J K).obj F).X n) :=
  HomologicalComplex.isZero_extend_X _ _ n (fun i ↦ by
    simp only [ComplexShape.embeddingUpNat_f]
    omega)

/-- **[Stacks, Tag 01GX], natural in the coefficient sheaf.**  The functor of morphisms out of the
complex of free abelian sheaves of a simplicial semi-representable object is its functor of
sections.  The fixed-sheaf isomorphism is `sectionsComplexIsoHomFreeAbelianSheafComplex`; what is
proved here is that it is natural.

The naturality is checked elementwise and stated as a standalone `key`, phrased only in
`sectionsEquiv` and `CategoryTheory.Limits.Pi.map`.  Rewriting in the goal itself is refused: the
goal mentions the two functors, whose values are products only after unfolding definitions that
the rewrite's type-correctness check does not see through. -/
noncomputable def homComplexFunctorIsoSectionsComplexFunctor (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max (max u v) (max q w)}]
    (K : SimplicialObject (FormalCoproduct.{w} C)) :
    ChainComplex.homComplexFunctor
        ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
          (associatedSimplicialPresheaf.{max (max u v) (max q w)} K)) ≅
      sectionsComplexFunctor.{q, w, v, u} J K := by
  refine NatIso.ofComponents
    (fun F ↦ (sectionsComplexIsoHomFreeAbelianSheafComplex.{q, w, v, u} J K F).symm) ?_
  intro F G g
  apply HomologicalComplex.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro z
  apply (Concrete.productEquiv
    (fun i ↦ G.obj.obj (op ((K.obj (op ⦋n⦌)).obj i)))).injective
  funext i
  have key :
      (Concrete.productEquiv (fun i ↦ G.obj.obj (op ((K.obj (op ⦋n⦌)).obj i))))
          (sectionsEquiv.{q, w, v, u} (C := C) J (K.obj (op ⦋n⦌)) G (z ≫ g)) i =
        (Concrete.productEquiv (fun i ↦ G.obj.obj (op ((K.obj (op ⦋n⦌)).obj i))))
          ((ConcreteCategory.hom (CategoryTheory.Limits.Pi.map
              (fun i ↦ g.hom.app (op ((K.obj (op ⦋n⦌)).obj i)))))
            (sectionsEquiv.{q, w, v, u} (C := C) J (K.obj (op ⦋n⦌)) F z)) i := by
    rw [Concrete.productEquiv_apply_apply, Concrete.productEquiv_apply_apply,
      ← ConcreteCategory.comp_apply, Limits.Pi.map_π, ConcreteCategory.comp_apply]
    exact sectionsEquiv_comp.{q, w, v, u} J (K.obj (op ⦋n⦌)) g z i
  exact key

/-- **[Stacks, Tag 01GX], natural in the coefficient sheaf**, in the direction in which the
comparison map of [Stacks, Tag 09VX] consumes it. -/
noncomputable abbrev sectionsComplexFunctorIsoHomComplexFunctor (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max (max u v) (max q w)}]
    (K : SimplicialObject (FormalCoproduct.{w} C)) :
    sectionsComplexFunctor.{q, w, v, u} J K ≅
      ChainComplex.homComplexFunctor
        ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
          (associatedSimplicialPresheaf.{max (max u v) (max q w)} K)) :=
  (homComplexFunctorIsoSectionsComplexFunctor.{q, w, v, u} J K).symm

end Stacks.CategoryTheory.Hypercovering.SemiRepresentable

end
