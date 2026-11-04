module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleStalkFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullback

/-!
# The stalk of a sheaf of modules carries the transported module structure

Let `(C, J)` be a site, `Φ` a point of it, `R` a sheaf of rings and `G` a sheaf of
`R`-modules.  There are two ways to put a module structure on the stalk of `G` at `Φ`.

The first is to take the colimit *in modules*: the stalk `G_Φ` of Stacks 04EH, computed as the
filtered colimit of the sections of `G` over the category of neighbourhoods of `Φ`, is a module
over the stalk `R_Φ` of the sheaf of rings.  This is `Stacks.sheafModuleFiber`.

The second is to take the stalk of the underlying sheaf of *sets* and transport the scalar
action along it.  The stalk functor on sheaves of sets preserves finite limits, so it carries
the addition and the scalar multiplication of `G`, which are morphisms of sheaves of sets out
of a finite product, to maps on the stalks; this is the algebraic form of Stacks 03D2 recorded
by `CategoryTheory.Sheaf.moduleObjModule`, and it is the structure the inverse image of
sheaves of modules along a morphism of topoi is built from.

This file identifies the two.  On underlying sets the identification is the comparison of
Mathlib's `GrothendieckTopology.Point.presheafFiberCompIso` for the forgetful functors, and
what is proved here is that it is additive and semilinear: a germ of a scalar acting on a germ
of a section is the germ of the product, in both structures.

## Main definitions

* `Stacks.Sheaves.StalkTransport.ringStalkComparison`: the stalk of the underlying sheaf of
  sets of a sheaf of rings is the underlying set of its stalk as a sheaf of rings.
* `Stacks.Sheaves.StalkTransport.moduleStalkComparison`: the stalk of the underlying sheaf of
  sets of a sheaf of modules is the underlying set of its stalk as a sheaf of modules.

## Main results

* `Stacks.Sheaves.StalkTransport.ringStalkComparison_germ` and
  `Stacks.Sheaves.StalkTransport.moduleStalkComparison_germ`: both comparisons carry a germ to
  the corresponding germ.
* `Stacks.Sheaves.StalkTransport.moduleStalkComparison_moduleAddObj`: the comparison is
  additive for the transported addition.
* `Stacks.Sheaves.StalkTransport.moduleStalkComparison_moduleSMulObj`: the comparison is
  semilinear for the transported scalar action, over the comparison of stalk rings.

## Implementation notes

The proofs are germ computations, and the device that makes them short is to take the germ in
the *product* sheaf `R ⨯ G` rather than in the two factors separately.  An element of the
stalk of the product is a germ of a section of the product over a single neighbourhood, by
`CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_jointly_surjective`; its two
projections are then germs of the two components over that same neighbourhood, so no
refinement of a pair of neighbourhoods to a common one is needed.  Both transported operations
are the image under the stalk functor of a morphism of sheaves of sets out of the product, so
naturality of the germ maps evaluates them on that section, and the sectionwise description of
those morphisms finishes the computation.

Both comparisons are stated for the fibre functor on *presheaves* applied to the underlying
presheaf, rather than for the fibre functor on sheaves applied to the underlying sheaf.  The
two agree definitionally, Mathlib's `GrothendieckTopology.Point.sheafFiber` being
`sheafToPresheaf ⋙ presheafFiber`, and the presheaf spelling is the one in which the germ
lemma `GrothendieckTopology.Point.toPresheafFiber_presheafFiberCompIso_hom_app` is stated.

## References

* [Stacks Project, Tag 04EH](https://stacks.math.columbia.edu/tag/04EH)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe w v u

namespace Stacks.Sheaves.StalkTransport

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (Φ : J.Point.{w}) (R : Sheaf J RingCat.{w})

/-- **The stalk of the underlying sheaf of sets of a sheaf of rings.**  It is the underlying
set of the stalk of the sheaf of rings, the forgetful functor preserving filtered colimits. -/
def ringStalkComparison :
    (Φ.sheafFiber (A := Type w)).obj (Sheaf.ringSheaf R) →
      (Φ.presheafFiber (A := RingCat.{w})).obj R.obj :=
  (Φ.presheafFiberCompIso (forget RingCat.{w})).hom.app R.obj

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The comparison of stalks of a sheaf of rings carries a germ to the corresponding germ. -/
lemma ringStalkComparison_germ (U : C) (x : Φ.fiber.obj U)
    (s : (Sheaf.ringSheaf R).obj.obj (op U)) :
    ringStalkComparison Φ R (Φ.toPresheafFiber U x (Sheaf.ringSheaf R).obj s) =
      Φ.toPresheafFiber U x R.obj s :=
  ConcreteCategory.congr_hom
    (Φ.toPresheafFiber_presheafFiberCompIso_hom_app (F := forget RingCat.{w}) U x R.obj) s

variable (G : SheafOfModules.{w} R)

/-- **The stalk of the underlying sheaf of sets of a sheaf of modules.**  It is the underlying
set of the stalk of the sheaf of modules. -/
def moduleStalkComparison :
    (Φ.sheafFiber (A := Type w)).obj (Sheaf.moduleSheaf R G) →
      (Stacks.sheafModuleFiber Φ R).obj G :=
  (Φ.presheafFiberCompIso (forget AddCommGrpCat.{w})).hom.app G.val.presheaf

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The comparison of stalks of a sheaf of modules carries a germ to the corresponding
germ. -/
lemma moduleStalkComparison_germ (U : C) (x : Φ.fiber.obj U)
    (s : (Sheaf.moduleSheaf R G).obj.obj (op U)) :
    moduleStalkComparison Φ R G (Φ.toPresheafFiber U x (Sheaf.moduleSheaf R G).obj s) =
      Stacks.toPresheafModuleFiber Φ G.val U x s :=
  ConcreteCategory.congr_hom
    (Φ.toPresheafFiber_presheafFiberCompIso_hom_app (F := forget AddCommGrpCat.{w})
      U x G.val.presheaf) s

omit [LocallySmall.{w} C] in
/-- The germ of a section of the product of the underlying sheaves of sets has the germ of its
first component as its image under the first projection. -/
lemma map_fst_toPresheafFiber (U : C) (x : Φ.fiber.obj U)
    (p : (Sheaf.ringSheaf R ⨯ Sheaf.moduleSheaf R G).obj.obj (op U)) :
    (Φ.sheafFiber (A := Type w)).map (prod.fst : Sheaf.ringSheaf R ⨯ Sheaf.moduleSheaf R G ⟶ _)
        (Φ.toPresheafFiber U x (Sheaf.ringSheaf R ⨯ Sheaf.moduleSheaf R G).obj p) =
      Φ.toPresheafFiber U x (Sheaf.ringSheaf R).obj
        ((prod.fst : Sheaf.ringSheaf R ⨯ Sheaf.moduleSheaf R G ⟶ _).hom.app (op U) p) :=
  Φ.toPresheafFiber_naturality_apply
    (prod.fst : Sheaf.ringSheaf R ⨯ Sheaf.moduleSheaf R G ⟶ _).hom U x p

omit [LocallySmall.{w} C] in
/-- The germ of a section of the product of the underlying sheaves of sets has the germ of its
second component as its image under the second projection. -/
lemma map_snd_toPresheafFiber (U : C) (x : Φ.fiber.obj U)
    (p : (Sheaf.ringSheaf R ⨯ Sheaf.moduleSheaf R G).obj.obj (op U)) :
    (Φ.sheafFiber (A := Type w)).map (prod.snd : Sheaf.ringSheaf R ⨯ Sheaf.moduleSheaf R G ⟶ _)
        (Φ.toPresheafFiber U x (Sheaf.ringSheaf R ⨯ Sheaf.moduleSheaf R G).obj p) =
      Φ.toPresheafFiber U x (Sheaf.moduleSheaf R G).obj
        ((prod.snd : Sheaf.ringSheaf R ⨯ Sheaf.moduleSheaf R G ⟶ _).hom.app (op U) p) :=
  Φ.toPresheafFiber_naturality_apply
    (prod.snd : Sheaf.ringSheaf R ⨯ Sheaf.moduleSheaf R G ⟶ _).hom U x p

/-- A pair of germs in the stalks of two sheaves of sets is the pair of projections of the germ of
a single section of the product, and every morphism out of the product acts on it sectionwise. -/
private lemma exists_germ_prodObjMk {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
    {J : GrothendieckTopology C}
    (Φ : J.Point.{w}) {X Y : Sheaf J (Type w)}
    (a : (Φ.sheafFiber (A := Type w)).obj X) (b : (Φ.sheafFiber (A := Type w)).obj Y) :
    ∃ (U : C) (x : Φ.fiber.obj U) (p : (X ⨯ Y).obj.obj (op U)),
      a = Φ.toPresheafFiber U x X.obj ((prod.fst : X ⨯ Y ⟶ _).hom.app (op U) p) ∧
      b = Φ.toPresheafFiber U x Y.obj ((prod.snd : X ⨯ Y ⟶ _).hom.app (op U) p) ∧
      ∀ (Z : Sheaf J (Type w)) (f : X ⨯ Y ⟶ Z),
        (Φ.sheafFiber (A := Type w)).map f
            (Functor.prodObjMk (P := Φ.sheafFiber (A := Type w)) a b) =
          Φ.toPresheafFiber U x Z.obj (f.hom.app (op U) p) := by
  obtain ⟨U, x, p, hp⟩ := Φ.toPresheafFiber_jointly_surjective (P := (X ⨯ Y).obj)
    (Functor.prodObjMk (P := Φ.sheafFiber (A := Type w)) a b)
  have h (Z : Sheaf J (Type w)) (f : X ⨯ Y ⟶ Z) :
      (Φ.sheafFiber (A := Type w)).map f
          (Functor.prodObjMk (P := Φ.sheafFiber (A := Type w)) a b) =
        Φ.toPresheafFiber U x Z.obj (f.hom.app (op U) p) := by
    rw [← hp]
    exact Φ.toPresheafFiber_naturality_apply f.hom U x p
  exact ⟨U, x, p, by rw [← h, Functor.map_fst_prodObjMk], by rw [← h, Functor.map_snd_prodObjMk],
    h⟩

/-- **The comparison is semilinear.**  The transported scalar action on the stalk of the
underlying sheaf of sets agrees with the action of the stalk ring on the stalk taken in
modules. -/
lemma moduleStalkComparison_moduleSMulObj
    (r : (Φ.sheafFiber (A := Type w)).obj (Sheaf.ringSheaf R))
    (m : (Φ.sheafFiber (A := Type w)).obj (Sheaf.moduleSheaf R G)) :
    moduleStalkComparison Φ R G
        (Sheaf.moduleSMulObj R G (Φ.sheafFiber (A := Type w)) r m) =
      ringStalkComparison Φ R r • moduleStalkComparison Φ R G m := by
  obtain ⟨U, x, p, hr, hm, h⟩ := exists_germ_prodObjMk Φ r m
  rw [Sheaf.moduleSMulObj, h, hr, hm, ringStalkComparison_germ, moduleStalkComparison_germ,
    moduleStalkComparison_germ]
  exact Stacks.toPresheafModuleFiber_smul Φ G.val U x _ _

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- **The comparison is additive.**  The transported addition on the stalk of the underlying
sheaf of sets agrees with the addition of the stalk taken in modules. -/
lemma moduleStalkComparison_moduleAddObj
    (m n : (Φ.sheafFiber (A := Type w)).obj (Sheaf.moduleSheaf R G)) :
    moduleStalkComparison Φ R G
        (Sheaf.moduleAddObj R G (Φ.sheafFiber (A := Type w)) m n) =
      moduleStalkComparison Φ R G m + moduleStalkComparison Φ R G n := by
  obtain ⟨U, x, p, hm, hn, h⟩ := exists_germ_prodObjMk Φ m n
  rw [Sheaf.moduleAddObj, h, hm, hn, moduleStalkComparison_germ, moduleStalkComparison_germ,
    moduleStalkComparison_germ]
  exact map_add (Stacks.toPresheafModuleFiber Φ G.val U x) _ _

end Stacks.Sheaves.StalkTransport

end

end
