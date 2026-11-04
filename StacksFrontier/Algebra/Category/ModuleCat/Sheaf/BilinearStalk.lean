module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorBilinear
public import StacksFrontier.CategoryTheory.Sites.Point.OpensConservativeFamily
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types

/-!
# The stalk criterion for bilinearity

A pairing `q : F × G → H` of the underlying sheaves of sets of three sheaves of modules induces,
on the stalk at a point, a map of modules over the stalk of the sheaf of rings. This file proves
that `q` is bilinear as soon as every one of those induced maps is bilinear, which is the third
assertion of the section [Stacks, Tag 0GIG].

The induced map is produced uniformly: a functor `P` to types which preserves finite products
carries the module structures of `F`, `G` and `H` to its values on their underlying sheaves of
sets, by `CategoryTheory.Sheaf.moduleObjModule`, and carries `q` to a map `pairingObj` between
them. `IsBilinearPairingObj` is bilinearity of that map. Taking for `P` the sections over an
object recovers the definition of bilinearity itself; taking a stalk functor gives the induced
map on stalks.

Bilinearity passes to every such `P` unconditionally. The converse needs the stalks to see all of
the site, and is proved from the characterisation of bilinearity by the four commuting squares of
`TensorBilinear.lean`: a conservative family of points is jointly faithful on sheaves of sets, so
an equality of morphisms of sheaves of sets which holds on every stalk holds outright.

## Main definitions

* `Stacks.SheafOfModules.pairingObj` — the map induced on `P`-elements by a pairing.
* `Stacks.SheafOfModules.IsBilinearPairingObj` — bilinearity of that induced map.

## Main results

* `Stacks.SheafOfModules.IsBilinearPairing.isBilinearPairingObj` — a bilinear pairing is bilinear
  on `P`-elements, for every finite-product-preserving `P`.
* `Stacks.SheafOfModules.isBilinearPairing_iff_forall_sheafFiber` — over a site with a
  conservative family of points, bilinearity is bilinearity on every stalk.
* `Stacks.SheafOfModules.isBilinearPairing_iff_stalk` — the same on a topological space, where
  the points of the space are such a family and nothing has to be assumed. This is the stalk
  characterisation of [Stacks, Tag 0GIG].

## References

* [Stacks Project, Tag 0GIG](https://stacks.math.columbia.edu/tag/0GIG)
-/

@[expose] public noncomputable section

open CategoryTheory Limits CategoryTheory.Sheaf TopologicalSpace
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules

universe w v u t

namespace Stacks.SheafOfModules

/-! ### Elements of an iterated product -/

section ProdExt

variable {D : Type u} [Category.{v} D] [HasFiniteProducts D]
  (P : D ⥤ Type t) [PreservesFiniteProducts P]

/-- Every element of `P` of a binary product is a pair of elements. -/
private theorem exists_prodObjMk {X Y : D} (s : P.obj (X ⨯ Y)) :
    ∃ (x : P.obj X) (y : P.obj Y), s = Functor.prodObjMk x y :=
  ⟨_, _, (Functor.prodObjMk_map_fst_map_snd s).symm⟩

/-- Two morphisms out of `(X ⨯ Y) ⨯ Z` have the same image under a finite-product-preserving
functor to types as soon as those images agree on the elements coming from a triple. -/
lemma map_ext_prodProd {X Y Z E : D} {m m' : (X ⨯ Y) ⨯ Z ⟶ E}
    (h : ∀ (x : P.obj X) (y : P.obj Y) (z : P.obj Z),
      P.map m (Functor.prodObjMk (Functor.prodObjMk x y) z) =
        P.map m' (Functor.prodObjMk (Functor.prodObjMk x y) z)) :
    P.map m = P.map m' := by
  refine ConcreteCategory.hom_ext _ _ fun s ↦ ?_
  obtain ⟨p, z, rfl⟩ := exists_prodObjMk P s
  obtain ⟨x, y, rfl⟩ := exists_prodObjMk P p
  exact h x y z

/-- Two morphisms out of `X ⨯ (Y ⨯ Z)` have the same image under a finite-product-preserving
functor to types as soon as those images agree on the elements coming from a triple. -/
lemma map_ext_prodProd' {X Y Z E : D} {m m' : X ⨯ (Y ⨯ Z) ⟶ E}
    (h : ∀ (x : P.obj X) (y : P.obj Y) (z : P.obj Z),
      P.map m (Functor.prodObjMk x (Functor.prodObjMk y z)) =
        P.map m' (Functor.prodObjMk x (Functor.prodObjMk y z))) :
    P.map m = P.map m' := by
  refine ConcreteCategory.hom_ext _ _ fun s ↦ ?_
  obtain ⟨x, p, rfl⟩ := exists_prodObjMk P s
  obtain ⟨y, z, rfl⟩ := exists_prodObjMk P p
  exact h x y z

end ProdExt

/-! ### Bilinearity on generalized elements -/

section Obj

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (R : Sheaf J RingCat.{w}) {A B N : SheafOfModules.{w} R}
  (q : moduleSheaf R A ⨯ moduleSheaf R B ⟶ moduleSheaf R N)
  (P : Sheaf J (Type w) ⥤ Type t) [PreservesFiniteProducts P]

/-- The value of a pairing of the underlying sheaves of sets on a pair of elements of the images
of those sheaves under a finite-product-preserving functor `P` to types. For `P` the sections
over an object this is `pairingApp`, and for `P` a stalk functor it is the induced map on
stalks. -/
def pairingObj (x : P.obj (moduleSheaf R A)) (y : P.obj (moduleSheaf R B)) :
    P.obj (moduleSheaf R N) :=
  P.map q (Functor.prodObjMk x y)

/-- A pairing of the underlying sheaves of sets is **bilinear on `P`-elements** when the map
`pairingObj` it induces is additive and compatible with scalars in each argument, for the module
structures that `P` transports from the sheaves of modules. -/
def IsBilinearPairingObj : Prop :=
  letI := Sheaf.ringObjRing R P
  letI := Sheaf.moduleObjAddCommGroup R A P
  letI := Sheaf.moduleObjAddCommGroup R B P
  letI := Sheaf.moduleObjAddCommGroup R N P
  letI := Sheaf.moduleObjModule R A P
  letI := Sheaf.moduleObjModule R B P
  letI := Sheaf.moduleObjModule R N P
  (∀ (x x' : P.obj (moduleSheaf R A)) (y : P.obj (moduleSheaf R B)),
      pairingObj R q P (x + x') y = pairingObj R q P x y + pairingObj R q P x' y) ∧
    (∀ (x : P.obj (moduleSheaf R A)) (y y' : P.obj (moduleSheaf R B)),
      pairingObj R q P x (y + y') = pairingObj R q P x y + pairingObj R q P x y') ∧
    (∀ (r : P.obj (Sheaf.ringSheaf R)) (x : P.obj (moduleSheaf R A))
        (y : P.obj (moduleSheaf R B)),
      pairingObj R q P (r • x) y = r • pairingObj R q P x y) ∧
    (∀ (r : P.obj (Sheaf.ringSheaf R)) (x : P.obj (moduleSheaf R A))
        (y : P.obj (moduleSheaf R B)),
      pairingObj R q P x (r • y) = r • pairingObj R q P x y)

/-- `IsBilinearPairingObj` spelled through the transported operations themselves, which is the
form the proofs below use. -/
lemma isBilinearPairingObj_iff :
    IsBilinearPairingObj R q P ↔
      (∀ (x x' : P.obj (moduleSheaf R A)) (y : P.obj (moduleSheaf R B)),
          pairingObj R q P (Sheaf.moduleAddObj R A P x x') y =
            Sheaf.moduleAddObj R N P (pairingObj R q P x y) (pairingObj R q P x' y)) ∧
        (∀ (x : P.obj (moduleSheaf R A)) (y y' : P.obj (moduleSheaf R B)),
            pairingObj R q P x (Sheaf.moduleAddObj R B P y y') =
              Sheaf.moduleAddObj R N P (pairingObj R q P x y) (pairingObj R q P x y')) ∧
          (∀ (r : P.obj (Sheaf.ringSheaf R)) (x : P.obj (moduleSheaf R A))
              (y : P.obj (moduleSheaf R B)),
              pairingObj R q P (Sheaf.moduleSMulObj R A P r x) y =
                Sheaf.moduleSMulObj R N P r (pairingObj R q P x y)) ∧
            (∀ (r : P.obj (Sheaf.ringSheaf R)) (x : P.obj (moduleSheaf R A))
                (y : P.obj (moduleSheaf R B)),
                pairingObj R q P x (Sheaf.moduleSMulObj R B P r y) =
                  Sheaf.moduleSMulObj R N P r (pairingObj R q P x y)) :=
  Iff.rfl

end Obj

/-! ### The forward direction -/

section Forward

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (R : Sheaf J RingCat.{w}) {A B N : SheafOfModules.{w} R}
  (q : moduleSheaf R A ⨯ moduleSheaf R B ⟶ moduleSheaf R N)
  (P : Sheaf J (Type w) ⥤ Type t) [PreservesFiniteProducts P]

/-- A bilinear pairing is bilinear on the elements of the image of any finite-product-preserving
functor to types, in particular on stalks. -/
lemma IsBilinearPairing.isBilinearPairingObj (h : IsBilinearPairing R q) :
    IsBilinearPairingObj R q P := by
  obtain ⟨hal, har, hsl, hsr⟩ := (isBilinearPairing_iff_squares R q).1 h
  unfold addLeftSquare at hal
  unfold addRightSquare at har
  unfold smulLeftSquare at hsl
  unfold smulRightSquare at hsr
  rw [isBilinearPairingObj_iff]
  refine ⟨fun x x' y ↦ ?_, fun x y y' ↦ ?_, fun r x y ↦ ?_, fun r x y ↦ ?_⟩
  on_goal 1 =>
    have := ConcreteCategory.congr_hom (congrArg P.map hal)
      (Functor.prodObjMk (Functor.prodObjMk x x') y)
  on_goal 2 =>
    have := ConcreteCategory.congr_hom (congrArg P.map har)
      (Functor.prodObjMk x (Functor.prodObjMk y y'))
  on_goal 3 =>
    have := ConcreteCategory.congr_hom (congrArg P.map hsl)
      (Functor.prodObjMk (Functor.prodObjMk r x) y)
  on_goal 4 =>
    have := ConcreteCategory.congr_hom (congrArg P.map hsr)
      (Functor.prodObjMk x (Functor.prodObjMk r y))
  all_goals
    simpa only [pairingObj, Sheaf.moduleAddObj, Sheaf.moduleSMulObj, Functor.map_comp_apply,
      Functor.map_prodMap_apply, Functor.map_lift_apply, Functor.map_fst_prodObjMk,
      Functor.map_snd_prodObjMk, CategoryTheory.Functor.map_id, types_id_apply] using this

end Forward

/-! ### The stalk criterion -/

section Criterion

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (R : Sheaf J RingCat.{w}) {A B N : SheafOfModules.{w} R}
  (q : moduleSheaf R A ⨯ moduleSheaf R B ⟶ moduleSheaf R N)

/-- **The stalk criterion over a site with enough points.** A pairing of the underlying sheaves
of sets which is bilinear on the stalk at every point of a conservative family is bilinear. -/
theorem isBilinearPairing_of_forall_sheafFiber
    {Pts : ObjectProperty (GrothendieckTopology.Point.{w} J)}
    (hPts : Pts.IsConservativeFamilyOfPoints)
    (h : ∀ Φ : Pts.FullSubcategory,
      IsBilinearPairingObj R q (Φ.obj.sheafFiber (A := Type w))) :
    IsBilinearPairing R q := by
  have hf := hPts.jointlyReflectIsomorphisms_type.jointlyFaithful
  rw [isBilinearPairing_iff_squares]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine hf.map_injective fun Φ ↦ ?_ <;>
    have H := (isBilinearPairingObj_iff R q _).1 (h Φ)
  on_goal 1 =>
    refine map_ext_prodProd _ fun x x' y ↦ ?_
    have := H.1 x x' y
  on_goal 2 =>
    refine map_ext_prodProd' _ fun x y y' ↦ ?_
    have := H.2.1 x y y'
  on_goal 3 =>
    refine map_ext_prodProd _ fun r x y ↦ ?_
    have := H.2.2.1 r x y
  on_goal 4 =>
    refine map_ext_prodProd' _ fun x r y ↦ ?_
    have := H.2.2.2 r x y
  all_goals
    simpa only [Functor.map_comp_apply, Functor.map_prodMap_apply, Functor.map_lift_apply,
      Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk, CategoryTheory.Functor.map_id,
      types_id_apply, pairingObj, Sheaf.moduleAddObj, Sheaf.moduleSMulObj] using this

/-- Over a site with a conservative family of points, bilinearity is exactly bilinearity on
every stalk. -/
theorem isBilinearPairing_iff_forall_sheafFiber
    {Pts : ObjectProperty (GrothendieckTopology.Point.{w} J)}
    (hPts : Pts.IsConservativeFamilyOfPoints) :
    IsBilinearPairing R q ↔ ∀ Φ : Pts.FullSubcategory,
      IsBilinearPairingObj R q (Φ.obj.sheafFiber (A := Type w)) :=
  ⟨fun h _ ↦ h.isBilinearPairingObj R q _,
    isBilinearPairing_of_forall_sheafFiber R q hPts⟩

end Criterion

/-! ### The stalk criterion on a topological space -/

section Space

variable {X : TopCat.{u}}
  [(Opens.grothendieckTopology X).HasSheafCompose (forget RingCat.{u})]
  [(Opens.grothendieckTopology X).HasSheafCompose (forget AddCommGrpCat.{u})]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) {A B N : SheafOfModules.{u} R}
  (q : moduleSheaf R A ⨯ moduleSheaf R B ⟶ moduleSheaf R N)

/-- The stalk at a point of a topological space, as a functor on sheaves of sets, in the shape
of the fibre functor at the point of the site of opens that `x` determines. -/
abbrev stalkTypeFunctor (x : X) :
    Sheaf (Opens.grothendieckTopology X) (Type u) ⥤ Type u :=
  (Opens.pointGrothendieckTopology x).sheafFiber (A := Type u)

/-- **The stalk characterisation of bilinearity.** A pairing of the underlying sheaves of sets
of three sheaves of modules on a topological space is bilinear if and only if the map it induces
on the stalks at a point is bilinear over the stalk of the sheaf of rings, at every point.

This is the third assertion of the section [Stacks, Tag 0GIG]. The forward direction is
`IsBilinearPairing.isBilinearPairingObj` and needs nothing of the space; the converse is
`isBilinearPairing_of_forall_sheafFiber` at the conservative family of points that a
topological space provides. -/
@[stacks 0GIG "the third characterisation of the section: a map of the underlying sheaves of sets
which induces a bilinear map of modules on the stalk at every point of `X` is bilinear, and
conversely. The stalk is taken in the shape the site gives it, the fibre functor at the point of
`Opens X` determined by `x`, which `Opens.pointFiberStalkFunctorIso` identifies with the ordinary
stalk; its module structure over the stalk of `O_X` is the one
`CategoryTheory.Sheaf.moduleObjModule` transports. Over a not necessarily commutative sheaf of
rings. The forward direction is proved for every finite-product-preserving functor to types, as
`IsBilinearPairing.isBilinearPairingObj`, and the converse over any site with a conservative
family of points, as `isBilinearPairing_iff_forall_sheafFiber`; the points of a topological space
are such a family, so this statement carries no hypothesis of its own beyond the standing binders
of the section"]
theorem isBilinearPairing_iff_stalk :
    IsBilinearPairing R q ↔ ∀ x : X, IsBilinearPairingObj R q (stalkTypeFunctor x) := by
  refine ⟨fun h x ↦ h.isBilinearPairingObj R q _, fun h ↦ ?_⟩
  refine isBilinearPairing_of_forall_sheafFiber R q
    (Opens.isConservativeFamilyOfPoints_pointsGrothendieckTopology X) ?_
  rintro ⟨-, ⟨x⟩⟩
  exact h x

end Space

end Stacks.SheafOfModules

end
