module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource

/-!
# The Hilbert functor of an algebraic space over a base (Stacks 0CZY)

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site. For a
scheme `T` of the site over `Y` write `X_T = X ×_Y T`. The *Hilbert functor* of `X/Y` sends `T` to
the set of closed subspaces `Z ⊆ X_T` which are of finite presentation, flat and proper over `T`.
This is a functor on the opposite of the category of schemes over `Y`, because each of the three
properties is stable under base change and a closed subspace pulls back to a closed subspace.

The same data, read over the schemes of the site rather than over the schemes of `Y`, is a presheaf
`Hilb` on the site together with a canonical morphism `Hilb ⟶ Y`, whose fibre over a point of `Y`
is the value of the Hilbert functor there.

## Main definitions

* `AlgebraicGeometry.Space.SchemesOverPresheaf` is the category of schemes of the site carrying
  a morphism to the functor of points of an algebraic space, and
  `AlgebraicGeometry.Space.schemeBaseChange` the base change of `X` to such a scheme.
* `AlgebraicGeometry.Space.HilbertFamily`: **Stacks 0CZY**, the families the functor classifies.
* `AlgebraicGeometry.Space.hilbertFunctor`: **Stacks 0CZY**, the Hilbert functor itself.
* `AlgebraicGeometry.Space.HilbertFamilyOver`: **Stacks 0CZY**, a family together with the morphism
  to `Y` it lies over.
* `AlgebraicGeometry.Space.hilbertPresheaf`: **Stacks 0CZY**, the Hilbert functor read as a
  presheaf on the schemes of the site, and `AlgebraicGeometry.Space.hilbertPresheafToBase` its
  canonical morphism to `Y`.
* `AlgebraicGeometry.Space.HilbertPresheafModel` records a model of that presheaf in the universe
  of the site.

## Main results

* `AlgebraicGeometry.Space.isPullback_schemeBaseChangeMap`: the base changes of `X` to two schemes
  over `Y` form a cartesian square.
* `AlgebraicGeometry.Space.hilbertFunctor_map_obj`: the Hilbert functor acts by inverse image of
  closed subspaces.
* `AlgebraicGeometry.Space.HilbertPresheafModel.relative_mapFrom`: a property of morphisms tested
  on represented fibre products holds for the corresponding morphism into any model.

## Implementation notes

An algebraic space is a presheaf on the schemes of the site over `S` satisfying the conditions of
Stacks 025Y, bundled as an object of `AlgebraicGeometry.AlgebraicSpaces` of Stacks 02X2; a scheme
over the algebraic space `Y` is therefore an object of `CategoryTheory.CostructuredArrow` for the
Yoneda embedding, and the base change of `X` is a fibre product of presheaves.

The source makes the standing assumption that `f` is of finite presentation. The functor and all
of its properties below hold for an arbitrary morphism of algebraic spaces, so the hypothesis is
not imposed.

A closed subspace of `X_T` is a `CategoryTheory.Subfunctor` of the fibre product satisfying
Stacks 02YU, and its base change along a transition map is the inverse image
`CategoryTheory.Subfunctor.preimage` of Stacks 083Q. Taking the inverse image pointwise rather
than as a chosen fibre product is what makes the functoriality of the Hilbert functor hold *on the
nose* — `Subfunctor.preimage_id` and `Subfunctor.preimage_comp` are equalities, not isomorphisms —
so `AlgebraicGeometry.Space.hilbertFunctor` can be the honest functor whose value at `T` is
definitionally the type of families, rather than a functor only characterized up to a bijection.

Subfunctors of a presheaf on the site live one universe up, so the Hilbert functor takes values in
`Type (u + 1)` while an algebraic space takes values in `Type u`. The canonical morphism to `Y`
therefore targets the universe lift of `Y`, and representability statements about the Hilbert
functor are made about a model of it in `Type u`, an
`AlgebraicGeometry.Space.HilbertPresheafModel`. One exists for every morphism, because the big
fppf site is essentially small (`AlgebraicGeometry.Space.HilbertPresheafModel.canonical`).

## References

* [Stacks Project, Tag 0CZY](https://stacks.math.columbia.edu/tag/0CZY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The schemes of the big fppf site over an algebraic space `Y`: an object is a scheme of the site
together with a morphism of presheaves from it to `Y`.

The comparison is with the *functor of points* of `Y`, which is what distinguishes this from
`AlgebraicGeometry.Space.SchemesOver`, whose objects carry a morphism of algebraic spaces into
`Y` itself. -/
abbrev SchemesOverPresheaf (Y : AlgebraicSpaces B S hS) :=
  CostructuredArrow (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) Y.obj

variable {B S hS} {X Y : AlgebraicSpaces B S hS}

/-- The base change `X_T = X ×_Y T` of the source of `f : X ⟶ Y` to a scheme `T` over `Y`. -/
abbrev schemeBaseChange (f : X ⟶ Y) (T : SchemesOverPresheaf B S hS Y) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback f.hom T.hom

/-- The base change `X_T` is an algebraic space. -/
theorem isAlgebraicSpace_schemeBaseChange (f : X ⟶ Y) (T : SchemesOverPresheaf B S hS Y) :
    IsAlgebraicSpace B S hS (schemeBaseChange f T) :=
  isAlgebraicSpace_pullback B S hS f.hom T.hom X.property
    (isAlgebraicSpace_yoneda B S hS T.left) Y.property

/-- The base change `X_T`, as an object of the category of algebraic spaces over `S`. -/
abbrev schemeBaseChangeSpace (f : X ⟶ Y) (T : SchemesOverPresheaf B S hS Y) :
    AlgebraicSpaces B S hS :=
  ⟨schemeBaseChange f T, isAlgebraicSpace_schemeBaseChange f T⟩

/-- A scheme over `Y`, as an object of the category of algebraic spaces over `S`. -/
abbrev schemeOverSpace (T : SchemesOverPresheaf B S hS Y) : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj T.left, isAlgebraicSpace_yoneda B S hS T.left⟩

/-- The transition morphism `X_{T'} ⟶ X_T` of base changes induced by a morphism `T' ⟶ T` of
schemes over `Y`. -/
def schemeBaseChangeMap (f : X ⟶ Y) {T T' : SchemesOverPresheaf B S hS Y} (g : T' ⟶ T) :
    schemeBaseChange f T' ⟶ schemeBaseChange f T :=
  pullback.lift (pullback.fst f.hom T'.hom) (pullback.snd f.hom T'.hom ≫ yoneda.map g.left) (by
    rw [Category.assoc, g.w]
    exact pullback.condition)

/-- The transition morphism of base changes commutes with the first projections to `X`. -/
@[simp]
theorem schemeBaseChangeMap_fst (f : X ⟶ Y) {T T' : SchemesOverPresheaf B S hS Y} (g : T' ⟶ T) :
    schemeBaseChangeMap f g ≫ pullback.fst f.hom T.hom = pullback.fst f.hom T'.hom := by
  rw [schemeBaseChangeMap, pullback.lift_fst]

/-- The transition morphism of base changes commutes with the second projections, through the
morphism of test schemes. -/
@[simp]
theorem schemeBaseChangeMap_snd (f : X ⟶ Y) {T T' : SchemesOverPresheaf B S hS Y} (g : T' ⟶ T) :
    schemeBaseChangeMap f g ≫ pullback.snd f.hom T.hom =
      pullback.snd f.hom T'.hom ≫ yoneda.map g.left := by
  rw [schemeBaseChangeMap, pullback.lift_snd]

/-- The transition morphism of base changes along the identity is the identity. -/
@[simp]
theorem schemeBaseChangeMap_id (f : X ⟶ Y) (T : SchemesOverPresheaf B S hS Y) :
    schemeBaseChangeMap f (𝟙 T) = 𝟙 (schemeBaseChange f T) := by
  apply pullback.hom_ext <;> simp

/-- The transition morphisms of base changes compose. -/
theorem schemeBaseChangeMap_comp (f : X ⟶ Y) {T T' T'' : SchemesOverPresheaf B S hS Y} (g : T' ⟶ T)
    (h : T'' ⟶ T') :
    schemeBaseChangeMap f (h ≫ g) = schemeBaseChangeMap f h ≫ schemeBaseChangeMap f g := by
  apply pullback.hom_ext
  · simp
  · simp only [Category.assoc, schemeBaseChangeMap_snd, CostructuredArrow.comp_left,
      Functor.map_comp]
    exact congrArg (fun k => k ≫ yoneda.map g.left) (schemeBaseChangeMap_snd f h).symm

/-- The square comparing the base changes of `X` to two schemes over `Y` is cartesian: `X_{T'}` is
the base change of `X_T` along `T' ⟶ T`. -/
theorem isPullback_schemeBaseChangeMap (f : X ⟶ Y) {T T' : SchemesOverPresheaf B S hS Y}
    (g : T' ⟶ T) :
    IsPullback (schemeBaseChangeMap f g) (pullback.snd f.hom T'.hom) (pullback.snd f.hom T.hom)
      (yoneda.map g.left) := by
  have hleft : IsPullback (pullback.fst f.hom T'.hom) (pullback.snd f.hom T'.hom) f.hom
      (yoneda.map g.left ≫ T.hom) := by
    simpa [g.w] using IsPullback.of_hasPullback f.hom T'.hom
  have hright := IsPullback.of_hasPullback f.hom T.hom
  have hpaste := IsPullback.of_right' hleft hright
  convert hpaste using 1
  apply pullback.hom_ext
  · simp only [schemeBaseChangeMap, pullback.lift_fst, hright.lift_fst]
  · simp only [schemeBaseChangeMap, pullback.lift_snd, hright.lift_snd]

/-- A cartesian square of algebraic spaces, seen as presheaves, is a cartesian square of algebraic
spaces. -/
private theorem isPullback_homMk {A A' C C' : AlgebraicSpaces B S hS} {a : A.obj ⟶ A'.obj}
    {b : A.obj ⟶ C.obj} {c : A'.obj ⟶ C'.obj} {d : C.obj ⟶ C'.obj} (H : IsPullback a b c d) :
    IsPullback (ObjectProperty.homMk a : A ⟶ A') (ObjectProperty.homMk b)
      (ObjectProperty.homMk c) (ObjectProperty.homMk d) :=
  IsPullback.of_map_of_faithful
    (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)) H

/-- **Stacks 0CZY.** A family classified by the Hilbert functor of `f : X ⟶ Y` over a scheme `T`
over `Y`: a closed subspace of the base change `X_T` which is of finite presentation, flat and
proper over `T`. -/
@[stacks 0CZY "families classified by the functor"]
structure HilbertFamily (f : X ⟶ Y) (T : SchemesOverPresheaf B S hS Y) where
  /-- The closed subspace of `X_T`. -/
  Z : Subfunctor (schemeBaseChange f T)
  /-- It is a closed subspace (Stacks 02YU). -/
  closed : IsClosedSubspace B S hS Z
  /-- It is of finite presentation over `T` (Stacks 03XP). -/
  finitePresentation : IsFinitePresentation B S hS (Z.ι ≫ pullback.snd f.hom T.hom)
  /-- It is flat over `T` (Stacks 03ML). -/
  flat : IsFlat B S hS (Z.ι ≫ pullback.snd f.hom T.hom)
  /-- It is proper over `T` (Stacks 03ZM). -/
  proper : IsProper B S hS (Z.ι ≫ pullback.snd f.hom T.hom)

namespace HilbertFamily

variable {f : X ⟶ Y}

/-- The closed subspace of a family, as an object of the category of algebraic spaces over `S`. -/
abbrev space {T : SchemesOverPresheaf B S hS Y} (z : HilbertFamily f T) : AlgebraicSpaces B S hS :=
  ⟨z.Z.toFunctor, z.closed.1⟩

/-- Two families over the same scheme over `Y` agree as soon as their closed subspaces agree: the
remaining four fields are propositions. -/
@[ext]
theorem ext {T : SchemesOverPresheaf B S hS Y} {a b : HilbertFamily f T} (h : a.Z = b.Z) :
    a = b := by
  obtain ⟨aZ, ac, afp, afl, apr⟩ := a
  obtain ⟨bZ, bc, bfp, bfl, bpr⟩ := b
  cases h
  rfl

/-- The inverse image of the closed subspace of a family along a transition map of base changes is
again a closed subspace. -/
theorem isClosedSubspace_preimage_Z {T T' : SchemesOverPresheaf B S hS Y} (g : T' ⟶ T)
    (z : HilbertFamily f T) :
    IsClosedSubspace B S hS (z.Z.preimage (schemeBaseChangeMap f g)) :=
  Space.isClosedSubspace_preimage B S hS (schemeBaseChangeMap f g) z.Z
    (isAlgebraicSpace_schemeBaseChange f T) (isAlgebraicSpace_schemeBaseChange f T') z.closed

/-- The square exhibiting the inverse image of the closed subspace of a family as its base change
along a transition map, as a square of algebraic spaces over the two test schemes. -/
theorem isPullback_preimage_Z {T T' : SchemesOverPresheaf B S hS Y} (g : T' ⟶ T)
    (z : HilbertFamily f T) :
    IsPullback
      (ObjectProperty.homMk (z.Z.fromPreimage (schemeBaseChangeMap f g)) :
        (⟨(z.Z.preimage (schemeBaseChangeMap f g)).toFunctor,
          (z.isClosedSubspace_preimage_Z g).1⟩ : AlgebraicSpaces B S hS) ⟶ z.space)
      ((ObjectProperty.homMk (z.Z.preimage (schemeBaseChangeMap f g)).ι :
        (⟨(z.Z.preimage (schemeBaseChangeMap f g)).toFunctor,
          (z.isClosedSubspace_preimage_Z g).1⟩ : AlgebraicSpaces B S hS) ⟶
            schemeBaseChangeSpace f T') ≫
        ObjectProperty.homMk (pullback.snd f.hom T'.hom))
      ((ObjectProperty.homMk z.Z.ι : z.space ⟶ schemeBaseChangeSpace f T) ≫
        ObjectProperty.homMk (pullback.snd f.hom T.hom))
      (ObjectProperty.homMk (yoneda.map g.left) :
        schemeOverSpace T' ⟶ schemeOverSpace T) := by
  exact (isPullback_homMk (Subfunctor.isPullback_preimage (schemeBaseChangeMap f g) z.Z)).paste_vert
    (isPullback_homMk (isPullback_schemeBaseChangeMap f g))

/-- The base change of a family along a morphism of schemes over `Y`: the inverse image of its
closed subspace, which is again of finite presentation, flat and proper over the new test scheme
because all three properties are stable under base change (Stacks 03XR, 03MO, 04WP). -/
def baseChange {T T' : SchemesOverPresheaf B S hS Y} (g : T' ⟶ T) (z : HilbertFamily f T) :
    HilbertFamily f T' := by
  have hpb := z.isPullback_preimage_Z g
  have := Space.isFinitePresentation_isStableUnderBaseChange B S hS
  have := Space.isFlat_isStableUnderBaseChange B S hS
  have := Space.isProper_isStableUnderBaseChange B S hS
  refine ⟨z.Z.preimage (schemeBaseChangeMap f g), z.isClosedSubspace_preimage_Z g, ?_, ?_, ?_⟩
  · simpa using MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {F G : AlgebraicSpaces B S hS} (k : F ⟶ G) => IsFinitePresentation B S hS k.hom)
      hpb (by simpa using z.finitePresentation)
  · simpa using MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {F G : AlgebraicSpaces B S hS} (k : F ⟶ G) => IsFlat B S hS k.hom)
      hpb (by simpa using z.flat)
  · simpa using MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {F G : AlgebraicSpaces B S hS} (k : F ⟶ G) => IsProper B S hS k.hom)
      hpb (by simpa using z.proper)

/-- Base change of a family along a transition map takes the inverse image of its closed
subspace. -/
@[simp]
theorem baseChange_Z {T T' : SchemesOverPresheaf B S hS Y} (g : T' ⟶ T) (z : HilbertFamily f T) :
    (z.baseChange g).Z = z.Z.preimage (schemeBaseChangeMap f g) := rfl

/-- Base change of a family along the identity is the family itself. -/
theorem baseChange_id (T : SchemesOverPresheaf B S hS Y) (z : HilbertFamily f T) :
    z.baseChange (𝟙 T) = z := by
  cases z
  simp [baseChange, Subfunctor.preimage_id]

/-- Base change of a family along a composite is the iterated base change. -/
theorem baseChange_comp {T T' T'' : SchemesOverPresheaf B S hS Y} (g : T' ⟶ T) (h : T'' ⟶ T')
    (z : HilbertFamily f T) :
    (z.baseChange g).baseChange h = z.baseChange (h ≫ g) := by
  cases z
  simp [baseChange, Subfunctor.preimage_comp, schemeBaseChangeMap_comp]

end HilbertFamily

/-- **Stacks 0CZY.** The *Hilbert functor* of `f : X ⟶ Y`: it sends a scheme `T` over `Y` to the
set of closed subspaces of `X_T` which are of finite presentation, flat and proper over `T`, and a
morphism of schemes over `Y` to base change of those subspaces. -/
@[stacks 0CZY "the Hilbert functor"]
def hilbertFunctor (f : X ⟶ Y) : (SchemesOverPresheaf B S hS Y)ᵒᵖ ⥤ Type (u + 1) where
  obj T := HilbertFamily f T.unop
  map g := TypeCat.ofHom fun z => z.baseChange g.unop
  map_id T := ConcreteCategory.hom_ext _ _ fun z => z.baseChange_id T.unop
  map_comp g h := ConcreteCategory.hom_ext _ _ fun z => (z.baseChange_comp g.unop h.unop).symm

/-- The value of the Hilbert functor at a scheme over `Y` is the type of families there. -/
theorem hilbertFunctor_obj (f : X ⟶ Y) (T : SchemesOverPresheaf B S hS Y) :
    (hilbertFunctor f).obj (Opposite.op T) = HilbertFamily f T := rfl

/-- **Stacks 0CZY.** The Hilbert functor acts by inverse image of closed subspaces along the
transition maps of base changes. -/
@[stacks 0CZY "base change in the Hilbert functor"]
theorem hilbertFunctor_map_obj (f : X ⟶ Y) {T T' : SchemesOverPresheaf B S hS Y} (g : T' ⟶ T)
    (z : HilbertFamily f T) :
    ((hilbertFunctor f).map g.op z).Z = z.Z.preimage (schemeBaseChangeMap f g) := rfl

/-- **Stacks 0CZY.** A family classified by the Hilbert functor, over a scheme of the big fppf site
rather than over a scheme of `Y`: the morphism to `Y` it lies over, together with a family over the
resulting scheme over `Y`. -/
@[stacks 0CZY "families over the schemes of the site"]
structure HilbertFamilyOver (f : X ⟶ Y) (T : BigFppfOver B S hS) where
  /-- The morphism to `Y` the family lies over. -/
  toBase : yoneda.obj T ⟶ Y.obj
  /-- The family over the resulting scheme over `Y`. -/
  family : HilbertFamily f (CostructuredArrow.mk toBase)

namespace HilbertFamilyOver

variable {f : X ⟶ Y}

/-- Two families over a scheme of the site agree as soon as the morphisms to `Y` they lie over
agree and their closed subspaces agree over that. The subspace is typed through the morphism to
`Y`, so its equality is heterogeneous. -/
theorem ext {T : BigFppfOver B S hS} {a b : HilbertFamilyOver f T} (hbase : a.toBase = b.toBase)
    (hZ : a.family.Z ≍ b.family.Z) : a = b := by
  obtain ⟨ab, af⟩ := a
  obtain ⟨bb, bf⟩ := b
  subst hbase
  exact congrArg (HilbertFamilyOver.mk ab) (HilbertFamily.ext (eq_of_heq hZ))

/-- Equal families over a scheme of the site have the same closed subspace, heterogeneously. -/
theorem family_Z_heq {T : BigFppfOver B S hS} {a b : HilbertFamilyOver f T} (h : a = b) :
    a.family.Z ≍ b.family.Z := by
  cases h
  rfl

/-- The morphism of schemes over `Y` induced by a morphism of schemes of the site and a morphism
from the target to `Y`. -/
def restrict {T T' : BigFppfOver B S hS} (g : T' ⟶ T) (h : yoneda.obj T ⟶ Y.obj) :
    (CostructuredArrow.mk (yoneda.map g ≫ h) : SchemesOverPresheaf B S hS Y) ⟶
      CostructuredArrow.mk h :=
  CostructuredArrow.homMk g rfl

/-- The morphism of schemes over `Y` induced by the identity is the identity. -/
theorem restrict_id (T : BigFppfOver B S hS) (h : yoneda.obj T ⟶ Y.obj) :
    restrict (𝟙 T) h = 𝟙 (CostructuredArrow.mk h) := by
  apply CostructuredArrow.hom_ext
  rfl

/-- The morphisms of schemes over `Y` induced by morphisms of schemes of the site compose. -/
theorem restrict_comp {T T' T'' : BigFppfOver B S hS} (g : T' ⟶ T) (h : T'' ⟶ T')
    (k : yoneda.obj T ⟶ Y.obj) :
    restrict h (yoneda.map g ≫ k) ≫ restrict g k = restrict (h ≫ g) k := by
  apply CostructuredArrow.hom_ext
  simp [restrict]

/-- Base change of a family over a scheme of the site along a morphism of schemes of the site. -/
def baseChange {T T' : BigFppfOver B S hS} (g : T' ⟶ T) (x : HilbertFamilyOver f T) :
    HilbertFamilyOver f T' :=
  ⟨yoneda.map g ≫ x.toBase, x.family.baseChange (restrict g x.toBase)⟩

/-- Base change of a family over a scheme of the site along the identity is the family itself. -/
theorem baseChange_id (T : BigFppfOver B S hS) (x : HilbertFamilyOver f T) :
    x.baseChange (𝟙 T) = x := by
  obtain ⟨h, family⟩ := x
  simp only [baseChange]
  have hbase : yoneda.map (𝟙 T) ≫ h = h := by simp
  cases hbase
  rw [restrict_id]
  exact congrArg (HilbertFamilyOver.mk h) (family.baseChange_id (CostructuredArrow.mk h))

/-- Base change of a family over a scheme of the site along a composite is the iterated base
change. -/
theorem baseChange_comp {T T' T'' : BigFppfOver B S hS} (g : T' ⟶ T) (h : T'' ⟶ T')
    (x : HilbertFamilyOver f T) :
    (x.baseChange g).baseChange h = x.baseChange (h ≫ g) := by
  obtain ⟨k, family⟩ := x
  simp only [baseChange]
  have hbase : yoneda.map h ≫ yoneda.map g ≫ k = yoneda.map (h ≫ g) ≫ k := by
    simp [Category.assoc]
  cases hbase
  refine congrArg (HilbertFamilyOver.mk _) ?_
  exact (family.baseChange_comp (restrict g k) (restrict h (yoneda.map g ≫ k))).trans
    (congrArg (fun q => family.baseChange q) (restrict_comp g h k))

end HilbertFamilyOver

/-- **Stacks 0CZY.** The Hilbert functor read as a presheaf on the schemes of the big fppf site: a
section over `T` is a morphism `T ⟶ Y` together with a family over `T` for the resulting scheme
over `Y`, and restriction pulls back both. -/
@[stacks 0CZY "the presheaf on the schemes of the site"]
def hilbertPresheaf (f : X ⟶ Y) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) where
  obj T := HilbertFamilyOver f T.unop
  map g := TypeCat.ofHom fun x => x.baseChange g.unop
  map_id T := ConcreteCategory.hom_ext _ _ fun x => x.baseChange_id T.unop
  map_comp g h := ConcreteCategory.hom_ext _ _ fun x => (x.baseChange_comp g.unop h.unop).symm

/-- **Stacks 0CZY.** The canonical morphism from the Hilbert presheaf to the base algebraic space
`Y`, sending a family to the morphism to `Y` it lies over. Its target is the universe lift of `Y`
because subfunctors of a presheaf on the site live one universe up. -/
@[stacks 0CZY "the canonical morphism to the base"]
def hilbertPresheafToBase (f : X ⟶ Y) : hilbertPresheaf f ⟶ Y.obj ⋙ uliftFunctor.{u + 1, u} where
  app T := TypeCat.ofHom fun x => ULift.up (yonedaEquiv x.toBase)
  naturality := by
    intro T T' g
    ext x
    exact congrArg ULift.up (yonedaEquiv_naturality x.toBase g.unop).symm

/-- The canonical morphism to the base takes a section of the Hilbert presheaf to the point of `Y`
corresponding to the morphism it lies over. -/
@[simp]
theorem hilbertPresheafToBase_app_apply (f : X ⟶ Y) (T : (BigFppfOver B S hS)ᵒᵖ)
    (x : (hilbertPresheaf f).obj T) :
    ((hilbertPresheafToBase f).app T x).down = yonedaEquiv x.toBase := rfl

/-- A model of the Hilbert presheaf of `f` in the universe of the big fppf site: a presheaf of
`Type u` whose universe lift is isomorphic to the Hilbert presheaf. -/
structure HilbertPresheafModel (f : X ⟶ Y) where
  /-- The small presheaf. -/
  presheaf : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- Its universe lift is the Hilbert presheaf. -/
  iso : presheaf ⋙ uliftFunctor.{u + 1, u} ≅ hilbertPresheaf f

namespace HilbertPresheafModel

variable {f : X ⟶ Y} (M : HilbertPresheafModel f)

/-- The canonical morphism from a model of the Hilbert presheaf to the base algebraic space. -/
def toBase : M.presheaf ⟶ Y.obj where
  app T := ↾fun z ↦ ((hilbertPresheafToBase f).app T (M.iso.hom.app T ⟨z⟩)).down
  naturality {T T'} g := by
    ext z
    have h := types_congr_hom ((M.iso.hom ≫ hilbertPresheafToBase f).naturality g)
      (ULift.up.{u + 1} z)
    exact congrArg ULift.down h

/-- Transport a morphism into the Hilbert presheaf from a universe-lifted small presheaf into a
model of the Hilbert presheaf. -/
def mapFrom {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : F ⋙ uliftFunctor.{u + 1, u} ⟶ hilbertPresheaf f) : F ⟶ M.presheaf where
  app T := ↾fun z ↦ (M.iso.inv.app T (p.app T ⟨z⟩)).down
  naturality {T T'} g := by
    ext z
    have h := types_congr_hom ((p ≫ M.iso.inv).naturality g) (ULift.up.{u + 1} z)
    exact congrArg ULift.down h

/-- Transporting a morphism into a model of the Hilbert presheaf does not change the induced
morphism to the base algebraic space. -/
theorem toBase_mapFrom_app_apply {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : F ⋙ uliftFunctor.{u + 1, u} ⟶ hilbertPresheaf f) (T : (BigFppfOver B S hS)ᵒᵖ)
    (z : F.obj T) :
    M.toBase.app T ((M.mapFrom p).app T z) =
      ((hilbertPresheafToBase f).app T (p.app T ⟨z⟩)).down := by
  show ((hilbertPresheafToBase f).app T
    (M.iso.hom.app T (M.iso.inv.app T (p.app T ⟨z⟩)))).down = _
  exact congrArg (fun w ↦ ((hilbertPresheafToBase f).app T w).down)
    (types_congr_hom (M.iso.inv_hom_id_app T) (p.app T ⟨z⟩))

/-- A property of morphisms of schemes of the site which holds for the represented fibre products
of a morphism into the universe-lifted Hilbert presheaf also holds for its transport into a
model. -/
theorem relative_mapFrom (P : MorphismProperty (BigFppfOver B S hS))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : F ⋙ uliftFunctor.{u + 1, u} ⟶ hilbertPresheaf f)
    (hp : P.relative (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj uliftFunctor.{u + 1, u}) p) :
    P.presheaf (M.mapFrom p) := by
  let L := (Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
    uliftFunctor.{u + 1, u}
  have hmap : L.map (M.mapFrom p) = p ≫ M.iso.inv := by
    ext T z
    cases z
    rfl
  have hp' : P.relative (yoneda ⋙ L) (L.map (M.mapFrom p)) := by
    rw [hmap]
    exact MorphismProperty.RespectsIso.postcomp _ M.iso.inv p hp
  constructor
  · intro a g
    obtain ⟨b, s, t, ht⟩ := hp'.1 (L.map g)
    have ht' : IsPullback (L.map (L.preimage t)) (L.map (yoneda.map s))
        (L.map (M.mapFrom p)) (L.map g) := by
      simpa using ht
    exact ⟨b, s, L.preimage t, ht'.of_map_of_faithful L⟩
  · intro a b g t s ht
    exact hp'.2 (L.map g) (L.map t) s (ht.map L)

end HilbertPresheafModel

end AlgebraicGeometry.Space

end
