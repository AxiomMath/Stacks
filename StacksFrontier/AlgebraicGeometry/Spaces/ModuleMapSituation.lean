module

public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# The standing situation of a map of quasi-coherent modules, and its base-change loci

Fix a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` and a map `u : F ⟶ G` of
quasi-coherent `𝒪_X`-modules.  Every scheme `T` over `Y` gives a base change
`X ×_Y T ⟶ X` and hence a pulled-back map of modules `u_T`.  Stacks 083F collects this data
and records that the four conditions "`u_T` is an isomorphism", "`u_T` is universally
injective", "`u_T` is surjective" and "`u_T` is zero" are stable under further base change,
so that each of them is a subterminal presheaf on the category of schemes over `Y`.

## Main definitions

* `AlgebraicGeometry.Space.ModuleMapSituation` is the standing data of Stacks 083F.
* `AlgebraicGeometry.Space.ModulePullbackSystem` is the pullback of modules along an
  arbitrary morphism of algebraic spaces, as *data*: the functors, their composition
  comparisons, and the two exactness properties the base-change loci need.  See the
  implementation notes.
* `AlgebraicGeometry.Space.subterminalSchemesOverFunctor` is the subterminal presheaf on the
  test schemes over an algebraic space cut out by a base-change-stable property of them, the
  shape shared by the four loci here and by the flattening functor of Stacks 0CWX.
* `AlgebraicGeometry.Space.ModuleMapSituation.baseChangeHom` is the pulled-back map `u_T`.
* `AlgebraicGeometry.Space.ModuleMapSituation.isoFunctor`, `.injFunctor`, `.surjFunctor` and
  `.zeroFunctor` are the four subterminal functors on schemes over `Y`.

## Main results

* `AlgebraicGeometry.Space.ModuleMapSituation.isIsoAt_of_hom`,
  `.isUniversallyInjectiveAt_of_hom`, `.isSurjectiveAt_of_hom` and `.isZeroAt_of_hom`: each
  of the four conditions is stable under a morphism of schemes over `Y`.
* The `nonempty_*Functor_obj_iff` lemmas characterise the four functors at a test scheme;
  with the `*Functor_obj_subsingleton` instances each value is a singleton exactly when the
  corresponding condition holds and empty otherwise.

## Implementation notes

Schemes over `Y` are the costructured arrows from `AlgebraicGeometry.schemeSpaceFunctor`
(a scheme read as an algebraic space) to `Y`, and the base-change space is the fibre product
`AlgebraicGeometry.AlgebraicSpaces.fiberProduct` in the category of algebraic spaces.

The pullback of modules along a general morphism of algebraic spaces is the inverse image of
Stacks 03D6(2) for the small étale ringed sites, `AlgebraicGeometry.Space.modulePullback`, with
its adjunction `AlgebraicGeometry.Space.modulePullbackAdjunction`; Stacks 03G2 part (3)
supplies the morphism of small étale topoi at `Type u`.  Both are stated at the module universe
of the structure rings, which is where the loci below use them.

The systems below are nonetheless phrased abstractly: the projection `X ×_Y T ⟶ X` is not
étale, so the *étale* pullback `AlgebraicGeometry.Space.etaleModulePullback` does not apply to
it, and comparing `modulePullback` with `etaleModulePullback` is Equation 03LW, whose theorem
content is Stacks 03LV clause (2).

Everything downstream of the pulled-back map is therefore stated relative to a
`AlgebraicGeometry.Space.ModulePullbackSystem`, which packages exactly the properties the
four loci need: the functors, the composition comparisons `f^* ∘ g^* ≅ (g ∘ f)^*`,
preservation of zero morphisms and preservation of epimorphisms.  The last two are
consequences of `f^*` being a left adjoint, but the loci do not need the adjoint, so it is
not demanded.  A system in the module universe of the structure rings is what Stacks 03LU
displays; `AlgebraicGeometry.Space.modulePullback` and
`AlgebraicGeometry.Space.modulePushforward` are the two functors it displays.

The value of each functor is a subtype of the one-point type, hence a singleton exactly when
its condition holds.  Universal injectivity quantifies over every scheme over `Y` equipped
with a map to the given one, as in the source; the other three conditions concern only the
base change at the test scheme itself.

## References

* [Stacks Project, Tag 083F](https://stacks.math.columbia.edu/tag/083F)
* [Stacks Project, Tag 04U8](https://stacks.math.columbia.edu/tag/04U8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The standing situation -/

/-- **Stacks 083F.** The standing data of Stacks 083F: a morphism `f : X ⟶ Y` of algebraic
spaces over `S` and a map `u : F ⟶ G` of quasi-coherent `𝒪_X`-modules. -/
@[stacks 083F "standing data"]
structure ModuleMapSituation where
  /-- The source algebraic space, carrying the two modules. -/
  X : AlgebraicSpaces B S hS
  /-- The target algebraic space, over which the test schemes live. -/
  Y : AlgebraicSpaces B S hS
  /-- The morphism of algebraic spaces being base changed along. -/
  f : X ⟶ Y
  /-- The source module of the map. -/
  F : Modules.{u, m} B S hS X.1 X.2
  /-- The target module of the map. -/
  G : Modules.{u, m} B S hS X.1 X.2
  /-- The source module is quasi-coherent. -/
  quasicoherent_F : F.IsQuasicoherentOnSite
  /-- The target module is quasi-coherent. -/
  quasicoherent_G : G.IsQuasicoherentOnSite
  /-- The map of modules whose base-change loci are studied. -/
  u : F ⟶ G

namespace ModuleMapSituation

variable {B S hS}

/-- Test schemes equipped with a map to the target algebraic space. -/
abbrev SchemesOver (D : ModuleMapSituation.{u, m} B S hS) :=
  CostructuredArrow (schemeSpaceFunctor B S hS) D.Y

/-- The fibre product of the source algebraic space with a test scheme. -/
def baseChangeSpace (D : ModuleMapSituation.{u, m} B S hS) (T : D.SchemesOver) :
    AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS D.f T.hom

/-- The canonical projection from the fibre product to the source space. -/
def baseChangeProjection (D : ModuleMapSituation.{u, m} B S hS) (T : D.SchemesOver) :
    D.baseChangeSpace T ⟶ D.X :=
  ObjectProperty.homMk (pullback.fst D.f.hom T.hom.hom)

/-- The second projection from the fibre product, to the test scheme. -/
def baseChangeInclusion (D : ModuleMapSituation.{u, m} B S hS) (T : D.SchemesOver) :
    D.baseChangeSpace T ⟶ (schemeSpaceFunctor B S hS).obj T.left :=
  ObjectProperty.homMk (pullback.snd D.f.hom T.hom.hom)

/-- A morphism of test schemes induces a morphism of base-change spaces over the source
space. -/
def baseChangeMap (D : ModuleMapSituation.{u, m} B S hS) {T T' : D.SchemesOver} (g : T' ⟶ T) :
    D.baseChangeSpace T' ⟶ D.baseChangeSpace T :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom).lift
    (D.baseChangeProjection T')
    (D.baseChangeInclusion T' ≫ (schemeSpaceFunctor B S hS).map g.left)
    (by
      rw [Category.assoc, CostructuredArrow.w g]
      exact ObjectProperty.hom_ext _ pullback.condition)

/-- The induced map of base-change spaces commutes with the projections to the source space. -/
@[simp]
theorem baseChangeMap_comp_baseChangeProjection (D : ModuleMapSituation.{u, m} B S hS)
    {T T' : D.SchemesOver} (g : T' ⟶ T) :
    D.baseChangeMap g ≫ D.baseChangeProjection T = D.baseChangeProjection T' :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom).lift_fst _ _ _

end ModuleMapSituation

/-! ### Pullback of modules as data -/

/-- The pullback of sheaves of modules along an arbitrary morphism of algebraic spaces over
`S`, as *data*: a functor for every morphism, the comparison of a composite of pullbacks with
the pullback of the composite, and the two exactness properties that the base-change loci of
Stacks 083F consume.

Stacks 03LU asserts that such a system exists, as the left adjoint of the direct image of
`AlgebraicGeometry.Space.modulePushforwardOfStructureMap`.  Everything built on the pullback is
stated relative to a system supplied as a hypothesis; see the implementation notes of the file.
-/
structure ModulePullbackSystem where
  /-- The pullback functor of a morphism of algebraic spaces. -/
  functor {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    Modules.{u, m} B S hS Y.1 Y.2 ⥤ Modules.{u, m} B S hS X.1 X.2
  /-- The comparison of a composite of pullbacks with the pullback of the composite. -/
  compIso {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) :
    functor g ⋙ functor f ≅ functor (f ≫ g)
  /-- Pullback preserves zero morphisms.  A consequence of its being a left adjoint between
  preadditive categories, but the adjoint itself is never used. -/
  preservesZeroMorphisms {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (functor f).PreservesZeroMorphisms
  /-- Pullback preserves epimorphisms.  A consequence of its being a left adjoint, but the
  adjoint itself is never used. -/
  preservesEpimorphisms {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (functor f).PreservesEpimorphisms

namespace ModulePullbackSystem

variable {B S hS}

/-- The pullback of a map of modules along a composite, conjugated to the composite of the
pullbacks by the comparison isomorphism. -/
theorem map_comp_eq_conj (P : ModulePullbackSystem.{u, m} B S hS)
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M N : Modules.{u, m} B S hS Z.1 Z.2} (a : M ⟶ N) :
    (P.functor (f ≫ g)).map a =
      (P.compIso f g).inv.app M ≫
        (P.functor f).map ((P.functor g).map a) ≫ (P.compIso f g).hom.app N := by
  have h := (P.compIso f g).hom.naturality a
  simp only [Functor.comp_map] at h
  rw [h]
  simp

end ModulePullbackSystem

/-! ### Subterminal presheaves on the test schemes -/

/-- The subterminal presheaf on the test schemes over an algebraic space cut out by a property
of test schemes stable under base change: its value at `T` is a one-element type if the property
holds at `T` and is empty otherwise, and the restriction maps are forced.

The flattening functor of Stacks 0CWX
(`AlgebraicGeometry.Space.FlatnessSituation.flatFunctor`) and the four base-change loci of
Stacks 083F below are all of this form. -/
def subterminalSchemesOverFunctor (Y : AlgebraicSpaces B S hS)
    (Q : CostructuredArrow (schemeSpaceFunctor B S hS) Y → Prop)
    (stable : ∀ {T T' : CostructuredArrow (schemeSpaceFunctor B S hS) Y},
      (T' ⟶ T) → Q T → Q T') :
    (CostructuredArrow (schemeSpaceFunctor B S hS) Y)ᵒᵖ ⥤ Type u where
  obj T := {x : PUnit.{u + 1} // Q T.unop}
  map g := ↾fun x => ⟨x.1, stable g.unop x.2⟩
  map_id := by
    intro T
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    rfl
  map_comp := by
    intro T U V g k
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    rfl

/-- A value of a subterminal presheaf has at most one element: it is a subtype of a one-element
type. -/
instance subterminalSchemesOverFunctor_obj_subsingleton (Y : AlgebraicSpaces B S hS)
    (Q : CostructuredArrow (schemeSpaceFunctor B S hS) Y → Prop)
    (stable : ∀ {T T' : CostructuredArrow (schemeSpaceFunctor B S hS) Y},
      (T' ⟶ T) → Q T → Q T')
    (T : (CostructuredArrow (schemeSpaceFunctor B S hS) Y)ᵒᵖ) :
    Subsingleton ((subterminalSchemesOverFunctor B S hS Y Q stable).obj T) :=
  ⟨fun a b => Subtype.ext (Subsingleton.elim a.val b.val)⟩

/-- A value of a subterminal presheaf is nonempty exactly when its property holds, so it is a
one-element type there and empty elsewhere. -/
theorem nonempty_subterminalSchemesOverFunctor_obj_iff (Y : AlgebraicSpaces B S hS)
    (Q : CostructuredArrow (schemeSpaceFunctor B S hS) Y → Prop)
    (stable : ∀ {T T' : CostructuredArrow (schemeSpaceFunctor B S hS) Y},
      (T' ⟶ T) → Q T → Q T')
    (T : CostructuredArrow (schemeSpaceFunctor B S hS) Y) :
    Nonempty ((subterminalSchemesOverFunctor B S hS Y Q stable).obj (Opposite.op T)) ↔ Q T :=
  ⟨fun ⟨x⟩ => x.2, fun h => ⟨⟨PUnit.unit, h⟩⟩⟩

/-! ### The four base-change loci -/

namespace ModuleMapSituation

variable {B S hS} (D : ModuleMapSituation.{u, m} B S hS)
    (P : ModulePullbackSystem.{u, m} B S hS)

/-- The pullback of the map of modules to a test scheme. -/
def baseChangeHom (T : D.SchemesOver) :
    (P.functor (D.baseChangeProjection T)).obj D.F ⟶
      (P.functor (D.baseChangeProjection T)).obj D.G :=
  (P.functor (D.baseChangeProjection T)).map D.u

/-- The base-changed map is an isomorphism at this test scheme. -/
def IsIsoAt (T : D.SchemesOver) : Prop := IsIso (D.baseChangeHom P T)

/-- The base-changed map is injective after every further scheme base change. -/
def IsUniversallyInjectiveAt (T : D.SchemesOver) : Prop :=
  ∀ (T' : D.SchemesOver) (_g : T' ⟶ T), Mono (D.baseChangeHom P T')

/-- The base-changed map is surjective at this test scheme. -/
def IsSurjectiveAt (T : D.SchemesOver) : Prop := Epi (D.baseChangeHom P T)

/-- The base-changed map is zero at this test scheme. -/
def IsZeroAt (T : D.SchemesOver) : Prop := D.baseChangeHom P T = 0

/-- Isomorphism of the base-changed map persists under further scheme base change. -/
theorem isIsoAt_of_hom {T T' : D.SchemesOver} (g : T' ⟶ T) (h : D.IsIsoAt P T) :
    D.IsIsoAt P T' := by
  have : IsIso ((P.functor (D.baseChangeProjection T)).map D.u) := h
  change IsIso ((P.functor (D.baseChangeProjection T')).map D.u)
  rw [← D.baseChangeMap_comp_baseChangeProjection g,
    P.map_comp_eq_conj (D.baseChangeMap g) (D.baseChangeProjection T) D.u]
  infer_instance

/-- Universal injectivity persists under further scheme base change. -/
theorem isUniversallyInjectiveAt_of_hom {T T' : D.SchemesOver} (g : T' ⟶ T)
    (h : D.IsUniversallyInjectiveAt P T) : D.IsUniversallyInjectiveAt P T' :=
  fun T'' k => h T'' (k ≫ g)

/-- Surjectivity of the base-changed map persists under further scheme base change. -/
theorem isSurjectiveAt_of_hom {T T' : D.SchemesOver} (g : T' ⟶ T)
    (h : D.IsSurjectiveAt P T) : D.IsSurjectiveAt P T' := by
  have : Epi ((P.functor (D.baseChangeProjection T)).map D.u) := h
  have := P.preservesEpimorphisms (D.baseChangeMap g)
  change Epi ((P.functor (D.baseChangeProjection T')).map D.u)
  rw [← D.baseChangeMap_comp_baseChangeProjection g,
    P.map_comp_eq_conj (D.baseChangeMap g) (D.baseChangeProjection T) D.u]
  infer_instance

/-- Vanishing of the base-changed map persists under further scheme base change. -/
theorem isZeroAt_of_hom {T T' : D.SchemesOver} (g : T' ⟶ T)
    (h : D.IsZeroAt P T) : D.IsZeroAt P T' := by
  have := P.preservesZeroMorphisms (D.baseChangeMap g)
  have h' : (P.functor (D.baseChangeProjection T)).map D.u = 0 := h
  change (P.functor (D.baseChangeProjection T')).map D.u = 0
  rw [← D.baseChangeMap_comp_baseChangeProjection g,
    P.map_comp_eq_conj (D.baseChangeMap g) (D.baseChangeProjection T) D.u, h']
  simp

/-! ### The four subterminal functors -/

/-- The subterminal presheaf associated to a base-change-stable property of test schemes. -/
def subterminalFunctor (Q : D.SchemesOver → Prop)
    (stable : ∀ {T T' : D.SchemesOver}, (T' ⟶ T) → Q T → Q T') :
    (D.SchemesOver)ᵒᵖ ⥤ Type u :=
  subterminalSchemesOverFunctor B S hS D.Y Q stable

/-- The functor of scheme base changes on which the module map is an isomorphism. -/
def isoFunctor : (D.SchemesOver)ᵒᵖ ⥤ Type u :=
  D.subterminalFunctor (D.IsIsoAt P) (fun g h => D.isIsoAt_of_hom P g h)

/-- The functor of scheme base changes on which the map is universally injective. -/
def injFunctor : (D.SchemesOver)ᵒᵖ ⥤ Type u :=
  D.subterminalFunctor (D.IsUniversallyInjectiveAt P)
    (fun g h => D.isUniversallyInjectiveAt_of_hom P g h)

/-- The functor of scheme base changes on which the module map is surjective. -/
def surjFunctor : (D.SchemesOver)ᵒᵖ ⥤ Type u :=
  D.subterminalFunctor (D.IsSurjectiveAt P) (fun g h => D.isSurjectiveAt_of_hom P g h)

/-- The functor of scheme base changes on which the module map is zero. -/
def zeroFunctor : (D.SchemesOver)ᵒᵖ ⥤ Type u :=
  D.subterminalFunctor (D.IsZeroAt P) (fun g h => D.isZeroAt_of_hom P g h)

/-- The functor of isomorphism loci is nonempty at a test scheme exactly when the
base-changed map is an isomorphism there. -/
@[simp]
theorem nonempty_isoFunctor_obj_iff (T : D.SchemesOver) :
    Nonempty ((D.isoFunctor P).obj (Opposite.op T)) ↔ IsIso (D.baseChangeHom P T) :=
  ⟨fun ⟨x⟩ => x.2, fun h => ⟨⟨PUnit.unit, h⟩⟩⟩

/-- The functor of universal-injectivity loci is nonempty at a test scheme exactly when
the base-changed map is injective after every further scheme base change. -/
@[simp]
theorem nonempty_injFunctor_obj_iff (T : D.SchemesOver) :
    Nonempty ((D.injFunctor P).obj (Opposite.op T)) ↔
      (∀ (T' : D.SchemesOver) (_g : T' ⟶ T), Mono (D.baseChangeHom P T')) :=
  ⟨fun ⟨x⟩ => x.2, fun h => ⟨⟨PUnit.unit, h⟩⟩⟩

/-- The functor of surjectivity loci is nonempty at a test scheme exactly when the
base-changed map is surjective there. -/
@[simp]
theorem nonempty_surjFunctor_obj_iff (T : D.SchemesOver) :
    Nonempty ((D.surjFunctor P).obj (Opposite.op T)) ↔ Epi (D.baseChangeHom P T) :=
  ⟨fun ⟨x⟩ => x.2, fun h => ⟨⟨PUnit.unit, h⟩⟩⟩

/-- The functor of vanishing loci is nonempty at a test scheme exactly when the
base-changed map is zero there. -/
@[simp]
theorem nonempty_zeroFunctor_obj_iff (T : D.SchemesOver) :
    Nonempty ((D.zeroFunctor P).obj (Opposite.op T)) ↔ D.baseChangeHom P T = 0 :=
  ⟨fun ⟨x⟩ => x.2, fun h => ⟨⟨PUnit.unit, h⟩⟩⟩

/-- A value of the functor of isomorphism loci has at most one element. -/
instance isoFunctor_obj_subsingleton (T : D.SchemesOver) :
    Subsingleton ((D.isoFunctor P).obj (Opposite.op T)) :=
  ⟨fun a b => Subtype.ext (Subsingleton.elim a.val b.val)⟩

/-- A value of the functor of universal-injectivity loci has at most one element. -/
instance injFunctor_obj_subsingleton (T : D.SchemesOver) :
    Subsingleton ((D.injFunctor P).obj (Opposite.op T)) :=
  ⟨fun a b => Subtype.ext (Subsingleton.elim a.val b.val)⟩

/-- A value of the functor of surjectivity loci has at most one element. -/
instance surjFunctor_obj_subsingleton (T : D.SchemesOver) :
    Subsingleton ((D.surjFunctor P).obj (Opposite.op T)) :=
  ⟨fun a b => Subtype.ext (Subsingleton.elim a.val b.val)⟩

/-- A value of the functor of vanishing loci has at most one element. -/
instance zeroFunctor_obj_subsingleton (T : D.SchemesOver) :
    Subsingleton ((D.zeroFunctor P).obj (Opposite.op T)) :=
  ⟨fun a b => Subtype.ext (Subsingleton.elim a.val b.val)⟩

end ModuleMapSituation

end AlgebraicGeometry.Space

end
