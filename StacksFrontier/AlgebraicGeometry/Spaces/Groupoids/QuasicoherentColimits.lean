module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCoherator

/-!
# Colimits of quasi-coherent modules on a groupoid in algebraic spaces

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `A`.  A colimit
of quasi-coherent modules on it is computed on the underlying `𝒪_U`-modules: the colimit of the
underlying modules carries a unique transition morphism `α : t^*ℱ ⟶ s^*ℱ` compatible with the
transitions of the diagram, that transition satisfies the cocycle and unit conditions, and the
resulting cocone is a colimit.  This is Stacks 077X.

The transport and naturality calculus for the transition morphisms that the construction is
assembled from is supplied here as well.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackEqToHom` is the transport of the inverse image of
  modules along an equality of the two morphisms it is taken along, at the level of functors.
* `AlgebraicGeometry.Space.QuasicoherentModule.colimitTransition` is the transition morphism on
  a colimit of the underlying modules of a diagram of quasi-coherent modules on the groupoid.
* `AlgebraicGeometry.Space.QuasicoherentModule.colimitModule` is that colimit with its
  transition morphism, as a quasi-coherent module on the groupoid, and
  `AlgebraicGeometry.Space.QuasicoherentModule.liftedColimitCocone` is the cocone over it.

## Main results

* `AlgebraicGeometry.Space.modulePullback_isLeftAdjoint`: the inverse image of modules along a
  morphism of algebraic spaces is a left adjoint, by the adjunction of Stacks 03LU, and so
  preserves all colimits.
* `CategoryTheory.comp_naturality₂` and `CategoryTheory.comp_naturality₃`: two, respectively
  three, commuting squares in a row paste into one, with the composites of the conclusion
  written in the brackets a goal normalized by `CategoryTheory.Category.assoc` has.
* `AlgebraicGeometry.Space.pullbackTransport_eq_modulePullbackEqToHom_app`: the canonical
  identification of the inverse images of a module along two equal morphisms is the
  functor-level transport, evaluated at that module.
* `AlgebraicGeometry.Space.pasteTransportFirstArrow` and
  `AlgebraicGeometry.Space.pasteTransportSecondArrow`: the transport along an endpoint equation
  of the composition diagram followed by the reindexing along a projection of the space of
  composable pairs is natural in the module.
* `AlgebraicGeometry.Space.QuasicoherentModule.colimitTransition_ι` is the defining property of
  the transition morphism on a colimit.
* `AlgebraicGeometry.Space.QuasicoherentModule.colimitTransition_cocycle` and
  `AlgebraicGeometry.Space.QuasicoherentModule.colimitTransition_unit`: the transition morphism
  on a colimit satisfies the cocycle condition and the unit condition.
* `AlgebraicGeometry.Space.QuasicoherentModule.liftedColimitCoconeIsColimit`: the lifted cocone
  is a colimit, so a diagram of quasi-coherent modules on the groupoid whose underlying diagram
  has a quasi-coherent colimit has a colimit.
* `AlgebraicGeometry.Space.quasicoherentModule_hasColimits_of_closure` is **Stacks 077X**: the
  quasi-coherent modules on a groupoid in algebraic spaces have all colimits indexed in the
  universe of the schemes.

## Implementation notes

The transport of Stacks 0441 is `AlgebraicGeometry.Space.pullbackTransport`, the canonical
identification of `f^*ℱ` with `g^*ℱ` for `f = g`, obtained by transporting at one module.
`AlgebraicGeometry.Space.modulePullbackEqToHom` transports instead at the level of functors, so
that its naturality in the module is an instance of `CategoryTheory.NatTrans.naturality`; the
two agree by `pullbackTransport_eq_modulePullbackEqToHom_app`.

The inverse image `f^*` of Stacks 03LU is a left adjoint, so it preserves colimits; this is
`AlgebraicGeometry.Space.modulePullback_isLeftAdjoint` and it is what makes the transition
morphism on a colimit exist and be unique.  Both the cocycle condition and the unit condition
are then checked leg by leg, using that `(c ≫ t)^*`, respectively `(e ≫ t)^*`, also preserves
the colimit; the two sides of each condition are natural in the module, which is
`AlgebraicGeometry.Space.groupoidPullbackTransition_naturality`,
`AlgebraicGeometry.Space.groupoidTransitionComposite_naturality` and
`AlgebraicGeometry.Space.pullbackTransport_naturality` of Stacks 0441.

The ambient colimits of `𝒪_U`-modules are not constructed here.  The category of sheaves of
modules on the small étale ringed site of an algebraic space is cocomplete at the universe of
the structure rings by Mathlib's `SheafOfModules` colimits together with the sheafification
instances of `StacksFrontier/AlgebraicGeometry/Spaces/ModulesAbelian.lean`, and instance search
finds them; this is what makes `colimitTransition` a morphism out of a colimit.

That the colimit of the underlying modules is again quasi-coherent is the arbitrary-colimit
clause of Stacks 03M1 for the space of objects,
`AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_quasicoherentSheaves_schemeUniverse`,
which is what the source proof cites at this point.

The module universe is the universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullback` exists only there; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullback.lean`.  The indexing universe of
the colimits is therefore that universe as well.

## References

* [Stacks Project, Tag 077X](https://stacks.math.columbia.edu/tag/077X)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u₁ v₁ u

namespace CategoryTheory

/-- **The composite of two composable morphisms**, as a named operation.

Naming the binary composite keeps it behind an ordinary constant rather than behind the
composition field of the ambient category, exactly as `CategoryTheory.comp₃` does for the triple
composite.  It is needed here for a reason that is invisible at the surface: deciding
`u ≫ v = u' ≫ v'` from `u = u'` forces the kernel to reduce the `CategoryStruct.comp`
projection of the `𝒪`-modules on a small étale ringed site, which opens the two factors
pointwise; when one of them is an `AlgebraicGeometry.Space.pullbackTransport`, reducing it
reaches an `CategoryTheory.eqToHom` over an equality of morphisms of algebraic spaces that is
not definitional, and the kernel exhausts its budget trying to reduce the equality proof.  At
`comp₂` the same comparison is settled argument by argument and costs nothing. -/
def comp₂ {C : Type u₁} [Category.{v₁} C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : X ⟶ Z :=
  f ≫ g

/-- The binary composite is the composite of its two factors. -/
theorem comp₂_eq {C : Type u₁} [Category.{v₁} C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    comp₂ f g = f ≫ g :=
  rfl

end CategoryTheory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : AlgebraicSpaces B S hS}

/-- Transport of the inverse image of modules along an equality of the two morphisms it is taken
along, read at the level of functors: the natural isomorphism `f^* ⟶ g^*` attached to `f = g`.

Taking the congruence at the functor rather than at one module keeps the proof terms small — the
equation it transports along is an equality of functors, not an equality of objects obtained by
abstracting a morphism inside `Functor.obj` — and it makes the naturality of the transport in
the module an instance of `CategoryTheory.NatTrans.naturality`. -/
def modulePullbackEqToHom {X Y : AlgebraicSpaces B S hS} {f g : X ⟶ Y} (h : f = g) :
    modulePullback B S hS f ⟶ modulePullback B S hS g :=
  eqToHom (congrArg (modulePullback B S hS) h)

/-- The canonical identification of the inverse images of a module along two equal morphisms is
the functor-level transport, evaluated at that module. -/
theorem pullbackTransport_eq_modulePullbackEqToHom_app {T X : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS X.1 X.2) {f g : T ⟶ X} (h : f = g) :
    pullbackTransport M h =
      (modulePullbackEqToHom (B := B) (S := S) (hS := hS) h).app M := by
  subst h
  simp [pullbackTransport, modulePullbackEqToHom]

/-- **Two commuting squares in a row paste into one.**  This is Mathlib's
`CategoryTheory.CommSq.vert_comp` with the two composites of the conclusion written out. -/
theorem _root_.CategoryTheory.comp_naturality₂ {C : Type*} [Category C]
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} {a : X₁ ⟶ X₂} {b : X₂ ⟶ X₃} {a' : Y₁ ⟶ Y₂} {b' : Y₂ ⟶ Y₃}
    {n₁ : X₁ ⟶ Y₁} {n₂ : X₂ ⟶ Y₂} {n₃ : X₃ ⟶ Y₃}
    (h₁ : n₁ ≫ a' = a ≫ n₂) (h₂ : n₂ ≫ b' = b ≫ n₃) :
    n₁ ≫ a' ≫ b' = (a ≫ b) ≫ n₃ := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- **Three commuting squares in a row paste into one**, with both composites of the conclusion
bracketed to the right, which is the form of a goal normalized by
`CategoryTheory.Category.assoc`. -/
theorem _root_.CategoryTheory.comp_naturality₃ {C : Type*} [Category C]
    {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : C} {a : X₁ ⟶ X₂} {b : X₂ ⟶ X₃} {c : X₃ ⟶ X₄}
    {a' : Y₁ ⟶ Y₂} {b' : Y₂ ⟶ Y₃} {c' : Y₃ ⟶ Y₄}
    {n₁ : X₁ ⟶ Y₁} {n₂ : X₂ ⟶ Y₂} {n₃ : X₃ ⟶ Y₃} {n₄ : X₄ ⟶ Y₄}
    (h₁ : n₁ ≫ a' = a ≫ n₂) (h₂ : n₂ ≫ b' = b ≫ n₃) (h₃ : n₃ ≫ c' = c ≫ n₄) :
    n₁ ≫ a' ≫ b' ≫ c' = a ≫ b ≫ c ≫ n₄ := by
  rw [← Category.assoc, h₁, Category.assoc, ← Category.assoc n₂ b' c', h₂, Category.assoc, h₃]

/-- The transport along the target equation of the composition diagram, followed by the
reindexing along the first projection of the space of composable pairs, is natural in the
module: the first two of the five squares of the cocycle condition, pasted. -/
theorem pasteTransportFirstArrow (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    {M N : Modules.{u, u} B S hS G.objects.1 G.objects.2}
    {α : (modulePullback B S hS G.target).obj M ⟶ (modulePullback B S hS G.source).obj M}
    {β : (modulePullback B S hS G.target).obj N ⟶ (modulePullback B S hS G.source).obj N}
    (φ : M ⟶ N)
    (hφ : α ≫ (modulePullback B S hS G.source).map φ =
      (modulePullback B S hS G.target).map φ ≫ β) :
    (modulePullback B S hS (G.comp ≫ G.target)).map φ ≫
        pullbackTransport N (GroupoidInAlgebraicSpaces.comp_comp_target G) ≫
          groupoidPullbackTransition B S hS G N β
            (GroupoidInAlgebraicSpaces.firstArrow G) =
      (pullbackTransport M (GroupoidInAlgebraicSpaces.comp_comp_target G) ≫
          groupoidPullbackTransition B S hS G M α
            (GroupoidInAlgebraicSpaces.firstArrow G)) ≫
        (modulePullback B S hS
          (GroupoidInAlgebraicSpaces.firstArrow G ≫ G.source)).map φ :=
  comp_naturality₂
    (pullbackTransport_naturality φ (GroupoidInAlgebraicSpaces.comp_comp_target G))
    (groupoidPullbackTransition_naturality B S hS G φ hφ
      (GroupoidInAlgebraicSpaces.firstArrow G))

/-- The transport along the commuting square of the space of composable pairs, followed by the
reindexing along its second projection, is natural in the module: the third and fourth of the
five squares of the cocycle condition, pasted. -/
theorem pasteTransportSecondArrow (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    {M N : Modules.{u, u} B S hS G.objects.1 G.objects.2}
    {α : (modulePullback B S hS G.target).obj M ⟶ (modulePullback B S hS G.source).obj M}
    {β : (modulePullback B S hS G.target).obj N ⟶ (modulePullback B S hS G.source).obj N}
    (φ : M ⟶ N)
    (hφ : α ≫ (modulePullback B S hS G.source).map φ =
      (modulePullback B S hS G.target).map φ ≫ β) :
    (modulePullback B S hS
          (GroupoidInAlgebraicSpaces.firstArrow G ≫ G.source)).map φ ≫
        pullbackTransport N (GroupoidInAlgebraicSpaces.firstArrow_comp_source G) ≫
          groupoidPullbackTransition B S hS G N β
            (GroupoidInAlgebraicSpaces.secondArrow G) =
      (pullbackTransport M (GroupoidInAlgebraicSpaces.firstArrow_comp_source G) ≫
          groupoidPullbackTransition B S hS G M α
            (GroupoidInAlgebraicSpaces.secondArrow G)) ≫
        (modulePullback B S hS
          (GroupoidInAlgebraicSpaces.secondArrow G ≫ G.source)).map φ :=
  comp_naturality₂
    (pullbackTransport_naturality φ (GroupoidInAlgebraicSpaces.firstArrow_comp_source G))
    (groupoidPullbackTransition_naturality B S hS G φ hφ
      (GroupoidInAlgebraicSpaces.secondArrow G))

/-- The inverse image of `𝒪`-modules along a morphism of algebraic spaces is a left adjoint:
its right adjoint is the direct image, by the adjunction of Stacks 03LU.  Consequently it
preserves all colimits. -/
instance modulePullback_isLeftAdjoint {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (modulePullback B S hS f).IsLeftAdjoint :=
  (modulePullbackAdjunction B S hS f).isLeftAdjoint

/-- Transporting along an equality of morphisms is natural in the module, stated at the named
binary composite `CategoryTheory.comp₂`.  This is the form in which the naturality can be used
against a goal whose two sides spell the module differently — through the vertex of a mapped
cocone on one side and through the cocone's own vertex on the other — because the comparison is
then made argument by argument instead of by reducing the composition of the two factors. -/
theorem pullbackTransport_naturality₂ {T X : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N) {f g : T ⟶ X} (h : f = g) :
    comp₂ (pullbackTransport M h) ((modulePullback B S hS g).map φ) =
      comp₂ ((modulePullback B S hS f).map φ) (pullbackTransport N h) := by
  rw [comp₂_eq, comp₂_eq]
  exact (pullbackTransport_naturality φ h).symm

namespace QuasicoherentModule

open GroupoidInAlgebraicSpaces

section

variable {G : GroupoidInAlgebraicSpaces B S hS A} {J : Type u} [Category.{u} J]
  (D : J ⥤ QuasicoherentModule B S hS G)
  (c : Cocone (D ⋙ QuasicoherentModule.forget G)) (hc : IsColimit c)

/-- The transition morphism `t^*ℱ ⟶ s^*ℱ` on a colimit `ℱ` of the underlying modules of a
diagram of quasi-coherent modules on a groupoid in algebraic spaces: the unique morphism out of
`t^*ℱ`, which is a colimit because `t^*` is a left adjoint, whose leg at `j` is the transition
of the `j`-th module followed by the `j`-th leg of `s^*ℱ`. -/
def colimitTransition :
    (modulePullback B S hS G.target).obj c.pt ⟶ (modulePullback B S hS G.source).obj c.pt :=
  (isColimitOfPreserves (modulePullback B S hS G.target) hc).desc
    { pt := (modulePullback B S hS G.source).obj c.pt
      ι :=
        { app := fun j => (D.obj j).alpha ≫
            (modulePullback B S hS G.source).map (c.ι.app j)
          naturality := by
            intro i j f
            dsimp
            simp only [Category.comp_id]
            rw [← Category.assoc, ← (D.map f).comm, Category.assoc, ← Functor.map_comp,
              show (D.map f).hom ≫ c.ι.app j = c.ι.app i from c.w f] } }

/-- The defining property of the transition morphism on a colimit: on the `j`-th leg of `t^*ℱ`
it is the transition of the `j`-th module followed by the `j`-th leg of `s^*ℱ`. -/
theorem colimitTransition_ι (j : J) :
    (modulePullback B S hS G.target).map (c.ι.app j) ≫ colimitTransition D c hc =
      (D.obj j).alpha ≫ (modulePullback B S hS G.source).map (c.ι.app j) :=
  (isColimitOfPreserves (modulePullback B S hS G.target) hc).fac _ j

/-- **The cocycle condition for the transition morphism on a colimit.**  Pulling the transition
back along the composition agrees with pulling it back along the two projections in turn: both
sides are checked on the `j`-th leg of `(c ≫ t)^*ℱ`, where they are the two sides of the cocycle
condition for the `j`-th module, because `(c ≫ t)^*` preserves the colimit and both sides are
natural in the module. -/
theorem colimitTransition_cocycle :
    groupoidPullbackTransition B S hS G c.pt (colimitTransition D c hc) G.comp =
      groupoidTransitionComposite B S hS G c.pt (colimitTransition D c hc) := by
  apply (isColimitOfPreserves (modulePullback B S hS (G.comp ≫ G.target)) hc).hom_ext
  intro j
  dsimp only [Functor.mapCocone_ι_app]
  rw [groupoidPullbackTransition_naturality B S hS G (M := (D.obj j).F.obj) (N := c.pt)
      (c.ι.app j) (colimitTransition_ι D c hc j).symm G.comp,
    groupoidTransitionComposite_naturality B S hS G (M := (D.obj j).F.obj) (N := c.pt)
      (c.ι.app j) (colimitTransition_ι D c hc j).symm,
    (D.obj j).cocycle]

/-- **The unit condition for the transition morphism on a colimit.**  Pulling the transition back
along the unit `e : U ⟶ R` gives the canonical transport, because `(e ≫ t)^*` preserves the
colimit and, on the `j`-th leg, the condition is the unit condition for the `j`-th module
followed by the naturality of the transport.  The last step is taken at
`CategoryTheory.comp₂` rather than at `≫`: the two sides reach the colimit module through
different spellings — the vertex of the mapped cocone, and the cocone's own vertex — and
reconciling them under a composition one of whose factors is a transport is not something the
kernel can do, while at the named composite it is settled factor by factor. -/
theorem colimitTransition_unit :
    groupoidPullbackTransition B S hS G c.pt (colimitTransition D c hc) (identityArrow G) =
      pullbackTransport c.pt
        ((identityArrow_comp_target G).trans (identityArrow_comp_source G).symm) := by
  apply (isColimitOfPreserves (modulePullback B S hS (identityArrow G ≫ G.target)) hc).hom_ext
  intro j
  dsimp only [Functor.mapCocone_ι_app]
  rw [groupoidPullbackTransition_naturality B S hS G (M := (D.obj j).F.obj) (N := c.pt)
      (c.ι.app j) (colimitTransition_ι D c hc j).symm (identityArrow G),
    (D.obj j).unit,
    ← comp₂_eq (C := Modules.{u, u} B S hS G.objects.1 G.objects.2),
    ← comp₂_eq (C := Modules.{u, u} B S hS G.objects.1 G.objects.2)]
  exact pullbackTransport_naturality₂ (M := (D.obj j).F.obj) (N := c.pt) (c.ι.app j)
    ((identityArrow_comp_target G).trans (identityArrow_comp_source G).symm)

/-- A colimit of the underlying modules of a diagram of quasi-coherent modules on a groupoid in
algebraic spaces, with its transition morphism, as a quasi-coherent module on the groupoid.  The
cocycle and unit conditions hold because `(c ≫ t)^*` and `(e ≫ t)^*` preserve the colimit and
both sides of each condition are natural in the module. -/
def colimitModule (hqc : c.pt.IsQuasicoherentOnSite) : QuasicoherentModule B S hS G where
  F := ⟨c.pt, hqc⟩
  alpha := colimitTransition D c hc
  cocycle := colimitTransition_cocycle D c hc
  unit := colimitTransition_unit D c hc

/-- The cocone on a diagram of quasi-coherent modules on a groupoid in algebraic spaces whose
vertex is the colimit of the underlying modules, with the legs of that colimit. -/
def liftedColimitCocone (hqc : c.pt.IsQuasicoherentOnSite) : Cocone D where
  pt := colimitModule D c hc hqc
  ι :=
    { app := fun j =>
        { hom := c.ι.app j
          comm := (colimitTransition_ι D c hc j).symm }
      naturality := by
        intro i j f
        apply QuasicoherentModule.Hom.ext
        change (D.map f).hom ≫ c.ι.app j = c.ι.app i ≫ 𝟙 c.pt
        simpa using c.w f }

/-- The underlying module of the colimit quasi-coherent module is the colimit of the underlying
modules. -/
@[simp]
theorem colimitModule_F_obj (hqc : c.pt.IsQuasicoherentOnSite) :
    (colimitModule D c hc hqc).F.obj = c.pt :=
  rfl

/-- The transition morphism of the colimit quasi-coherent module is
`AlgebraicGeometry.Space.QuasicoherentModule.colimitTransition`. -/
@[simp]
theorem colimitModule_alpha (hqc : c.pt.IsQuasicoherentOnSite) :
    (colimitModule D c hc hqc).alpha = colimitTransition D c hc :=
  rfl

/-- The vertex of the lifted cocone is the colimit quasi-coherent module. -/
@[simp]
theorem liftedColimitCocone_pt (hqc : c.pt.IsQuasicoherentOnSite) :
    (liftedColimitCocone D c hc hqc).pt = colimitModule D c hc hqc :=
  rfl

/-- The cocone of `AlgebraicGeometry.Space.QuasicoherentModule.liftedColimitCocone` is a
colimit: a morphism out of it is a morphism out of the colimit of the underlying modules, and
such a morphism is compatible with the transitions as soon as it is on every leg. -/
def liftedColimitCoconeIsColimit (hqc : c.pt.IsQuasicoherentOnSite) :
    IsColimit (liftedColimitCocone D c hc hqc) where
  desc s :=
    { hom := hc.desc ((QuasicoherentModule.forget G).mapCocone s)
      comm := by
        apply (isColimitOfPreserves (modulePullback B S hS G.target) hc).hom_ext
        intro j
        have hfac : c.ι.app j ≫ hc.desc ((QuasicoherentModule.forget G).mapCocone s) =
          (s.ι.app j).hom := hc.fac _ j
        dsimp only [Functor.mapCocone_ι_app, Functor.mapCocone_pt, forget_obj,
          liftedColimitCocone_pt, colimitModule_alpha, colimitModule_F_obj]
        rw [← Category.assoc, colimitTransition_ι D c hc j, Category.assoc,
          ← Functor.map_comp, hfac, ← Category.assoc, ← Functor.map_comp, hfac]
        exact (s.ι.app j).comm }
  fac s j := QuasicoherentModule.Hom.ext (hc.fac ((QuasicoherentModule.forget G).mapCocone s) j)
  uniq s f hf := by
    refine QuasicoherentModule.Hom.ext (hc.hom_ext fun j => ?_)
    change c.ι.app j ≫ f.hom =
      c.ι.app j ≫ hc.desc ((QuasicoherentModule.forget G).mapCocone s)
    rw [hc.fac]
    exact congrArg QuasicoherentModule.Hom.hom (hf j)

end

/-- A diagram of quasi-coherent modules on a groupoid in algebraic spaces has a colimit as soon
as the colimit of its underlying modules is quasi-coherent. -/
theorem hasColimit_of_forget {G : GroupoidInAlgebraicSpaces B S hS A} {J : Type u}
    [Category.{u} J] (D : J ⥤ QuasicoherentModule B S hS G)
    [HasColimit (D ⋙ QuasicoherentModule.forget G)]
    (hqc : (colimit (D ⋙ QuasicoherentModule.forget G)).IsQuasicoherentOnSite) :
    HasColimit D :=
  ⟨⟨liftedColimitCocone D _ (colimit.isColimit _) hqc,
    liftedColimitCoconeIsColimit D _ (colimit.isColimit _) hqc⟩⟩

end QuasicoherentModule

/-- **Stacks 077X.**  The category of quasi-coherent modules on a groupoid in algebraic spaces
has colimits, indexed by the categories of the universe of the schemes.

A colimit is computed on the underlying `𝒪_U`-modules, where it exists because the sheaves of
modules on the small étale ringed site of an algebraic space are cocomplete, and it is
quasi-coherent by the arbitrary-colimit clause of Stacks 03M1,
`AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_quasicoherentSheaves_schemeUniverse`. -/
@[stacks 077X]
theorem quasicoherentModule_hasColimits_of_closure (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : AlgebraicSpaces B S hS}
    (G : GroupoidInAlgebraicSpaces B S hS A) :
    HasColimitsOfSize.{u, u} (QuasicoherentModule B S hS G) :=
  ⟨fun K _ => ⟨fun D =>
    have := isClosedUnderColimitsOfShape_quasicoherentSheaves_schemeUniverse B S hS
      G.objects.1 G.objects.2 K
    QuasicoherentModule.hasColimit_of_forget D
      (ObjectProperty.prop_colimit _ _ fun k => (D.obj k).F.property)⟩⟩

end AlgebraicGeometry.Space

end
