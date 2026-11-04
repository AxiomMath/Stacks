module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentModuleHomMk
public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatExact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentFiniteProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsUnconditional

/-!
# The quasi-coherent modules on a groupoid in algebraic spaces form an abelian category

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `A`.  Stacks 06VZ
asserts that if `s` and `t` are flat then the quasi-coherent modules on the groupoid form an
abelian category.  The argument is the one of the source: a kernel and a cokernel are computed on
the underlying `𝒪_U`-module, flatness making `s^*` and `t^*` exact, so that the transition
morphism `α : t^*ℱ ⟶ s^*ℱ` is carried along; the cocycle and unit conditions for the induced
transition morphism hold because both sides of each are natural in the module and the kernel,
respectively the cokernel, is preserved by the inverse images the two conditions are read along.

The cokernel half needs no flatness at all: an inverse image of `𝒪`-modules is a left adjoint,
hence preserves every colimit.  Flatness enters only through the kernel half, and only through
the inverse images along `s`, along `c ≫ s` and along `e ≫ s`.

## Main definitions

* `AlgebraicGeometry.Space.QuasicoherentModule.limitTransition` is the transition morphism on a
  limit of the underlying modules of a diagram of quasi-coherent modules on the groupoid, and
  `AlgebraicGeometry.Space.QuasicoherentModule.limitModule`,
  `AlgebraicGeometry.Space.QuasicoherentModule.liftedLimitCone` package it as a quasi-coherent
  module on the groupoid and as a cone.
* `AlgebraicGeometry.Space.QuasicoherentModule.cokernelTransition` is the transition morphism on
  a cokernel of the underlying morphism, with
  `AlgebraicGeometry.Space.QuasicoherentModule.cokernelModule` and
  `AlgebraicGeometry.Space.QuasicoherentModule.liftedCokernelCofork`.
* `AlgebraicGeometry.Space.QuasicoherentModule.homAddSubgroup` is the group of morphisms of
  `𝒪_U`-modules compatible with two transition morphisms.

## Main results

* `AlgebraicGeometry.Space.modulePullback_additive`: an inverse image of `𝒪`-modules along a
  morphism of algebraic spaces is additive, being a left adjoint.
* `AlgebraicGeometry.Space.QuasicoherentModule.preadditive`: the quasi-coherent modules on a
  groupoid in algebraic spaces form a preadditive category, and
  `AlgebraicGeometry.Space.QuasicoherentModule.forget_additive` and
  `AlgebraicGeometry.Space.QuasicoherentModule.forget_reflectsIsomorphisms` are the two
  properties of the forgetful functor that the abelian structure runs on.
* `AlgebraicGeometry.Space.QuasicoherentModule.limitTransition_cocycle` and
  `AlgebraicGeometry.Space.QuasicoherentModule.limitTransition_unit`, and their counterparts
  `AlgebraicGeometry.Space.QuasicoherentModule.cokernelTransition_cocycle` and
  `AlgebraicGeometry.Space.QuasicoherentModule.cokernelTransition_unit`: the two conditions of
  Stacks 0441 for the induced transition morphisms.
* `AlgebraicGeometry.Space.QuasicoherentModule.liftedLimitConeIsLimit` and
  `AlgebraicGeometry.Space.QuasicoherentModule.liftedCokernelCoforkIsColimit`: the lifted cone
  and cofork are a limit and a colimit, and
  `AlgebraicGeometry.Space.QuasicoherentModule.preservesLimit_forget`,
  `AlgebraicGeometry.Space.QuasicoherentModule.preservesColimit_forget`: the forgetful functor
  preserves them.
* `AlgebraicGeometry.Space.QuasicoherentModule.hasKernels_of_closure`,
  `AlgebraicGeometry.Space.QuasicoherentModule.hasCokernels_of_closure` and
  `AlgebraicGeometry.Space.QuasicoherentModule.hasFiniteProducts`: the three finite (co)limit
  properties of the category.
* `AlgebraicGeometry.Space.QuasicoherentModule.abelian_of_closure` is **Stacks 06VZ**: if the
  source and the target of the groupoid are flat, its quasi-coherent modules form an abelian
  category.

## Implementation notes

The limit construction is stated for an arbitrary diagram, not only for a kernel, because the
finite products of the category are an instance of it as well: there the required preservation is
free, an additive functor preserving finite products.  It is the exact dual of
`AlgebraicGeometry.Space.QuasicoherentModule.colimitTransition` of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuasicoherentColimits.lean`, whose shape universes
are those of the schemes and so does not cover the two-object shape of a cokernel; the cokernel is
therefore built here directly on a cofork, which is also what makes the forgetful functor's
preservation of it immediate.

The preadditive structure is transported from the subgroup
`AlgebraicGeometry.Space.QuasicoherentModule.homAddSubgroup` of compatible morphisms, so that the
underlying morphism of a sum, of a zero and of a composite is the sum, the zero and the composite
of the underlying morphisms by `rfl`; those three equations are recorded as simp lemmas and
are what the arguments below run on.

The abelian structure is Mathlib's
`CategoryTheory.Abelian.ofCoimageImageComparisonIsIso`.  Its hypothesis is checked by pushing the
coimage-image comparison through the forgetful functor, which preserves kernels and cokernels by
the two constructions above and reflects isomorphisms, and by the comparison already being
invertible in the abelian category of all `𝒪_U`-modules.

The kernel and cokernel constructions take the closure of quasi-coherence and the left exactness
of the inverse images as instance arguments, and the proof of Stacks 06VZ supplies them.  The
kernel and cokernel clauses of Stacks 03M1(3) on the space of objects are
`AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_schemeUniverse` and
`AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves`.  The inverse images along
`s`, along `c ≫ s` and along `e ≫ s` preserve finite limits by
`AlgebraicGeometry.Space.preservesFiniteLimits_modulePullback_of_isFlat_hom`: `s` is flat by
assumption, `c` is a base change of `s` by the cartesian square of Stacks 043Z
(`AlgebraicGeometry.Space.isPullback_comp_source`), so `c ≫ s` is flat, and `e ≫ s` is the
identity.  Flatness of `t` is not used: in a groupoid it is equivalent to flatness of `s`.

## References

* [Stacks Project, Tag 06VZ](https://stacks.math.columbia.edu/tag/06VZ)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 077X](https://stacks.math.columbia.edu/tag/077X)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w' u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : AlgebraicSpaces B S hS}

/-- The inverse image of `𝒪`-modules along a morphism of algebraic spaces is additive. -/
instance modulePullback_additive {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (modulePullback B S hS f).Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (modulePullback B S hS f)
  exact Functor.additive_of_preservesBinaryBiproducts _

namespace QuasicoherentModule

variable {G : GroupoidInAlgebraicSpaces B S hS A}

/-- The morphisms of `𝒪_U`-modules compatible with the transition morphisms of two
quasi-coherent modules on a groupoid in algebraic spaces, as a subgroup of all morphisms. -/
def homAddSubgroup (M N : QuasicoherentModule B S hS G) :
    AddSubgroup (M.F.obj ⟶ N.F.obj) where
  carrier := {h | M.alpha ≫ (modulePullback B S hS G.source).map h =
    (modulePullback B S hS G.target).map h ≫ N.alpha}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Functor.map_add, Preadditive.comp_add,
      Preadditive.add_comp] at ha hb ⊢
    rw [ha, hb]
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, Functor.map_neg, Preadditive.comp_neg,
      Preadditive.neg_comp] at ha ⊢
    rw [ha]

/-- A morphism of quasi-coherent modules on a groupoid in algebraic spaces is the same thing as
a compatible morphism of the underlying `𝒪_U`-modules. -/
def homEquiv (M N : QuasicoherentModule B S hS G) : (M ⟶ N) ≃ homAddSubgroup M N where
  toFun f := ⟨f.hom, f.comm⟩
  invFun h := ⟨h.1, h.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The quasi-coherent modules on a groupoid in algebraic spaces form a preadditive category:
the compatible morphisms form a subgroup of all morphisms of the underlying modules, and
composition there is bilinear. -/
instance preadditive : Preadditive (QuasicoherentModule B S hS G) where
  homGroup M N := (homEquiv M N).addCommGroup
  add_comp _ _ _ f f' g :=
    QuasicoherentModule.Hom.ext (Preadditive.add_comp _ _ _ f.hom f'.hom g.hom)
  comp_add _ _ _ f g g' :=
    QuasicoherentModule.Hom.ext (Preadditive.comp_add _ _ _ f.hom g.hom g'.hom)

/-- The underlying morphism of a sum of morphisms is the sum of the underlying morphisms. -/
@[simp]
theorem hom_add {M N : QuasicoherentModule B S hS G} (f g : M ⟶ N) :
    (f + g).hom = f.hom + g.hom :=
  rfl

/-- The underlying morphism of the zero morphism is zero. -/
@[simp]
theorem hom_zero (M N : QuasicoherentModule B S hS G) :
    QuasicoherentModule.Hom.hom (0 : M ⟶ N) = 0 :=
  rfl

/-- The forgetful functor to the `𝒪_U`-modules is additive. -/
instance forget_additive (G : GroupoidInAlgebraicSpaces B S hS A) :
    (QuasicoherentModule.forget G).Additive where
  map_add := rfl

section Limit

open GroupoidInAlgebraicSpaces

variable {J : Type w} [Category.{w'} J] (D : J ⥤ QuasicoherentModule B S hS G)
  (c : Cone (D ⋙ QuasicoherentModule.forget G)) (hc : IsLimit c)

variable [PreservesLimit (D ⋙ QuasicoherentModule.forget G) (modulePullback B S hS G.source)]

/-- The transition morphism `t^*ℱ ⟶ s^*ℱ` on a limit `ℱ` of the underlying modules of a diagram
of quasi-coherent modules on a groupoid in algebraic spaces: the unique morphism into `s^*ℱ`,
which is a limit because `s^*` is assumed to preserve the limit, whose leg at `j` is the `j`-th
leg of `t^*ℱ` followed by the transition of the `j`-th module. -/
def limitTransition :
    (modulePullback B S hS G.target).obj c.pt ⟶ (modulePullback B S hS G.source).obj c.pt :=
  (isLimitOfPreserves (modulePullback B S hS G.source) hc).lift
    { pt := (modulePullback B S hS G.target).obj c.pt
      π :=
        { app := fun j => (modulePullback B S hS G.target).map (c.π.app j) ≫ (D.obj j).alpha
          naturality := by
            intro i j f
            dsimp
            simp only [Category.id_comp, Category.assoc]
            rw [(D.map f).comm, ← Category.assoc, ← Functor.map_comp,
              show c.π.app i ≫ (D.map f).hom = c.π.app j from c.w f] } }

/-- The defining property of the transition morphism on a limit: on the `j`-th leg of `s^*ℱ` it
is the `j`-th leg of `t^*ℱ` followed by the transition of the `j`-th module. -/
theorem limitTransition_π (j : J) :
    limitTransition D c hc ≫ (modulePullback B S hS G.source).map (c.π.app j) =
      (modulePullback B S hS G.target).map (c.π.app j) ≫ (D.obj j).alpha :=
  (isLimitOfPreserves (modulePullback B S hS G.source) hc).fac _ j

/-- **The cocycle condition for the transition morphism on a limit.**  Both sides are checked on
the `j`-th leg of `(c ≫ s)^*ℱ`, where they are the two sides of the cocycle condition for the
`j`-th module, because `(c ≫ s)^*` preserves the limit and both sides are natural in the
module. -/
theorem limitTransition_cocycle
    [PreservesLimit (D ⋙ QuasicoherentModule.forget G)
      (modulePullback B S hS (G.comp ≫ G.source))] :
    groupoidPullbackTransition B S hS G c.pt (limitTransition D c hc) G.comp =
      groupoidTransitionComposite B S hS G c.pt (limitTransition D c hc) := by
  apply (isLimitOfPreserves (modulePullback B S hS (G.comp ≫ G.source)) hc).hom_ext
  intro j
  dsimp only [Functor.mapCone_π_app]
  rw [← groupoidPullbackTransition_naturality B S hS G (M := c.pt) (N := (D.obj j).F.obj)
      (c.π.app j) (limitTransition_π D c hc j) G.comp,
    (D.obj j).cocycle,
    groupoidTransitionComposite_naturality B S hS G (M := c.pt) (N := (D.obj j).F.obj)
      (c.π.app j) (limitTransition_π D c hc j)]

/-- **The unit condition for the transition morphism on a limit.**  Both sides are checked on
the `j`-th leg of `(e ≫ s)^*ℱ`, where they are the unit condition for the `j`-th module and the
naturality of the canonical transport. -/
theorem limitTransition_unit
    [PreservesLimit (D ⋙ QuasicoherentModule.forget G)
      (modulePullback B S hS (identityArrow G ≫ G.source))] :
    groupoidPullbackTransition B S hS G c.pt (limitTransition D c hc) (identityArrow G) =
      pullbackTransport c.pt
        ((identityArrow_comp_target G).trans (identityArrow_comp_source G).symm) := by
  apply (isLimitOfPreserves (modulePullback B S hS (identityArrow G ≫ G.source)) hc).hom_ext
  intro j
  dsimp only [Functor.mapCone_π_app]
  rw [← groupoidPullbackTransition_naturality B S hS G (M := c.pt) (N := (D.obj j).F.obj)
      (c.π.app j) (limitTransition_π D c hc j) (identityArrow G),
    (D.obj j).unit,
    ← comp₂_eq (C := Modules.{u, u} B S hS G.objects.1 G.objects.2),
    ← comp₂_eq (C := Modules.{u, u} B S hS G.objects.1 G.objects.2)]
  exact (pullbackTransport_naturality₂ (M := c.pt) (N := (D.obj j).F.obj) (c.π.app j)
    ((identityArrow_comp_target G).trans (identityArrow_comp_source G).symm)).symm

variable [PreservesLimit (D ⋙ QuasicoherentModule.forget G)
    (modulePullback B S hS (G.comp ≫ G.source))]
  [PreservesLimit (D ⋙ QuasicoherentModule.forget G)
    (modulePullback B S hS (identityArrow G ≫ G.source))]

/-- A limit of the underlying modules of a diagram of quasi-coherent modules on a groupoid in
algebraic spaces, with its transition morphism, as a quasi-coherent module on the groupoid. -/
def limitModule (hqc : c.pt.IsQuasicoherentOnSite) : QuasicoherentModule B S hS G where
  F := ⟨c.pt, hqc⟩
  alpha := limitTransition D c hc
  cocycle := limitTransition_cocycle D c hc
  unit := limitTransition_unit D c hc

/-- The cone on a diagram of quasi-coherent modules on a groupoid in algebraic spaces whose
vertex is the limit of the underlying modules, with the legs of that limit. -/
def liftedLimitCone (hqc : c.pt.IsQuasicoherentOnSite) : Cone D where
  pt := limitModule D c hc hqc
  π :=
    { app := fun j => { hom := c.π.app j, comm := limitTransition_π D c hc j }
      naturality := by
        intro i j f
        apply QuasicoherentModule.Hom.ext
        change 𝟙 c.pt ≫ c.π.app j = c.π.app i ≫ (D.map f).hom
        simpa using (c.w f).symm }

/-- The underlying module of the limit quasi-coherent module is the limit of the underlying
modules. -/
@[simp]
theorem limitModule_F_obj (hqc : c.pt.IsQuasicoherentOnSite) :
    (limitModule D c hc hqc).F.obj = c.pt :=
  rfl

/-- The transition morphism of the limit quasi-coherent module is
`AlgebraicGeometry.Space.QuasicoherentModule.limitTransition`. -/
@[simp]
theorem limitModule_alpha (hqc : c.pt.IsQuasicoherentOnSite) :
    (limitModule D c hc hqc).alpha = limitTransition D c hc :=
  rfl

/-- The vertex of the lifted cone is the limit quasi-coherent module. -/
@[simp]
theorem liftedLimitCone_pt (hqc : c.pt.IsQuasicoherentOnSite) :
    (liftedLimitCone D c hc hqc).pt = limitModule D c hc hqc :=
  rfl

/-- The legs of the lifted limit cone are the legs of the limit cone of the underlying
modules. -/
@[simp]
theorem liftedLimitCone_π_hom (hqc : c.pt.IsQuasicoherentOnSite) (j : J) :
    ((liftedLimitCone D c hc hqc).π.app j).hom = c.π.app j :=
  rfl

/-- The cone of `AlgebraicGeometry.Space.QuasicoherentModule.liftedLimitCone` is a limit: a
morphism into it is a morphism into the limit of the underlying modules, and such a morphism is
compatible with the transitions as soon as it is on every leg. -/
def liftedLimitConeIsLimit (hqc : c.pt.IsQuasicoherentOnSite) :
    IsLimit (liftedLimitCone D c hc hqc) where
  lift E :=
    { hom := hc.lift ((QuasicoherentModule.forget G).mapCone E)
      comm := by
        apply (isLimitOfPreserves (modulePullback B S hS G.source) hc).hom_ext
        intro j
        have hfac : hc.lift ((QuasicoherentModule.forget G).mapCone E) ≫ c.π.app j =
          (E.π.app j).hom := hc.fac _ j
        dsimp only [Functor.mapCone_π_app, Functor.mapCone_pt, forget_obj,
          liftedLimitCone_pt, limitModule_alpha, limitModule_F_obj]
        rw [Category.assoc, Category.assoc, ← Functor.map_comp, hfac,
          limitTransition_π D c hc j, ← Category.assoc, ← Functor.map_comp, hfac]
        exact (E.π.app j).comm }
  fac E j := QuasicoherentModule.Hom.ext (hc.fac ((QuasicoherentModule.forget G).mapCone E) j)
  uniq E f hf := by
    refine QuasicoherentModule.Hom.ext (hc.hom_ext fun j => ?_)
    change f.hom ≫ c.π.app j =
      hc.lift ((QuasicoherentModule.forget G).mapCone E) ≫ c.π.app j
    rw [hc.fac]
    exact congrArg QuasicoherentModule.Hom.hom (hf j)

end Limit

section Cokernel

open GroupoidInAlgebraicSpaces

variable {P Q : QuasicoherentModule B S hS G} (φ : P ⟶ Q)
  (c : CokernelCofork (QuasicoherentModule.Hom.hom φ)) (hc : IsColimit c)

/-- The transition morphism `t^*𝒞 ⟶ s^*𝒞` on a cokernel `𝒞` of the underlying morphism of a
morphism of quasi-coherent modules on a groupoid in algebraic spaces: the unique morphism out of
`t^*𝒞`, which is a cokernel because `t^*` is a left adjoint, whose composite with the projection
is the transition of the target followed by the projection pulled back along `s`. -/
def cokernelTransition :
    (modulePullback B S hS G.target).obj c.pt ⟶ (modulePullback B S hS G.source).obj c.pt :=
  (CokernelCofork.mapIsColimit c hc (modulePullback B S hS G.target)).desc
    (CokernelCofork.ofπ (Q.alpha ≫ (modulePullback B S hS G.source).map (Cofork.π c))
      (by
        rw [← Category.assoc, ← φ.comm, Category.assoc, ← Functor.map_comp,
          CokernelCofork.condition c, Functor.map_zero, comp_zero]))

/-- The defining property of the transition morphism on a cokernel. -/
theorem cokernelTransition_π :
    (modulePullback B S hS G.target).map (Cofork.π c) ≫ cokernelTransition φ c hc =
      Q.alpha ≫ (modulePullback B S hS G.source).map (Cofork.π c) :=
  (CokernelCofork.mapIsColimit c hc (modulePullback B S hS G.target)).fac _
    WalkingParallelPair.one

/-- **The cocycle condition for the transition morphism on a cokernel.**  Both sides are checked
after the projection pulled back along `c ≫ t`, where they are the two sides of the cocycle
condition for the target module, because `(c ≫ t)^*` is a left adjoint and both sides are
natural in the module. -/
theorem cokernelTransition_cocycle :
    groupoidPullbackTransition B S hS G c.pt (cokernelTransition φ c hc) G.comp =
      groupoidTransitionComposite B S hS G c.pt (cokernelTransition φ c hc) := by
  apply Cofork.IsColimit.hom_ext
    (CokernelCofork.mapIsColimit c hc (modulePullback B S hS (G.comp ≫ G.target)))
  simp only [CokernelCofork.map_π]
  rw [groupoidPullbackTransition_naturality B S hS G (M := Q.F.obj) (N := c.pt) (Cofork.π c)
      (cokernelTransition_π φ c hc).symm G.comp,
    Q.cocycle,
    ← groupoidTransitionComposite_naturality B S hS G (M := Q.F.obj) (N := c.pt) (Cofork.π c)
      (cokernelTransition_π φ c hc).symm]

/-- **The unit condition for the transition morphism on a cokernel.**  Both sides are checked
after the projection pulled back along `e ≫ t`, where they are the unit condition for the target
module and the naturality of the canonical transport. -/
theorem cokernelTransition_unit :
    groupoidPullbackTransition B S hS G c.pt (cokernelTransition φ c hc) (identityArrow G) =
      pullbackTransport c.pt
        ((identityArrow_comp_target G).trans (identityArrow_comp_source G).symm) := by
  apply Cofork.IsColimit.hom_ext
    (CokernelCofork.mapIsColimit c hc (modulePullback B S hS (identityArrow G ≫ G.target)))
  simp only [CokernelCofork.map_π]
  rw [groupoidPullbackTransition_naturality B S hS G (M := Q.F.obj) (N := c.pt) (Cofork.π c)
      (cokernelTransition_π φ c hc).symm (identityArrow G),
    Q.unit, ← comp₂_eq (C := Modules.{u, u} B S hS G.objects.1 G.objects.2),
    ← comp₂_eq (C := Modules.{u, u} B S hS G.objects.1 G.objects.2)]
  exact pullbackTransport_naturality₂ (M := Q.F.obj) (N := c.pt) (Cofork.π c)
    ((identityArrow_comp_target G).trans (identityArrow_comp_source G).symm)

/-- A cokernel of the underlying morphism, with its transition morphism, as a quasi-coherent
module on the groupoid. -/
def cokernelModule (hqc : c.pt.IsQuasicoherentOnSite) : QuasicoherentModule B S hS G where
  F := ⟨c.pt, hqc⟩
  alpha := cokernelTransition φ c hc
  cocycle := cokernelTransition_cocycle φ c hc
  unit := cokernelTransition_unit φ c hc

/-- The underlying module of `cokernelModule` is the vertex of the cokernel cofork. -/
@[simp]
theorem cokernelModule_F_obj (hqc : c.pt.IsQuasicoherentOnSite) :
    (cokernelModule φ c hc hqc).F.obj = c.pt :=
  rfl

/-- The transition morphism of `cokernelModule` is `cokernelTransition`. -/
@[simp]
theorem cokernelModule_alpha (hqc : c.pt.IsQuasicoherentOnSite) :
    (cokernelModule φ c hc hqc).alpha = cokernelTransition φ c hc :=
  rfl

/-- The cofork of `𝒪_U`-modules underlying a cofork of quasi-coherent modules on a groupoid in
algebraic spaces. -/
def forgetCofork (E : CokernelCofork φ) : CokernelCofork (QuasicoherentModule.Hom.hom φ) :=
  CokernelCofork.ofπ (Cofork.π E).hom
    (by rw [← comp_hom, CokernelCofork.condition, hom_zero])

/-- The projection of `forgetCofork` is the underlying morphism of the projection of the
cofork. -/
@[simp]
theorem forgetCofork_π (E : CokernelCofork φ) :
    Cofork.π (forgetCofork φ E) = (Cofork.π E).hom :=
  rfl

/-- A morphism out of a cokernel of the underlying morphism which agrees with the projection of a
cofork of quasi-coherent modules is compatible with the transition morphisms.  Both sides are
checked after the projection, where the statement is the compatibility of that cofork. -/
theorem cokernelTransition_comp (E : CokernelCofork φ) (d : c.pt ⟶ E.pt.F.obj)
    (hd : Cofork.π c ≫ d = (Cofork.π E).hom) :
    cokernelTransition φ c hc ≫ (modulePullback B S hS G.source).map d =
      (modulePullback B S hS G.target).map d ≫ E.pt.alpha := by
  apply Cofork.IsColimit.hom_ext
    (CokernelCofork.mapIsColimit c hc (modulePullback B S hS G.target))
  simp only [CokernelCofork.map_π]
  rw [← Category.assoc, cokernelTransition_π φ c hc, Category.assoc, ← Functor.map_comp,
    ← Category.assoc, ← Functor.map_comp, hd]
  exact (Cofork.π E).comm

/-- The cokernel cofork on a morphism of quasi-coherent modules on a groupoid in algebraic
spaces whose vertex is a cokernel of the underlying morphism. -/
def liftedCokernelCofork (hqc : c.pt.IsQuasicoherentOnSite) : CokernelCofork φ :=
  CokernelCofork.ofπ (f := φ)
    (show Q ⟶ cokernelModule φ c hc hqc from
      { hom := Cofork.π c, comm := (cokernelTransition_π φ c hc).symm })
    (by
      apply QuasicoherentModule.Hom.ext
      rw [comp_hom, hom_zero]
      exact CokernelCofork.condition c)

/-- The vertex of `liftedCokernelCofork` is `cokernelModule`. -/
@[simp]
theorem liftedCokernelCofork_pt (hqc : c.pt.IsQuasicoherentOnSite) :
    (liftedCokernelCofork φ c hc hqc).pt = cokernelModule φ c hc hqc :=
  rfl

/-- The underlying morphism of the projection of `liftedCokernelCofork` is the projection of
the cokernel cofork of the underlying morphism. -/
@[simp]
theorem liftedCokernelCofork_π (hqc : c.pt.IsQuasicoherentOnSite) :
    (Cofork.π (liftedCokernelCofork φ c hc hqc)).hom = Cofork.π c :=
  rfl

/-- The morphism of quasi-coherent modules out of the cokernel induced by a cofork: the induced
morphism of the underlying modules, which is compatible with the transition morphisms. -/
def cokernelDesc (hqc : c.pt.IsQuasicoherentOnSite) (E : CokernelCofork φ) :
    cokernelModule φ c hc hqc ⟶ E.pt where
  hom := hc.desc (forgetCofork φ E)
  comm := cokernelTransition_comp φ c hc E _ (Cofork.IsColimit.π_desc hc)

/-- The underlying morphism of `cokernelDesc` is the morphism induced on the cokernel of the
underlying morphism by the forgotten cofork. -/
@[simp]
theorem cokernelDesc_hom (hqc : c.pt.IsQuasicoherentOnSite) (E : CokernelCofork φ) :
    (cokernelDesc φ c hc hqc E).hom = hc.desc (forgetCofork φ E) :=
  rfl

/-- The cofork of `AlgebraicGeometry.Space.QuasicoherentModule.liftedCokernelCofork` is a
colimit: a morphism out of it is a morphism out of the cokernel of the underlying morphism, and
such a morphism is compatible with the transitions because it is after the projection. -/
def liftedCokernelCoforkIsColimit (hqc : c.pt.IsQuasicoherentOnSite) :
    IsColimit (liftedCokernelCofork φ c hc hqc) :=
  Cofork.IsColimit.mk _ (fun E => cokernelDesc φ c hc hqc E)
    (fun E => QuasicoherentModule.Hom.ext (Cofork.IsColimit.π_desc (t := forgetCofork φ E) hc))
    (fun E m hm => by
      refine QuasicoherentModule.Hom.ext (Cofork.IsColimit.hom_ext hc ?_)
      change Cofork.π c ≫ m.hom = Cofork.π c ≫ hc.desc (forgetCofork φ E)
      rw [Cofork.IsColimit.π_desc hc]
      exact congrArg QuasicoherentModule.Hom.hom hm)

end Cokernel

section Abelian

open GroupoidInAlgebraicSpaces

/-- A diagram of quasi-coherent modules on a groupoid in algebraic spaces has a limit as soon as
the limit of its underlying modules is quasi-coherent and the three inverse images that the
cocycle and unit conditions are read along preserve it. -/
theorem hasLimit_of_forget {J : Type w} [Category.{w'} J] (D : J ⥤ QuasicoherentModule B S hS G)
    [HasLimit (D ⋙ QuasicoherentModule.forget G)]
    [PreservesLimit (D ⋙ QuasicoherentModule.forget G) (modulePullback B S hS G.source)]
    [PreservesLimit (D ⋙ QuasicoherentModule.forget G)
      (modulePullback B S hS (G.comp ≫ G.source))]
    [PreservesLimit (D ⋙ QuasicoherentModule.forget G)
      (modulePullback B S hS (identityArrow G ≫ G.source))]
    (hqc : (limit (D ⋙ QuasicoherentModule.forget G)).IsQuasicoherentOnSite) : HasLimit D :=
  ⟨⟨liftedLimitCone D _ (limit.isLimit _) hqc,
    liftedLimitConeIsLimit D _ (limit.isLimit _) hqc⟩⟩

/-- A morphism of quasi-coherent modules on a groupoid in algebraic spaces whose underlying
morphism of `𝒪_U`-modules is invertible is itself invertible: the inverse of the underlying
morphism is again compatible with the transition morphisms. -/
instance forget_reflectsIsomorphisms :
    (QuasicoherentModule.forget G).ReflectsIsomorphisms where
  reflects {M N} f _ := by
    have hiso : IsIso f.hom := ‹IsIso ((QuasicoherentModule.forget G).map f)›
    have h : (modulePullback B S hS G.target).map f.hom ≫ N.alpha ≫
        (modulePullback B S hS G.source).map (inv f.hom) =
        (modulePullback B S hS G.target).map f.hom ≫
          (modulePullback B S hS G.target).map (inv f.hom) ≫ M.alpha := by
      rw [← Category.assoc, ← f.comm, Category.assoc, ← Functor.map_comp, IsIso.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.comp_id, ← Category.assoc,
        ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
    exact ⟨{ hom := inv f.hom, comm := (cancel_epi _).1 h },
      QuasicoherentModule.Hom.ext (by simp), QuasicoherentModule.Hom.ext (by simp)⟩

/-- The forgetful functor preserves the limits that it lifts: the underlying cone of the lifted
limit cone is the limit cone it was lifted from. -/
theorem preservesLimit_forget {J : Type w} [Category.{w'} J]
    (D : J ⥤ QuasicoherentModule B S hS G) (c : Cone (D ⋙ QuasicoherentModule.forget G))
    (hc : IsLimit c)
    [PreservesLimit (D ⋙ QuasicoherentModule.forget G) (modulePullback B S hS G.source)]
    [PreservesLimit (D ⋙ QuasicoherentModule.forget G)
      (modulePullback B S hS (G.comp ≫ G.source))]
    [PreservesLimit (D ⋙ QuasicoherentModule.forget G)
      (modulePullback B S hS (identityArrow G ≫ G.source))]
    (hqc : c.pt.IsQuasicoherentOnSite) :
    PreservesLimit D (QuasicoherentModule.forget G) :=
  preservesLimit_of_preserves_limit_cone (liftedLimitConeIsLimit D c hc hqc)
    (IsLimit.ofIsoLimit hc (Cone.ext (Iso.refl _) (fun j => by simp)))

/-- The forgetful functor preserves the cokernels it lifts: the underlying cofork of the lifted
cokernel cofork is the cokernel cofork it was lifted from. -/
theorem preservesColimit_forget {M N : QuasicoherentModule B S hS G} (φ : M ⟶ N)
    (hqc : (cokernel (QuasicoherentModule.Hom.hom φ)).IsQuasicoherentOnSite) :
    PreservesColimit (parallelPair φ 0) (QuasicoherentModule.forget G) :=
  preservesColimit_of_preserves_colimit_cocone
    (liftedCokernelCoforkIsColimit φ _ (cokernelIsCokernel _) hqc)
    ((isColimitMapCoconeCoforkEquiv' (QuasicoherentModule.forget G)
      (CokernelCofork.condition
        (liftedCokernelCofork φ _ (cokernelIsCokernel _) hqc))).symm
      (cokernelIsCokernel (QuasicoherentModule.Hom.hom φ)))

variable (G) in
/-- The kernel of the underlying morphism of a morphism of quasi-coherent modules on a groupoid
in algebraic spaces is quasi-coherent, by the kernel clause of Stacks 03M1(3). -/
theorem isQuasicoherentOnSite_limit_parallelPair
    [ObjectProperty.IsClosedUnderKernels (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS G.objects.1 G.objects.2).O)))]
    {M N : QuasicoherentModule B S hS G} (φ : M ⟶ N) :
    (limit (parallelPair φ 0 ⋙ QuasicoherentModule.forget G)).IsQuasicoherentOnSite := by
  have hiso : limit (parallelPair φ 0 ⋙ QuasicoherentModule.forget G) ≅
      kernel (QuasicoherentModule.Hom.hom φ) :=
    HasLimit.isoOfNatIso (diagramIsoParallelPair _)
  exact (SheafOfModules.isQuasicoherentOnSite _).prop_of_iso hiso.symm
    ((SheafOfModules.isQuasicoherentOnSite _).prop_kernel _ M.F.property N.F.property)

variable (G) in
/-- **Kernels of quasi-coherent modules on a groupoid in algebraic spaces.**  The kernel is the
kernel of the underlying morphism, which is quasi-coherent by Stacks 03M1(3) and carries a
transition morphism because the inverse images along `s`, along `c ≫ s` and along `e ≫ s`
are left exact — which is what flatness of the source and the target supplies. -/
theorem hasKernels_of_closure
    [ObjectProperty.IsClosedUnderKernels (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS G.objects.1 G.objects.2).O)))]
    [PreservesFiniteLimits (modulePullback B S hS G.source)]
    [PreservesFiniteLimits (modulePullback B S hS (G.comp ≫ G.source))]
    [PreservesFiniteLimits (modulePullback B S hS (identityArrow G ≫ G.source))] :
    HasKernels (QuasicoherentModule B S hS G) where
  has_limit φ :=
    hasLimit_of_forget (parallelPair φ 0) (isQuasicoherentOnSite_limit_parallelPair G φ)

variable (G) in
/-- **Cokernels of quasi-coherent modules on a groupoid in algebraic spaces.**  The cokernel is
the cokernel of the underlying morphism, which is quasi-coherent by Stacks 03M1(3); no flatness
is needed, because every inverse image of `𝒪`-modules is a left adjoint and so right exact. -/
theorem hasCokernels_of_closure
    [ObjectProperty.IsClosedUnderCokernels (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS G.objects.1 G.objects.2).O)))] :
    HasCokernels (QuasicoherentModule B S hS G) where
  has_colimit {M N} φ :=
    ⟨⟨liftedCokernelCofork φ _ (cokernelIsCokernel _)
        ((SheafOfModules.isQuasicoherentOnSite _).prop_cokernel _ M.F.property N.F.property),
      liftedCokernelCoforkIsColimit φ _ (cokernelIsCokernel _) _⟩⟩

variable (G) in
/-- **Finite products of quasi-coherent modules on a groupoid in algebraic spaces.**  A finite
product is the product of the underlying modules: it is quasi-coherent unconditionally, and
every inverse image of `𝒪`-modules preserves it, being additive. -/
theorem hasFiniteProducts :
    HasFiniteProducts (QuasicoherentModule B S hS G) where
  out _n :=
    { has_limit := fun D => hasLimit_of_forget D
        ((SheafOfModules.isQuasicoherentOnSite _).prop_limit
          (D ⋙ QuasicoherentModule.forget G) fun j => (D.obj j).F.property) }

variable (G) in
/-- **Stacks 06VZ.**  If the source and the target of a groupoid in algebraic spaces
`(U, R, s, t, c)` over `A` are flat, the quasi-coherent modules on it form an abelian category.

Kernels and cokernels are computed on the underlying `𝒪_U`-modules, which are quasi-coherent by
the kernel and cokernel clauses of Stacks 03M1(3).  A transition morphism is carried along a
cokernel because an inverse image of `𝒪`-modules is a left adjoint, and along a kernel because
the inverse images along `s`, along `c ≫ s` and along `e ≫ s` are left exact: `s` is flat,
`c` is a base change of `s` by Stacks 043Z, and `e ≫ s` is the identity.  The flatness of `t` is
not used, being equivalent to that of `s` in a groupoid. -/
@[stacks 06VZ, instance_reducible]
noncomputable def abelian_of_closure (hs : IsFlat B S hS G.source.hom)
    (_ht : IsFlat B S hS G.target.hom) :
    Abelian (QuasicoherentModule B S hS G) := by
  letI := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS G.objects.1 G.objects.2
  letI := isClosedUnderCokernels_quasicoherentSheaves B S hS G.objects.1 G.objects.2
  have hc : IsFlat B S hS G.comp.hom :=
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback (Space.isPullback_comp_source G).flip hs
  haveI := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS G.source hs
  haveI := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS (G.comp ≫ G.source)
    (isFlat_comp B S hS (AlgebraicSpaces.fiberProduct B S hS G.source G.target).2 G.arrows.2
      G.objects.2 G.comp.hom G.source.hom hc hs)
  haveI := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS (identityArrow G ≫ G.source)
    (by
      rw [identityArrow_comp_source]
      exact isFlat_id B S hS G.objects.2)
  letI := hasKernels_of_closure G
  letI := hasCokernels_of_closure G
  letI := hasFiniteProducts G
  letI : ∀ {M N : QuasicoherentModule B S hS G} (f : M ⟶ N),
      PreservesLimit (parallelPair f 0) (QuasicoherentModule.forget G) := fun f =>
    preservesLimit_forget (parallelPair f 0) _ (limit.isLimit _)
      (isQuasicoherentOnSite_limit_parallelPair G f)
  letI : ∀ {M N : QuasicoherentModule B S hS G} (f : M ⟶ N),
      PreservesColimit (parallelPair f 0) (QuasicoherentModule.forget G) := fun {M N} f =>
    preservesColimit_forget f
      ((SheafOfModules.isQuasicoherentOnSite _).prop_cokernel _ M.F.property N.F.property)
  letI : ∀ {M N : QuasicoherentModule B S hS G} (f : M ⟶ N),
      IsIso (Abelian.coimageImageComparison f) := fun f => by
    have : IsIso ((QuasicoherentModule.forget G).map (Abelian.coimageImageComparison f)) :=
      (Arrow.isIso_iff_isIso_of_isIso
        (Abelian.PreservesCoimageImageComparison.iso (QuasicoherentModule.forget G) f).hom).2
        inferInstance
    exact isIso_of_reflects_iso (Abelian.coimageImageComparison f)
      (QuasicoherentModule.forget G)
  exact Abelian.ofCoimageImageComparisonIsIso

end Abelian

end QuasicoherentModule

end AlgebraicGeometry.Space

end
