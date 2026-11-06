module

public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Sites.Point.Monoidal
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleStalkDecomposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.CoefficientHypotheses
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Coefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceConstruction

/-!
# Tensor products and inverse images of sheaves of `Λ`-modules on small étale sites

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site and let `Λ` be a
commutative ring. The direct image with compact support of sheaves of `Λ`-modules,
`AlgebraicGeometry.SmallEtale.fShriekMod`, is available, as is its stalk decomposition
`(f_!F)_ȳ ≅ ⊕_{f(x̄) = ȳ} F_x̄`. This file assembles the remaining vocabulary in which the
projection formula of [Stacks, Tag 0GKF] is phrased — the tensor product `⊗_Λ` of sheaves of
`Λ`-modules, the inverse image `f^{-1}` of sheaves of `Λ`-modules, and the behaviour of both on
stalks — and carries out the stalk computation that formula rests on: the stalk of
`f_!F ⊗_Λ G` at a geometric point `ȳ` of `Y` is canonically the stalk of
`f_!(F ⊗_Λ f^{-1}G)` there.

The one construction this does *not* contain is the comparison map of sheaves itself, so the
projection formula is not proved. See the implementation notes.

## Main definitions

* `Stacks.ModuleCatLift.moduleSmulHom`, `Stacks.ModuleCatLift.presheafModuleSmul` and
  `Stacks.ModuleCatLift.moduleSheafSmul` — multiplication by a scalar `a : Λ` on a `Λ`-module,
  on a presheaf of `Λ`-modules and on a sheaf of `Λ`-modules, as a morphism in the respective
  category of `Λ`-modules. For a commutative ring these are `Λ`-linear, so unlike
  `Stacks.ModuleCatLift.sheafScalarEnd` they are morphisms of sheaves of `Λ`-modules and not
  merely of the underlying abelian sheaves.
* `AlgebraicGeometry.SmallEtale.modPullback` — the inverse image `f^{-1}` of sheaves of
  `Λ`-modules on the small étale sites, with its adjunction
  `AlgebraicGeometry.SmallEtale.modPullbackAdjunction`.
* `AlgebraicGeometry.SmallEtale.modStalkFunctor` — the stalk at a geometric point of a sheaf of
  `Λ`-modules, as the fibre of the point of the site with coefficients in `Λ`-modules.
* `AlgebraicGeometry.SmallEtale.moduleSheafMonoidal` — the tensor product `⊗_Λ` of sheaves of
  `Λ`-modules on a small étale site: the monoidal structure of
  `CategoryTheory.Sheaf.monoidalCategory`, the sheafification of `V ↦ F(V) ⊗_Λ G(V)`.

## Main results

* `Stacks.ModuleCatLift.valueLiftSheafFiberIso` and
  `Stacks.ModuleCatLift.valueLiftSheafFiberNatIso` — **the two `Λ`-module structures on a stalk
  agree.** The stalk of a sheaf of `Λ`-modules can be formed either as the fibre of the point of
  the site with coefficients in `Λ`-modules, or as the abelian fibre with the `Λ`-action obtained
  from functoriality (`Stacks.ModuleCatLift.valueLift`); the canonical comparison between them
  is an isomorphism of `Λ`-modules, naturally in the sheaf. This is what lets the stalk
  decomposition of `f_!` be used together with results stated for the fibre functor.
* `AlgebraicGeometry.SmallEtale.modShriekStalkIso` — the stalk decomposition
  `(f_!F)_ȳ ≅ ⊕_{f(x̄) = ȳ} F_x̄` of sheaves of `Λ`-modules, in the fibre-functor form of the
  stalk.
* `AlgebraicGeometry.SmallEtale.modPullbackStalkIso` — the stalk of `f^{-1}G` at `x̄` is the
  stalk of `G` at the image of `x̄`; this is Stacks 03Q1 at these coefficients.
* `AlgebraicGeometry.SmallEtale.modStalkTensorIso` — the stalk of a tensor product is the tensor
  product of the stalks, `(F ⊗_Λ G)_x̄ ≅ F_x̄ ⊗_Λ G_x̄`.
* `AlgebraicGeometry.SmallEtale.modShriekTensorStalkIso` and
  `AlgebraicGeometry.SmallEtale.modShriekPullbackTensorStalkIso` — the two sides of the
  projection formula, on the stalk at a geometric point `ȳ` of `Y`: the left-hand side
  `f_!F ⊗_Λ G` has stalk `(⊕_{f(x̄) = ȳ} F_x̄) ⊗_Λ G_ȳ`, and the right-hand side
  `f_!(F ⊗_Λ f^{-1}G)` has stalk `⊕_{f(x̄) = ȳ} (F ⊗_Λ f^{-1}G)_x̄`.
* `AlgebraicGeometry.SmallEtale.modFiberStalksTensorIso` — tensoring distributes over the direct
  sum of stalks over the geometric fibre,
  `(⊕_{f(x̄) = ȳ} F_x̄) ⊗_Λ N ≅ ⊕_{f(x̄) = ȳ} (F_x̄ ⊗_Λ N)`.
* `AlgebraicGeometry.SmallEtale.modShriekProjectionStalkIso` — **the stalk computation behind
  the projection formula.** For a locally quasi-finite `f`, the stalk of `f_!F ⊗_Λ G` at a
  geometric point `ȳ` of `Y` is canonically the stalk of `f_!(F ⊗_Λ f^{-1}G)` there. This
  composes the stalk decomposition of `f_!`, the distributivity above, monoidality of the stalk
  functor and Stacks 03Q1.

## Implementation notes

**What is not here.** No `stacks` attribute appears in this file, and in particular there is no
0GKF attribute: the projection formula of [Stacks, Tag 0GKF] is *not* proved here, because its
comparison map `can : f_!F ⊗_Λ G ⟶ f_!(F ⊗_Λ f^{-1}G)` of sheaves is not constructed. The
source builds that map at the level of *presheaves*, on the finite-support direct image `f_{p!}`
of Stacks 0F6E whose sections over `V` are the sections of `F` on `X_V` supported on a locally
closed `Z ⊂ X_V` finite over `V`: a pure tensor `(Z, s) ⊗ t` goes to `(Z, s ⊗ f^{-1}t)`, which
has the same support, and sheafifying gives the map.

The map `can` is `AlgebraicGeometry.SmallEtale.modFShriekProjectionMap` of
`StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleProjectionMap`, and
`AlgebraicGeometry.SmallEtale.modFShriekProjectionIso` of
`StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleProjectionIso` carries the 0GKF attribute for
the resulting isomorphism.

What *is* carried out here is the other half of the source's proof, the computation on stalks:
`modShriekProjectionStalkIso` identifies the stalks of the two sheaves at every geometric point
of `Y`, through the chain the source uses. This does not by itself make the two sheaves
isomorphic — an isomorphism of all stalks which is not known to be induced by a morphism of
sheaves gives no morphism of sheaves — so it is a proper part of 0GKF and not 0GKF, and the
attribute sits on the file which produces `can` and checks that the isomorphism below is the one
`can` induces on stalks.

**The transport along the geometric fibre.** A point `x̄` of the geometric fibre above `ȳ`
satisfies `f(x̄) = ȳ` on the nose only after `AlgebraicGeometry.SmallEtale.toGeometricPoint_map`,
an equality of geometric points; `stalkPullbackFiberIso` transports along it with `eqToIso`, the
same idiom as the abelian
`AlgebraicGeometry.SmallEtale.fiberPointPullbackStalkIso` it is modelled on.

**Two stalks.** The `Λ`-module stalk of
`StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleStalkDecomposition` is the abelian stalk with
the `Λ`-action read off from functoriality, which is what makes the decomposition of Stacks 0F5F
transport with no comparison of colimits; the stalk appearing in Stacks 03Q1 for arbitrary
coefficients, and in the monoidality of the fibre functor, is the colimit formed in `Λ`-modules.
`valueLiftSheafFiberIso` identifies them. Its `Λ`-linearity is naturality of
`CategoryTheory.GrothendieckTopology.Point.sheafFiberCompIso` applied to the endomorphism
"multiplication by `a`" *of the sheaf of `Λ`-modules* — which exists because `Λ` is commutative,
and is the reason `moduleSheafSmul` is introduced alongside the existing `sheafScalarEnd`.

**The coefficient universe.** The tensor product of sheaves of `Λ`-modules needs a monoidal
structure on the coefficient category `ModuleCat.{max (u + 1) v} Λ`, and Mathlib equips
`ModuleCat.{w} Λ` with one only for `Λ : Type w`. So the sections on the tensor product carry
`Λ` in the coefficient universe `max (u + 1) v` of the small étale site, as they do in
`AlgebraicGeometry.smallEtaleSheafPullbackTensorIso`. Everything not mentioning the tensor
product is stated for `Λ` in an arbitrary universe.

## References

* [Stacks Project, Tag 0GKF](https://stacks.math.columbia.edu/tag/0GKF)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
* [Stacks Project, Tag 0F6R](https://stacks.math.columbia.edu/tag/0F6R)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry
open scoped DirectSum

namespace Stacks.ModuleCatLift

universe w w' r u₁ v₁

variable (Λ : Type r) [CommRing Λ]

/-- **Multiplication by a scalar on a `Λ`-module, as a morphism of `Λ`-modules.** Unlike
`CategoryTheory.ModuleCat.smul`, which is an endomorphism of the underlying abelian group, this
is a morphism in `ModuleCat Λ`; it is `Λ`-linear because `Λ` is commutative. -/
public def moduleSmulHom (M : ModuleCat.{w} Λ) (a : Λ) : M ⟶ M :=
  ModuleCat.homMk (M.smul a).asHom fun c => by
    rw [← End.mul_asHom, ← End.mul_asHom, ← map_mul, ← map_mul, mul_comm]

/-- The underlying map of abelian groups of `moduleSmulHom Λ M a` is multiplication by `a`. -/
@[simp]
public lemma forget₂_map_moduleSmulHom (M : ModuleCat.{w} Λ) (a : Λ) :
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).map (moduleSmulHom.{w} Λ M a) =
      (M.smul a).asHom :=
  rfl

/-- Every morphism of `Λ`-modules commutes with multiplication by a scalar. -/
public lemma moduleSmulHom_naturality {M N : ModuleCat.{w} Λ} (g : M ⟶ N) (a : Λ) :
    g ≫ moduleSmulHom.{w} Λ N a = moduleSmulHom.{w} Λ M a ≫ g :=
  (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).map_injective (by
    rw [Functor.map_comp, Functor.map_comp, forget₂_map_moduleSmulHom,
      forget₂_map_moduleSmulHom]
    exact ModuleCat.smul_naturality g a)

/-- **Multiplication by a scalar on a presheaf of `Λ`-modules**, as an endomorphism of that
presheaf: the restriction maps are `Λ`-linear, which is its naturality. -/
public def presheafModuleSmul {K : Type u₁} [Category.{v₁} K] (P : K ⥤ ModuleCat.{w} Λ)
    (a : Λ) : P ⟶ P where
  app U := moduleSmulHom.{w} Λ (P.obj U) a
  naturality _ _ g := moduleSmulHom_naturality.{w} Λ (P.map g) a

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)

/-- **Multiplication by a scalar on a sheaf of `Λ`-modules**, as an endomorphism of that sheaf
of `Λ`-modules. -/
public def moduleSheafSmul (F : Sheaf J (ModuleCat.{w} Λ)) (a : Λ) : F ⟶ F :=
  ObjectProperty.homMk (presheafModuleSmul.{w} Λ F.obj a)

/-- The fibre functor on presheaves of `Λ`-modules is `Λ`-linear: it carries multiplication by
`a` on a presheaf to multiplication by `a` on the fibre. Both maps agree after composing with
every germ map, the germ maps being `Λ`-linear. -/
public lemma presheafFiber_map_presheafModuleSmul (Φ : J.Point.{w'})
    [HasColimitsOfSize.{w', w'} (ModuleCat.{w} Λ)] (P : Cᵒᵖ ⥤ ModuleCat.{w} Λ) (a : Λ) :
    (Φ.presheafFiber (A := ModuleCat.{w} Λ)).map (presheafModuleSmul.{w} Λ P a) =
      moduleSmulHom.{w} Λ ((Φ.presheafFiber (A := ModuleCat.{w} Λ)).obj P) a := by
  refine Φ.presheafFiber_hom_ext fun X x => ?_
  rw [Φ.toPresheafFiber_naturality]
  exact (moduleSmulHom_naturality.{w} Λ (Φ.toPresheafFiber X x P) a).symm

/-- The fibre functor on sheaves of `Λ`-modules is `Λ`-linear. -/
public lemma sheafFiber_map_moduleSheafSmul (Φ : J.Point.{w'})
    [HasColimitsOfSize.{w', w'} (ModuleCat.{w} Λ)] (F : Sheaf J (ModuleCat.{w} Λ)) (a : Λ) :
    (Φ.sheafFiber (A := ModuleCat.{w} Λ)).map (moduleSheafSmul.{w} Λ J F a) =
      moduleSmulHom.{w} Λ ((Φ.sheafFiber (A := ModuleCat.{w} Λ)).obj F) a :=
  presheafFiber_map_presheafModuleSmul Λ J Φ F.obj a

variable [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- Multiplication by a scalar on a sheaf of `Λ`-modules induces multiplication by that scalar
on the underlying abelian sheaf. -/
public lemma sheafCompose_map_moduleSheafSmul (F : Sheaf J (ModuleCat.{w} Λ)) (a : Λ) :
    (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
      (moduleSheafSmul.{w} Λ J F a) = (sheafScalarEnd Λ J F a).asHom :=
  rfl

variable (Φ : J.Point.{w'}) [LocallySmall.{w'} C]
  [HasColimitsOfSize.{w', w'} (ModuleCat.{w} Λ)]
  [HasColimitsOfSize.{w', w'} AddCommGrpCat.{w}]
  [PreservesFilteredColimitsOfSize.{w', w'}
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- **The two `Λ`-module structures on a stalk agree.** The abelian fibre of a sheaf of
`Λ`-modules with the `Λ`-action obtained from functoriality is the fibre formed in `Λ`-modules:
the canonical comparison of the two colimits is `Λ`-linear, its `Λ`-linearity being naturality
of `CategoryTheory.GrothendieckTopology.Point.sheafFiberCompIso` applied to multiplication by a
scalar on the sheaf of `Λ`-modules. -/
public def valueLiftSheafFiberIso (F : Sheaf J (ModuleCat.{w} Λ)) :
    (valueLift.{w} Λ J (Φ.sheafFiber (A := AddCommGrpCat.{w}))).obj F ≅
      (Φ.sheafFiber (A := ModuleCat.{w} Λ)).obj F :=
  ModuleCat.isoMk ((Φ.sheafFiberCompIso (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).app F)
    fun a => by
      have h := (Φ.sheafFiberCompIso
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).hom.naturality
          (moduleSheafSmul.{w} Λ J F a)
      simp only [Functor.comp_map] at h
      rw [sheafFiber_map_moduleSheafSmul, sheafCompose_map_moduleSheafSmul,
        forget₂_map_moduleSmulHom] at h
      exact h.symm

/-- The underlying map of abelian groups of the comparison of the two `Λ`-module structures on
a stalk is the canonical comparison of the two colimits. -/
@[simp]
public lemma forget₂_map_valueLiftSheafFiberIso_hom (F : Sheaf J (ModuleCat.{w} Λ)) :
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).map
        (valueLiftSheafFiberIso.{w} Λ J Φ F).hom =
      (Φ.sheafFiberCompIso (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).hom.app F :=
  rfl

/-- **The two `Λ`-module structures on a stalk agree, naturally in the sheaf.** -/
public def valueLiftSheafFiberNatIso :
    valueLift.{w} Λ J (Φ.sheafFiber (A := AddCommGrpCat.{w})) ≅
      Φ.sheafFiber (A := ModuleCat.{w} Λ) :=
  NatIso.ofComponents (fun F => valueLiftSheafFiberIso.{w} Λ J Φ F) fun {F G} φ =>
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).map_injective (by
      rw [Functor.map_comp, Functor.map_comp, forget₂_map_valueLiftSheafFiberIso_hom,
        forget₂_map_valueLiftSheafFiberIso_hom]
      exact (Φ.sheafFiberCompIso
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).hom.naturality φ)

end Stacks.ModuleCatLift

namespace AlgebraicGeometry.SmallEtale

universe u v r

attribute [local instance] SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat

section Vocabulary

variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ] {X Y : B.Scheme} (f : X ⟶ Y)

/-- **The inverse image `f^{-1}` of sheaves of `Λ`-modules on the small étale sites** along a
morphism of a big étale site: the sheaf pullback along small étale base change. This is the
`Λ`-linear companion of `AlgebraicGeometry.SmallEtale.abPullback`. -/
public def modPullback : ModuleSheaf.{u, v, r} B Y Λ ⥤ ModuleSheaf.{u, v, r} B X Λ :=
  (smallEtaleBaseChange B f).sheafPullback (ModuleCat.{max (u + 1) v r} Λ)
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)

/-- The inverse image of sheaves of `Λ`-modules is left adjoint to the direct image. -/
public def modPullbackAdjunction :
    modPullback.{u, v, r} B Λ f ⊣
      (smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{max (u + 1) v r} Λ)
        (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property) :=
  (smallEtaleBaseChange B f).sheafAdjunctionContinuous (ModuleCat.{max (u + 1) v r} Λ)
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)

/-- **The stalk at a geometric point of a sheaf of `Λ`-modules**, formed as the fibre of the
point of the small étale site with coefficients in `Λ`-modules. -/
public abbrev modStalkFunctor (S : B.Scheme) (s : GeometricPoint S.obj) :
    ModuleSheaf.{u, v, r} B S Λ ⥤ ModuleCat.{max (u + 1) v r} Λ :=
  (geometricPointSitePoint B S.obj S.property s).sheafFiber

/-- **Stacks 03Q1 for these coefficients.** The stalk of the inverse image `f^{-1}G` at a
geometric point `x̄` of `X` is the stalk of `G` at the image of `x̄`, naturally in `G`. -/
public def modPullbackStalkIso (x : GeometricPoint X.obj) :
    modPullback.{u, v, r} B Λ f ⋙ modStalkFunctor.{u, v, r} B Λ X x ≅
      modStalkFunctor.{u, v, r} B Λ Y (x.map (B.inclusion.map f)) := by
  letI : HasProducts.{u} (ModuleCat.{max (u + 1) v r} Λ) :=
    fun _ => ModuleCat.hasLimitsOfShape
  exact smallEtalePullbackSheafFiberIso B f x (ModuleCat.{max (u + 1) v r} Λ)

/-- **The two `Λ`-module structures on an étale stalk agree.** The stalk of
`StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleStalkDecomposition`, the abelian étale stalk
with the `Λ`-action from functoriality, is the fibre formed in `Λ`-modules. -/
public def moduleEtaleStalkIso (S : B.Scheme) (s : GeometricPoint S.obj) :
    moduleEtaleStalkFunctor.{u, v, r} B Λ S s ≅ modStalkFunctor.{u, v, r} B Λ S s := by
  letI : PreservesColimits
      (forget₂ (ModuleCat.{max (u + 1) v r} Λ) AddCommGrpCat.{max (u + 1) v r}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max (u + 1) v r, r,
      max (u + 1) v r, max (u + 1) v r} Λ
  letI : PreservesColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{max (u + 1) v r} Λ) AddCommGrpCat.{max (u + 1) v r}) :=
    preservesColimitsOfSize_shrink.{u, max (u + 1) v r, u, max (u + 1) v r} _
  letI : PreservesFilteredColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{max (u + 1) v r} Λ) AddCommGrpCat.{max (u + 1) v r}) :=
    ⟨fun _ => inferInstance⟩
  exact Stacks.ModuleCatLift.valueLiftSheafFiberNatIso.{max (u + 1) v r} Λ
    (SmallEtale.topology B S.obj S.property) (geometricPointSitePoint B S.obj S.property s)

variable [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- **The stalk decomposition of the direct image with compact support of sheaves of
`Λ`-modules**, in the fibre-functor form of the stalk: `(f_!F)_ȳ ≅ ⊕_{f(x̄) = ȳ} F_x̄` as
`Λ`-modules, naturally in `F`. This is the decomposition
`AlgebraicGeometry.SmallEtale.moduleFShriekStalkNatIso` of the `Λ`-module form of Stacks 0F5F,
transported along `moduleEtaleStalkIso`. -/
public def modShriekStalkIso (s : GeometricPoint Y.obj) :
    fShriekMod.{u, v, r} B Λ f ⋙ modStalkFunctor.{u, v, r} B Λ Y s ≅
      moduleFiberStalks.{u, v, r} B Λ f s :=
  Functor.isoWhiskerLeft (fShriekMod.{u, v, r} B Λ f)
      (moduleEtaleStalkIso.{u, v, r} B Λ Y s).symm ≪≫
    moduleFShriekStalkNatIso.{u, v, r} B Λ f s

/-- **The direct sum of the fibre-functor stalks over the geometric fibre**, the `Λ`-module
`⊕_{f(x̄) = ȳ} F_x̄` with the stalks formed as fibres of points of the site with coefficients in
`Λ`-modules. -/
public abbrev modFiberStalks (s : GeometricPoint Y.obj) (F : ModuleSheaf.{u, v, r} B X Λ) :
    ModuleCat.{max (u + 1) v r} Λ :=
  ModuleCat.of Λ (⨁ x : GeometricFiberPoint B f s,
    ((modStalkFunctor.{u, v, r} B Λ X (x.toGeometricPoint B f s)).obj F : Type _))

/-- `AlgebraicGeometry.SmallEtale.moduleFiberStalks` is the direct sum of the fibre-functor
stalks: the two differ only in which of the two equal `Λ`-module structures on a stalk each
summand carries, and `moduleEtaleStalkIso` identifies those. -/
public def moduleFiberStalksIso (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, r} B X Λ) :
    (moduleFiberStalks.{u, v, r} B Λ f s).obj F ≅ modFiberStalks.{u, v, r} B Λ f s F :=
  (DirectSum.congrLinearEquiv (R := Λ)
    (N := fun x : GeometricFiberPoint B f s =>
      ((moduleEtaleStalkFunctor.{u, v, r} B Λ X (x.toGeometricPoint B f s)).obj F : Type _))
    (P := fun x : GeometricFiberPoint B f s =>
      ((modStalkFunctor.{u, v, r} B Λ X (x.toGeometricPoint B f s)).obj F : Type _))
    fun x =>
      ((moduleEtaleStalkIso.{u, v, r} B Λ X (x.toGeometricPoint B f s)).app F).toLinearEquiv
      ).toModuleIso

end Vocabulary

section Tensor

variable (B : BigEtaleSite.{u}) (Λ : Type (max (u + 1) v)) [CommRing Λ]
  {X Y : B.Scheme} (f : X ⟶ Y)

/-- **The tensor product `⊗_Λ` of sheaves of `Λ`-modules on a small étale site.** This is the
monoidal structure of `CategoryTheory.Sheaf.monoidalCategory`: the sheafification of
`V ↦ F(V) ⊗_Λ G(V)`. It is not a global instance, as in Mathlib, so a consumer activates it
with `attribute [local instance]`. -/
@[instance_reducible]
public def moduleSheafMonoidal (S : B.Scheme) :
    MonoidalCategory (ModuleSheaf.{u, v, max (u + 1) v} B S Λ) :=
  Sheaf.monoidalCategory _ _

attribute [local instance] moduleSheafMonoidal

/-- **The stalk functor is monoidal.** The tensor product of `Λ`-modules commutes with the
filtered colimits computing a stalk — tensoring with a fixed module has a right adjoint,
`Λ`-modules being monoidal closed — so the fibre of the point of the site attached to a
geometric point is a monoidal functor. -/
@[instance_reducible]
public def modStalkMonoidal (S : B.Scheme) (s : GeometricPoint S.obj) :
    (modStalkFunctor.{u, v, max (u + 1) v} B Λ S s).Monoidal := by
  letI : HasProducts.{u} (ModuleCat.{max (u + 1) v} Λ) :=
    fun _ => ModuleCat.hasLimitsOfShape
  letI : ∀ M : ModuleCat.{max (u + 1) v} Λ,
      PreservesFilteredColimitsOfSize.{u, u} (tensorLeft M) := fun _ =>
    ⟨fun _ => inferInstance⟩
  letI : ∀ M : ModuleCat.{max (u + 1) v} Λ,
      PreservesFilteredColimitsOfSize.{u, u} (tensorRight M) := fun _ =>
    ⟨fun _ => { preservesColimit := inferInstance }⟩
  infer_instance

attribute [local instance] modStalkMonoidal

/-- **The stalk of a tensor product is the tensor product of the stalks**,
`F_x̄ ⊗_Λ G_x̄ ≅ (F ⊗_Λ G)_x̄`. -/
public def modStalkTensorIso (S : B.Scheme) (s : GeometricPoint S.obj)
    (F G : ModuleSheaf.{u, v, max (u + 1) v} B S Λ) :
    (modStalkFunctor.{u, v, max (u + 1) v} B Λ S s).obj F ⊗
        (modStalkFunctor.{u, v, max (u + 1) v} B Λ S s).obj G ≅
      (modStalkFunctor.{u, v, max (u + 1) v} B Λ S s).obj (F ⊗ G) :=
  Functor.Monoidal.μIso (modStalkFunctor.{u, v, max (u + 1) v} B Λ S s) F G

section Shriek

variable [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- **The left-hand side of the projection formula, on a stalk.** The stalk at a geometric point
`ȳ` of `Y` of `f_!F ⊗_Λ G` is `(⊕_{f(x̄) = ȳ} F_x̄) ⊗_Λ G_ȳ`. -/
public def modShriekTensorStalkIso (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj
        ((fShriekMod.{u, v, max (u + 1) v} B Λ f).obj F ⊗ G) ≅
      (moduleFiberStalks.{u, v, max (u + 1) v} B Λ f s).obj F ⊗
        (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G :=
  (modStalkTensorIso.{u, v} B Λ Y s ((fShriekMod.{u, v, max (u + 1) v} B Λ f).obj F) G).symm ≪≫
    tensorIso ((modShriekStalkIso.{u, v, max (u + 1) v} B Λ f s).app F) (Iso.refl _)

/-- **The right-hand side of the projection formula, on a stalk.** The stalk at a geometric
point `ȳ` of `Y` of `f_!(F ⊗_Λ f^{-1}G)` is `⊕_{f(x̄) = ȳ} (F ⊗_Λ f^{-1}G)_x̄`. -/
public def modShriekPullbackTensorStalkIso (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj
        ((fShriekMod.{u, v, max (u + 1) v} B Λ f).obj
          (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) ≅
      (moduleFiberStalks.{u, v, max (u + 1) v} B Λ f s).obj
        (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G) :=
  (modShriekStalkIso.{u, v, max (u + 1) v} B Λ f s).app
    (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)

end Shriek

/-- **Tensoring distributes over the direct sum of stalks over the geometric fibre**,
`(⊕_{f(x̄) = ȳ} F_x̄) ⊗_Λ N ≅ ⊕_{f(x̄) = ȳ} (F_x̄ ⊗_Λ N)`. This is the lower arrow of the stalk
comparison square of the projection formula. -/
public def modFiberStalksTensorIso (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ) (N : ModuleCat.{max (u + 1) v} Λ) :
    modFiberStalks.{u, v, max (u + 1) v} B Λ f s F ⊗ N ≅
      ModuleCat.of Λ (⨁ x : GeometricFiberPoint B f s,
        (((modStalkFunctor.{u, v, max (u + 1) v} B Λ X
          (x.toGeometricPoint B f s)).obj F ⊗ N : ModuleCat.{max (u + 1) v} Λ) : Type _)) := by
  letI : DecidableEq (GeometricFiberPoint B f s) := Classical.decEq _
  exact (TensorProduct.directSumLeft Λ Λ
    (fun x : GeometricFiberPoint B f s =>
      ((modStalkFunctor.{u, v, max (u + 1) v} B Λ X
        (x.toGeometricPoint B f s)).obj F : Type _))
    ((N : Type _))).toModuleIso

/-- **Stacks 03Q1 above a point of the geometric fibre, with coefficients in `Λ`-modules.** The
stalk of `G` at a geometric point `ȳ` of `Y` is the stalk of `f^{-1}G` at a point `x̄` of the
geometric fibre of `f` above `ȳ`. -/
public def stalkPullbackFiberIso (s : GeometricPoint Y.obj)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (x : GeometricFiberPoint B f s) :
    (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G ≅
      (modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).obj
        ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G) :=
  eqToIso (congrArg (fun t => (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y t).obj G)
      (toGeometricPoint_map B f s x).symm) ≪≫
    ((modPullbackStalkIso.{u, v, max (u + 1) v} B Λ f
      (x.toGeometricPoint B f s)).app G).symm

/-- **The summand of the stalk comparison of the projection formula** indexed by a point `x̄` of
the geometric fibre: `F_x̄ ⊗_Λ G_ȳ ≅ (F ⊗_Λ f^{-1}G)_x̄`. -/
public def stalkFiberSummandIso (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (x : GeometricFiberPoint B f s) :
    (modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).obj F ⊗
        (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G ≅
      (modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).obj
        (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G) :=
  tensorIso (Iso.refl _) (stalkPullbackFiberIso.{u, v} B Λ f s G x) ≪≫
    modStalkTensorIso.{u, v} B Λ X (x.toGeometricPoint B f s) F
      ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)

/-- The summandwise comparison of `stalkFiberSummandIso`, assembled over the geometric fibre:
`⊕_{f(x̄) = ȳ} (F_x̄ ⊗_Λ G_ȳ) ≅ ⊕_{f(x̄) = ȳ} (F ⊗_Λ f^{-1}G)_x̄`. -/
public def modFiberStalksSummandsIso (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    ModuleCat.of Λ (⨁ x : GeometricFiberPoint B f s,
        (((modStalkFunctor.{u, v, max (u + 1) v} B Λ X
          (x.toGeometricPoint B f s)).obj F ⊗
            (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G :
              ModuleCat.{max (u + 1) v} Λ) : Type _)) ≅
      modFiberStalks.{u, v, max (u + 1) v} B Λ f s
        (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G) :=
  (DirectSum.congrLinearEquiv (R := Λ)
    (N := fun x : GeometricFiberPoint B f s =>
      (((modStalkFunctor.{u, v, max (u + 1) v} B Λ X
        (x.toGeometricPoint B f s)).obj F ⊗
          (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G :
            ModuleCat.{max (u + 1) v} Λ) : Type _))
    (P := fun x : GeometricFiberPoint B f s =>
      ((modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).obj
        (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G) : Type _))
    fun x => (stalkFiberSummandIso.{u, v} B Λ f s F G x).toLinearEquiv).toModuleIso

section Shriek2

variable [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- **The stalk computation behind the projection formula.** For a locally quasi-finite `f`, a
commutative ring `Λ`, a sheaf of `Λ`-modules `F` on `X_étale` and a sheaf of `Λ`-modules `G` on
`Y_étale`, the stalk at a geometric point `ȳ` of `Y` of `f_!F ⊗_Λ G` is canonically the stalk of
`f_!(F ⊗_Λ f^{-1}G)` there. The chain is the one of the source: decompose the stalk of `f_!`
into the direct sum over the geometric fibre, distribute the tensor product over that sum, and
on each summand use that the stalk functor is monoidal and that the stalk of `f^{-1}G` above a
point of the fibre is the stalk of `G` at `ȳ`.

This is a part of [Stacks, Tag 0GKF] and not that tag: the comparison map of *sheaves* is not
constructed, and an isomorphism of stalks not known to come from a morphism of sheaves does not
make the two sheaves isomorphic. -/
public def modShriekProjectionStalkIso (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj
        ((fShriekMod.{u, v, max (u + 1) v} B Λ f).obj F ⊗ G) ≅
      (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj
        ((fShriekMod.{u, v, max (u + 1) v} B Λ f).obj
          (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) :=
  modShriekTensorStalkIso.{u, v} B Λ f s F G ≪≫
    tensorIso (moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s F) (Iso.refl _) ≪≫
    modFiberStalksTensorIso.{u, v} B Λ f s F
      ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G) ≪≫
    modFiberStalksSummandsIso.{u, v} B Λ f s F G ≪≫
    (moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s
      (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).symm ≪≫
    (modShriekPullbackTensorStalkIso.{u, v} B Λ f s F G).symm

end Shriek2

end Tensor

end AlgebraicGeometry.SmallEtale

end
