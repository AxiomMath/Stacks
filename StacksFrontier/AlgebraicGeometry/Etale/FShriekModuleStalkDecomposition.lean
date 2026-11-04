module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleLift

/-!
# The stalks of the direct image with compact support with coefficients in a ring

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site, let `ȳ` be a geometric
point of `Y`, let `Λ` be a ring and let `F` be a sheaf of `Λ`-modules on the small étale site of
`X`. The stalk of the `Λ`-linear direct image with compact support `f_!F` at `ȳ` is, as a
`Λ`-module, the direct sum of the stalks of `F` over the geometric points of `X` lying over `ȳ`,
naturally in `F`. This is the `Λ`-module form of the stalk decomposition of Stacks 0F5F.

## Main definitions

* `Stacks.ModuleCatLift.valueLift` — the lift to sheaves of `Λ`-modules of an additive functor
  from abelian sheaves to abelian groups.
* `AlgebraicGeometry.SmallEtale.moduleEtaleStalkFunctor` — the stalk at a geometric point of a
  sheaf of `Λ`-modules on a small étale site, as a `Λ`-module.
* `AlgebraicGeometry.SmallEtale.fiberStalksFunctor` — the direct sum of the stalks over a
  geometric fibre, as a functor on abelian sheaves.
* `AlgebraicGeometry.SmallEtale.moduleFiberStalks` — the `Λ`-module `⊕_{f(x̄) = ȳ} F_x̄`.
* `AlgebraicGeometry.SmallEtale.moduleFShriekStalkIso` — the `Λ`-linear stalk decomposition
  `(f_!F)_ȳ ≅ ⊕_{f(x̄) = ȳ} F_x̄`, and
  `AlgebraicGeometry.SmallEtale.moduleFShriekStalkNatIso` — the same as an isomorphism of
  functors on sheaves of `Λ`-modules.

## Main results

* `AlgebraicGeometry.SmallEtale.moduleFShriekStalkIso_forget₂` — the `Λ`-linear decomposition is
  the canonical one: its underlying map of abelian groups is the decomposition
  `AlgebraicGeometry.SmallEtale.fShriekStalkIso` of Stacks 0F5F. Together with
  `AlgebraicGeometry.SmallEtale.fShriekStalkIso_comp_sheafification` this says that it is the
  germ decomposition of the finite-support direct image.
* `AlgebraicGeometry.SmallEtale.moduleFShriekStalkIso_natural` — the decomposition is natural in
  the sheaf of `Λ`-modules.
* `AlgebraicGeometry.SmallEtale.moduleFiberStalks_smul_apply` — the scalar action on the target
  of the decomposition is summandwise the scalar action on the stalks of `F`, so the target
  really is the direct sum of the `Λ`-module stalks.

## Implementation notes

The `Λ`-module structure on a stalk is the one given by functoriality: multiplication by `a : Λ`
is an endomorphism of the abelian sheaf underlying a sheaf of `Λ`-modules, so an additive functor
on abelian sheaves carries it to an endomorphism of the value of the functor, and `a ↦ (a • ·)`
is a ring map into that endomorphism ring. This is the construction
`Stacks.ModuleCatLift.moduleLift` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLift` with values in abelian groups rather
than in abelian sheaves; it is set up here as `Stacks.ModuleCatLift.valueLift` and applied to the
stalk functor at a geometric point, and to the direct sum of the stalk functors over a geometric
fibre. Both are additive, being built from colimits of restrictions of sheaves.

The point of taking stalks this way, rather than as colimits formed in `ModuleCat Λ`, is that the
underlying abelian group is then *literally* the abelian one — `valueLift` changes nothing but
the scalar action — so the decomposition of Stacks 0F5F transports with no comparison of
colimits at all: the `Λ`-linear isomorphism is `ModuleCat.isoMk` applied to
`AlgebraicGeometry.SmallEtale.fShriekStalkIso`, and the only thing to prove is that it commutes
with the scalar action. That in turn is an instance of the naturality
`AlgebraicGeometry.SmallEtale.fShriekStalkIso_natural` of the abelian decomposition, applied to
the endomorphism "multiplication by `a`" of the underlying abelian sheaf. No `Λ`-module structure
on `AlgebraicGeometry.SmallEtale.supportedSections` and no `Λ`-linear refinement of
`AlgebraicGeometry.SmallEtale.fiberStalksMap` is needed, and nothing in the development of the
finite-support direct image has to be generalised from abelian groups to `Λ`-modules.

The coefficient universe is the cutoff `max (u + 1) v r` at which `f_!` is defined, `u` being the
universe of the schemes, as it is for `AlgebraicGeometry.SmallEtale.fShriekMod`. The lift is
therefore applied with its coefficient universe given explicitly; left implicit it produces the
stuck universe constraint `max (u + 1) ?w = max (u + 1) v r`.

Nothing here carries a `stacks` attribute. The stalk decomposition is the one of Stacks 0F5F with
coefficients in a ring, but 0F5F is already attributed to
`AlgebraicGeometry.SmallEtale.fShriekStalkIso`, of which this is a transport rather than an
independent construction: the underlying map of abelian groups is literally the one 0F5F
produces, and the only thing added is `Λ`-linearity, which is formal. A second attribute would
double-count the tag. Nor is this Stacks 0GKF, the projection formula, to which it is an input.

## References

* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
* [Stacks Project, Tag 0F6R](https://stacks.math.columbia.edu/tag/0F6R)
* [Stacks Project, Tag 04FM](https://stacks.math.columbia.edu/tag/04FM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

namespace Stacks.ModuleCatLift

universe w r t u₁ v₁ u₂ v₂ u₃ v₃

/-- Whiskering on the right by an additive functor, as a map of endomorphism rings. -/
public def whiskerRightEndRingHom {K : Type u₁} [Category.{v₁} K] {A : Type u₂}
    [Category.{v₂} A] [Preadditive A] {Bc : Type u₃} [Category.{v₃} Bc] [Preadditive Bc]
    (P : K ⥤ A) (H : A ⥤ Bc) [H.Additive] : End P →+* End (P ⋙ H) where
  toFun α := Functor.whiskerRight α H
  map_one' := NatTrans.ext (funext fun U => H.map_id (P.obj U))
  map_mul' _ _ := NatTrans.ext (funext fun _ => H.map_comp _ _)
  map_zero' := NatTrans.ext (funext fun _ => H.map_zero _ _)
  map_add' _ _ := NatTrans.ext (funext fun _ => H.map_add)

/-- The fibre functor of a point of a site on presheaves with values in a preadditive category is
additive: it is the colimit of the restriction of a presheaf along the projection from the
category of elements of the fibre, and both restriction and the colimit are additive. -/
public instance additive_presheafFiber {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} (Φ : J.Point.{t}) (A : Type u₂) [Category.{v₂} A]
    [Preadditive A] [HasColimitsOfSize.{t, t} A] :
    (Φ.presheafFiber (A := A)).Additive := by
  change ((Functor.whiskeringLeft _ _ _).obj
    (CategoryOfElements.π Φ.fiber).op ⋙ colim).Additive
  infer_instance

/-- The fibre functor of a point of a site on sheaves with values in a preadditive category is
additive, being the fibre functor on the underlying presheaves. -/
public instance additive_sheafFiber {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} (Φ : J.Point.{t}) (A : Type u₂) [Category.{v₂} A]
    [Preadditive A] [HasColimitsOfSize.{t, t} A] :
    (Φ.sheafFiber (A := A)).Additive := by
  change (sheafToPresheaf J A ⋙ Φ.presheafFiber).Additive
  infer_instance

section Sheaf

variable (Λ : Type r) [Ring Λ] {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- Multiplication by a scalar on the abelian sheaves underlying sheaves of `Λ`-modules, as an
endomorphism of the forgetful functor. This is `Stacks.ModuleCatLift.sheafScalarEnd` assembled
over all sheaves; its naturality is the `Λ`-linearity of a morphism of sheaves of
`Λ`-modules. -/
public def sheafScalarNatEnd :
    Λ →+* End (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})) where
  toFun a :=
    { app := fun F => sheafScalarEnd Λ J F a
      naturality := fun _ _ φ => (sheafScalarEnd_naturality Λ J φ a).symm }
  map_one' := NatTrans.ext (funext fun F => map_one (sheafScalarEnd Λ J F))
  map_mul' a b := NatTrans.ext (funext fun F => map_mul (sheafScalarEnd Λ J F) a b)
  map_zero' := NatTrans.ext (funext fun F => map_zero (sheafScalarEnd Λ J F))
  map_add' a b := NatTrans.ext (funext fun F => map_add (sheafScalarEnd Λ J F) a b)

/-- The component of `sheafScalarNatEnd Λ J a` at a sheaf `F` of `Λ`-modules is multiplication
by `a` on the abelian sheaf underlying `F`. -/
@[simp]
public lemma sheafScalarNatEnd_app (a : Λ) (F : Sheaf J (ModuleCat.{w} Λ)) :
    (sheafScalarNatEnd.{w} Λ J a).app F = sheafScalarEnd Λ J F a :=
  rfl

variable (H : Sheaf J AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w}) [H.Additive]

/-- The action of `Λ` on the value of an additive functor to abelian groups at the abelian sheaf
underlying a sheaf of `Λ`-modules. -/
public def valueScalarEnd :
    Λ →+* End (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ⋙ H) :=
  (whiskerRightEndRingHom _ H).comp (sheafScalarNatEnd.{w} Λ J)

/-- **The lift of an additive functor from abelian sheaves to abelian groups to sheaves of
`Λ`-modules.** The underlying abelian group of `valueLift H F` is `H` applied to the abelian
sheaf underlying `F`, and its `Λ`-action is the image under `H` of multiplication by scalars on
that sheaf. This is `Stacks.ModuleCatLift.moduleLift` with values in abelian groups instead of
abelian sheaves. -/
public def valueLift : Sheaf J (ModuleCat.{w} Λ) ⥤ ModuleCat.{w} Λ :=
  ofEndAction Λ _ (valueScalarEnd.{w} Λ J H)

/-- Forgetting the `Λ`-module structure of `Stacks.ModuleCatLift.valueLift` gives the original
functor applied to the underlying abelian sheaves, on the nose. -/
public lemma valueLift_comp_forget₂ :
    valueLift.{w} Λ J H ⋙ forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w} =
      sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ⋙ H :=
  rfl

/-- Multiplication by a scalar on the lift is the image under `H` of multiplication by that
scalar on the underlying abelian sheaf. -/
public lemma valueLift_obj_smul (F : Sheaf J (ModuleCat.{w} Λ)) (a : Λ) :
    ((valueLift.{w} Λ J H).obj F).smul a = H.map (sheafScalarEnd Λ J F a) :=
  rfl

/-- The map the lift induces on a morphism, read on underlying abelian groups. -/
@[simp]
public lemma forget₂_map_valueLift_map {F G : Sheaf J (ModuleCat.{w} Λ)} (φ : F ⟶ G) :
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).map ((valueLift.{w} Λ J H).map φ) =
      H.map ((sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map φ) :=
  rfl

end Sheaf

section Lift

variable (Λ : Type r) [Ring Λ] {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂}
  [Category.{v₂} C₂] (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂)
  [J₁.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [J₂.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  (G : Sheaf J₁ AddCommGrpCat.{w} ⥤ Sheaf J₂ AddCommGrpCat.{w}) [G.Additive]

/-- Multiplication by a scalar on the abelian sheaf underlying the lift of an additive functor
`G` is the image under `G` of multiplication by that scalar. -/
public lemma sheafScalarEnd_moduleLiftObj (F : Sheaf J₁ (ModuleCat.{w} Λ)) (a : Λ) :
    sheafScalarEnd Λ J₂ (moduleLiftObj Λ J₁ J₂ G F) a = G.map (sheafScalarEnd Λ J₁ F a) :=
  rfl

end Lift

end Stacks.ModuleCatLift

namespace AlgebraicGeometry.SmallEtale

section FiberStalksFunctor

universe u v

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) (s : GeometricPoint Y.obj)

/-- **The direct sum of the stalks over a geometric fibre, as a functor** on abelian sheaves on
the small étale site of `X`: the object is
`AlgebraicGeometry.SmallEtale.fiberStalks` and the map is
`AlgebraicGeometry.SmallEtale.fiberStalksMap`. This is the direct sum itself, not the coproduct
it represents. -/
public def fiberStalksFunctor :
    Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max u v} ⥤
      AddCommGrpCat.{max u v} where
  obj F := AddCommGrpCat.of (fiberStalks.{u, v} B f s F)
  map φ := AddCommGrpCat.ofHom (fiberStalksMap.{u, v} B f s φ)
  map_id F := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun z => DFinsupp.ext fun x => ?_)
    exact ConcreteCategory.congr_hom
      (((geometricPointSitePoint B X.obj X.property
        (x.toGeometricPoint B f s)).sheafFiber (A := AddCommGrpCat.{max u v})).map_id F) (z x)
  map_comp φ ψ := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun z => DFinsupp.ext fun x => ?_)
    exact ConcreteCategory.congr_hom
      (((geometricPointSitePoint B X.obj X.property
        (x.toGeometricPoint B f s)).sheafFiber
          (A := AddCommGrpCat.{max u v})).map_comp φ ψ) (z x)

/-- The direct sum of the stalks over a geometric fibre is an additive functor: each stalk
functor is, and a direct sum of additive maps is additive. -/
public instance fiberStalksFunctor_additive : (fiberStalksFunctor.{u, v} B f s).Additive where
  map_add {F G} {φ ψ} := by
    change AddCommGrpCat.ofHom (fiberStalksMap.{u, v} B f s (φ + ψ)) =
      AddCommGrpCat.ofHom (fiberStalksMap.{u, v} B f s φ) +
        AddCommGrpCat.ofHom (fiberStalksMap.{u, v} B f s ψ)
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun z => DFinsupp.ext fun x => ?_)
    exact ConcreteCategory.congr_hom
      (((geometricPointSitePoint B X.obj X.property
        (x.toGeometricPoint B f s)).sheafFiber (A := AddCommGrpCat.{max u v})).map_add) (z x)

end FiberStalksFunctor

section Decomposition

universe u v r

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ]

/-- **The stalk at a geometric point of a sheaf of `Λ`-modules**, as a `Λ`-module: the abelian
stalk of Stacks 040R with the scalar action obtained from functoriality of the stalk. -/
public def moduleEtaleStalkFunctor (S : B.Scheme) (s : GeometricPoint S.obj) :
    ModuleSheaf.{u, v, r} B S Λ ⥤ ModuleCat.{max (u + 1) v r} Λ :=
  Stacks.ModuleCatLift.valueLift.{max (u + 1) v r, r, _, _} Λ
    (SmallEtale.topology B S.obj S.property)
    ((geometricPointSitePoint B S.obj S.property s).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v r}))

/-- The abelian group underlying the `Λ`-module stalk is the étale stalk of the underlying
abelian sheaf. -/
public lemma forget₂_obj_moduleEtaleStalkFunctor_obj (S : B.Scheme)
    (s : GeometricPoint S.obj) (F : ModuleSheaf.{u, v, r} B S Λ) :
    (forget₂ (ModuleCat.{max (u + 1) v r} Λ) AddCommGrpCat.{max (u + 1) v r}).obj
        ((moduleEtaleStalkFunctor.{u, v, r} B Λ S s).obj F) =
      etaleStalk B S.obj S.property s ((forgetModuleSheaf.{u, v, r} B S Λ).obj F).obj :=
  rfl

variable {X Y : B.Scheme} (f : X ⟶ Y)

/-- **The direct sum of the stalks of a sheaf of `Λ`-modules over a geometric fibre**, as a
`Λ`-module: the `Λ`-module `⊕_{f(x̄) = ȳ} F_x̄`. Its underlying abelian group is
`AlgebraicGeometry.SmallEtale.fiberStalks` of the underlying abelian sheaf, and the scalar
action is summandwise the scalar action on the stalks of `F`. -/
public def moduleFiberStalks (s : GeometricPoint Y.obj) :
    ModuleSheaf.{u, v, r} B X Λ ⥤ ModuleCat.{max (u + 1) v r} Λ :=
  Stacks.ModuleCatLift.valueLift.{max (u + 1) v r, r, _, _} Λ
    (SmallEtale.topology B X.obj X.property)
    (fiberStalksFunctor.{u, max (u + 1) v r} B f s)

/-- The abelian group underlying `AlgebraicGeometry.SmallEtale.moduleFiberStalks` is the direct
sum of the abelian stalks over the geometric fibre. -/
public lemma forget₂_obj_moduleFiberStalks_obj (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, r} B X Λ) :
    (forget₂ (ModuleCat.{max (u + 1) v r} Λ) AddCommGrpCat.{max (u + 1) v r}).obj
        ((moduleFiberStalks.{u, v, r} B Λ f s).obj F) =
      AddCommGrpCat.of (fiberStalks.{u, max (u + 1) v r} B f s
        ((forgetModuleSheaf.{u, v, r} B X Λ).obj F)) :=
  rfl

/-- The map `AlgebraicGeometry.SmallEtale.moduleFiberStalks` induces on a morphism of sheaves of
`Λ`-modules is `AlgebraicGeometry.SmallEtale.fiberStalksMap` of the underlying morphism of
abelian sheaves. -/
public lemma forget₂_map_moduleFiberStalks_map (s : GeometricPoint Y.obj)
    {F G : ModuleSheaf.{u, v, r} B X Λ} (φ : F ⟶ G) :
    (forget₂ (ModuleCat.{max (u + 1) v r} Λ) AddCommGrpCat.{max (u + 1) v r}).map
        ((moduleFiberStalks.{u, v, r} B Λ f s).map φ) =
      AddCommGrpCat.ofHom (fiberStalksMap.{u, max (u + 1) v r} B f s
        ((forgetModuleSheaf.{u, v, r} B X Λ).map φ)) :=
  rfl

/-- Multiplication by a scalar on the direct sum of the stalks over the geometric fibre is the
map that multiplication by that scalar on the underlying abelian sheaf induces on stalks. -/
public lemma moduleFiberStalks_smul (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, r} B X Λ) (a : Λ) :
    ((moduleFiberStalks.{u, v, r} B Λ f s).obj F).smul a =
      AddCommGrpCat.ofHom (fiberStalksMap.{u, max (u + 1) v r} B f s
        (Stacks.ModuleCatLift.sheafScalarEnd Λ
          (SmallEtale.topology B X.obj X.property) F a)) :=
  rfl

/-- **The scalar action on `⊕_{f(x̄) = ȳ} F_x̄` is summandwise the scalar action on the stalks of
`F`**: the target of the `Λ`-linear stalk decomposition really is the direct sum of the
`Λ`-module stalks of `F` over the geometric fibre. -/
public lemma moduleFiberStalks_smul_apply (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, r} B X Λ) (a : Λ)
    (z : fiberStalks.{u, max (u + 1) v r} B f s
      ((forgetModuleSheaf.{u, v, r} B X Λ).obj F)) :
    (((moduleFiberStalks.{u, v, r} B Λ f s).obj F).smul a).hom z =
      DirectSum.map (fun x : GeometricFiberPoint B f s =>
        (((moduleEtaleStalkFunctor.{u, v, r} B Λ X
          (x.toGeometricPoint B f s)).obj F).smul a).hom) z :=
  rfl

variable [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- **The stalk decomposition of the direct image with compact support with coefficients in a
ring `Λ`.** The stalk of the `Λ`-linear `f_!F` of
`AlgebraicGeometry.SmallEtale.fShriekMod` at a geometric point `ȳ` of `Y` is, as a `Λ`-module,
the direct sum of the stalks of `F` over the geometric points of `X` lying over `ȳ`:
`(f_!F)_ȳ ≅ ⊕_{f(x̄) = ȳ} F_x̄`. This is the `Λ`-module form of the decomposition of Stacks
0F5F. -/
public def moduleFShriekStalkIso (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, r} B X Λ) :
    (moduleEtaleStalkFunctor.{u, v, r} B Λ Y s).obj ((fShriekMod.{u, v, r} B Λ f).obj F) ≅
      (moduleFiberStalks.{u, v, r} B Λ f s).obj F :=
  ModuleCat.isoMk
    (fShriekStalkIso.{u, max v r} B f s ((forgetModuleSheaf.{u, v, r} B X Λ).obj F))
    fun a =>
      (congrArg
        (fun z => (fShriekStalkIso.{u, max v r} B f s
          ((forgetModuleSheaf.{u, v, r} B X Λ).obj F)).hom ≫ z)
        (moduleFiberStalks_smul.{u, v, r} B Λ f s F a)).trans
        (fShriekStalkIso_natural.{u, max v r} B f s
          (Stacks.ModuleCatLift.sheafScalarEnd Λ
            (SmallEtale.topology B X.obj X.property) F a)).symm

/-- **The `Λ`-linear stalk decomposition is the canonical one**: its underlying map of abelian
groups is the decomposition `AlgebraicGeometry.SmallEtale.fShriekStalkIso` of Stacks 0F5F. With
`AlgebraicGeometry.SmallEtale.fShriekStalkIso_comp_sheafification` this identifies it with the
germ decomposition of the finite-support direct image. -/
public lemma moduleFShriekStalkIso_forget₂ (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, r} B X Λ) :
    (forget₂ (ModuleCat.{max (u + 1) v r} Λ) AddCommGrpCat.{max (u + 1) v r}).map
        (moduleFShriekStalkIso.{u, v, r} B Λ f s F).hom =
      (fShriekStalkIso.{u, max v r} B f s
        ((forgetModuleSheaf.{u, v, r} B X Λ).obj F)).hom :=
  rfl

/-- **The `Λ`-linear stalk decomposition is natural in the sheaf of `Λ`-modules:** a morphism of
sheaves of `Λ`-modules on `X` acts on the direct sum of stalks over the geometric fibre by its
maps on those stalks. -/
public theorem moduleFShriekStalkIso_natural (s : GeometricPoint Y.obj)
    {F G : ModuleSheaf.{u, v, r} B X Λ} (φ : F ⟶ G) :
    (moduleEtaleStalkFunctor.{u, v, r} B Λ Y s).map ((fShriekMod.{u, v, r} B Λ f).map φ) ≫
        (moduleFShriekStalkIso.{u, v, r} B Λ f s G).hom =
      (moduleFShriekStalkIso.{u, v, r} B Λ f s F).hom ≫
        (moduleFiberStalks.{u, v, r} B Λ f s).map φ := by
  refine (forget₂ (ModuleCat.{max (u + 1) v r} Λ)
    AddCommGrpCat.{max (u + 1) v r}).map_injective ?_
  rw [Functor.map_comp, Functor.map_comp,
    forget₂_map_moduleFiberStalks_map.{u, v, r} B Λ f s φ]
  exact fShriekStalkIso_natural.{u, max v r} B f s
    ((forgetModuleSheaf.{u, v, r} B X Λ).map φ)

/-- **The stalk decomposition of the direct image with compact support with coefficients in a
ring `Λ`, as an isomorphism of functors.** Composing the `Λ`-linear `f_!` with the stalk at a
geometric point `ȳ` of `Y` gives the direct sum over the geometric fibre of the stalk functors
of `X`: `(f_!(-))_ȳ ≅ ⊕_{f(x̄) = ȳ} (-)_x̄` as functors on sheaves of `Λ`-modules. -/
public def moduleFShriekStalkNatIso (s : GeometricPoint Y.obj) :
    fShriekMod.{u, v, r} B Λ f ⋙ moduleEtaleStalkFunctor.{u, v, r} B Λ Y s ≅
      moduleFiberStalks.{u, v, r} B Λ f s :=
  NatIso.ofComponents (fun F => moduleFShriekStalkIso.{u, v, r} B Λ f s F)
    fun {_ _} φ => moduleFShriekStalkIso_natural.{u, v, r} B Λ f s φ

end Decomposition

end AlgebraicGeometry.SmallEtale

end
