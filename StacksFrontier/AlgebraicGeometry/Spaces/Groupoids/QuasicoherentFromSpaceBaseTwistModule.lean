module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentFromSpaceBaseMemberModule

/-!
# The sheaf of modules a quasi-coherent module on a kernel-pair groupoid gives

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces and let `φ : U ⟶ X` be an étale morphism
with `R = U ×_X U` and `t`, `s` the two projections. A quasi-coherent module `(ℱ, α)` on the
groupoid gives a sheaf of modules over the restricted structure sheaf of the site of the charts of
`φ`, whose underlying presheaf of abelian groups is `AlgebraicGeometry.Space.memberPresheaf`.

## Main definitions

* `AlgebraicGeometry.Space.memberModule`: the sheaf of modules over the restricted structure
  sheaf of the site of the charts of `φ` given by a quasi-coherent module on the groupoid.
* `AlgebraicGeometry.Space.memberModuleRestrict`: its underlying abelian presheaf, restricted
  along the charts of `U`, is isomorphic to the abelian presheaf of `ℱ`.

## Main results

* `AlgebraicGeometry.Space.transitionSect_smul`: the reading on sections of a morphism of two
  inverse images of a module along étale morphisms is linear over the structure ring of the chart
  of the test space.
* `AlgebraicGeometry.Space.legSect_smul`: the reading on sections of the transition morphism of
  the groupoid is linear.
* `AlgebraicGeometry.Space.memberSectMap_smul`: the restriction map
  `AlgebraicGeometry.Space.memberSectMap` is semilinear.
* `AlgebraicGeometry.Space.memberPresheaf_map_smul`: the restriction maps of
  `AlgebraicGeometry.Space.memberPresheaf` are semilinear over the restricted structure sheaf.
* `AlgebraicGeometry.Space.memberModule_val_obj`: the sections of the sheaf of modules over a
  chart of `U` are the sections of `ℱ` over that chart.
* `AlgebraicGeometry.Space.memberModule_val_map`: the restriction maps of the sheaf of modules
  are `AlgebraicGeometry.Space.memberSectMap`.

## Implementation notes

The structure ring of the chart `Y ≫ g` of `C` is the structure ring of the chart `Y` of `D` by
`rfl` (`AlgebraicGeometry.Space.ringSheaf_postcomp_obj`), but the two are different terms, so
instance resolution does not see that a scalar of one acts on a module over the other. A scalar of
one ring is therefore read in the other as `id r` with the other ring ascribed; a bare ascription
`(r : T)` does not elaborate, since the `HSMul` instance is sought at the inferred type of `r`.

Each reconciliation of the two readings is kept in a declaration of its own
(`AlgebraicGeometry.Space.memberSectMap_smul`, `AlgebraicGeometry.Space.smul_memberSectMap`,
`AlgebraicGeometry.Space.memberPresheaf_map_smul`, and
`AlgebraicGeometry.Space.memberModule_val_map` through
`AlgebraicGeometry.Space.memberModule_val_map_apply`): two of them in one `isDefEq` call exhaust
the elaborator's recursion depth.

## References

* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The reading of a morphism of inverse images is linear -/

section Abstract

variable {C D U V : AlgebraicSpaces B S hS}

/-- The structure ring of the chart of `C` obtained by postcomposing a chart `Y` of `D` with an
étale `g : D ⟶ C` is the structure ring of `Y`. -/
theorem ringSheaf_postcomp_obj (g : D ⟶ C) (hg : IsEtale B S hS g.hom)
    (Y : SmallEtale B S hS D.1) :
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS C.1 C.2).O)).obj.obj
        (.op ((smallEtalePostcomp B S hS g hg).obj Y)) =
      ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS D.1 D.2).O)).obj.obj (.op Y) :=
  rfl

/-- Reading a section of an étale restriction back as a section of the inverse image is
linear, the scalar being read over the composite chart on the one side and over the chart of
the test space on the other. -/
private theorem etaleSectInv_smul_test (g : D ⟶ C) (hg : IsEtale B S hS g.hom)
    (M : Modules.{u, u} B S hS C.1 C.2) (Y : SmallEtale B S hS D.1)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.1 D.2).O)).obj.obj (.op Y))
    (m : M.val.obj (.op ((smallEtalePostcomp B S hS g hg).obj Y))) :
    etaleSectInv B S hS g hg M Y
        ((id r : ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS C.1 C.2).O)).obj.obj
          (.op ((smallEtalePostcomp B S hS g hg).obj Y))) • m) =
      r • etaleSectInv B S hS g hg M Y m :=
  (((modulePullbackIsoEtaleModulePullback B S hS g hg).inv.app M).val.app (.op Y)).hom.map_smul
    r m

/-- Reading a section of the inverse image as a section over the composite chart is linear,
the scalar being read over the chart of the test space on the one side and over the composite
chart on the other. -/
private theorem etaleSect_smul_test (g : D ⟶ C) (hg : IsEtale B S hS g.hom)
    (M : Modules.{u, u} B S hS C.1 C.2) (Y : SmallEtale B S hS D.1)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.1 D.2).O)).obj.obj (.op Y))
    (s : ((modulePullback B S hS g).obj M).val.obj (.op Y)) :
    etaleSect B S hS g hg M Y (r • s) =
      (id r : ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS C.1 C.2).O)).obj.obj
          (.op ((smallEtalePostcomp B S hS g hg).obj Y))) •
        etaleSect B S hS g hg M Y s :=
  (((modulePullbackIsoEtaleModulePullback B S hS g hg).hom.app M).val.app (.op Y)).hom.map_smul
    r s

/-- Reading a section of the inverse image over the composite chart respects equality of
sections. -/
private theorem etaleSect_congr_sect (g : D ⟶ C) (hg : IsEtale B S hS g.hom)
    (M : Modules.{u, u} B S hS C.1 C.2) (Y : SmallEtale B S hS D.1)
    {s s' : ((modulePullback B S hS g).obj M).val.obj (.op Y)} (h : s = s') :
    etaleSect B S hS g hg M Y s = etaleSect B S hS g hg M Y s' :=
  congrArg (etaleSect B S hS g hg M Y) h

/-- The reading of a morphism of two inverse images of a module along étale morphisms is
linear: a scalar on the chart `Y` of the test space, read over the chart `Y ≫ a` of `U`, is
carried to the same scalar read over the chart `Y ≫ b`. -/
theorem transitionSect_smul (F : Modules.{u, u} B S hS U.1 U.2) {a b : V ⟶ U}
    (ψ : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F)
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom) (Y : SmallEtale B S hS V.1)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS V.1 V.2).O)).obj.obj (.op Y))
    (m : F.val.obj (.op ((smallEtalePostcomp B S hS a ha).obj Y))) :
    transitionSect B S hS F ψ ha hb Y
        ((id r : ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS U.1 U.2).O)).obj.obj
          (.op ((smallEtalePostcomp B S hS a ha).obj Y))) • m) =
      (id r : ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS U.1 U.2).O)).obj.obj
          (.op ((smallEtalePostcomp B S hS b hb).obj Y))) •
        transitionSect B S hS F ψ ha hb Y m :=
  (etaleSect_congr_sect B S hS b hb F Y
      ((val_app_congr B S hS ψ Y (etaleSectInv_smul_test B S hS a ha F Y r m)).trans
        ((ψ.val.app (.op Y)).hom.map_smul r (etaleSectInv B S hS a ha F Y m)))).trans
    (etaleSect_smul_test B S hS b hb F Y r
      (ψ.val.app (.op Y) (etaleSectInv B S hS a ha F Y m)))

end Abstract

variable {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
  {X : AlgebraicSpaces B S hS} (φ : G.objects ⟶ X) (hφet : IsEtale B S hS φ.hom)
  (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom)
  (Z : QuasicoherentModule B S hS G)

/-- The reading of the transition morphism of the groupoid on sections is linear. -/
theorem legSect_smul {P : AlgebraicSpaces B S hS} (a b : P ⟶ G.objects)
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom) (hab : a ≫ φ = b ≫ φ)
    (Y : SmallEtale B S hS P.1)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS P.1 P.2).O)).obj.obj (.op Y))
    (m : Z.F.obj.val.obj (.op ((smallEtalePostcomp B S hS a ha).obj Y))) :
    legSect B S hS G φ hpb Z a b ha hb hab Y
        ((id r : ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS G.objects.1
          G.objects.2).O)).obj.obj (.op ((smallEtalePostcomp B S hS a ha).obj Y))) • m) =
      (id r : ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS G.objects.1
          G.objects.2).O)).obj.obj (.op ((smallEtalePostcomp B S hS b hb).obj Y))) •
        legSect B S hS G φ hpb Z a b ha hb hab Y m :=
  transitionSect_smul B S hS Z.F.obj (legTransition B S hS G φ hpb Z a b hab) ha hb Y r m

/-! ### The sheaf of modules -/

section CoverDense

variable [(singleFunctor B S hS φ hφet).IsCoverDense (SmallEtale.topology B S hS X.1)]

/-- The restriction map `AlgebraicGeometry.Space.memberSectMap` is semilinear, with the
restricted scalar read over the target chart of `U`. -/
theorem memberSectMap_smul {P Q : (SingleSite B S hS φ hφet)ᵒᵖ} (f : P ⟶ Q)
    (r : (singleRing B S hS φ hφet).obj.obj P)
    (m : (memberPresheaf B S hS G φ hφet hpb Z).obj P) :
    memberSectMap B S hS G φ hφet hpb Z f.unop (r • m) =
      (id ((singleRing B S hS φ hφet).obj.map f r) :
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS G.objects.1
            G.objects.2).O)).obj.obj (.op Q.unop.2)) •
        memberSectMap B S hS G φ hφet hpb Z f.unop m :=
  (memberSectMap_smul_apply B S hS G φ hφet hpb Z f r m).trans
    (legSect_smul B S hS G φ hpb Z (chartLegSnd B S hS φ hφet f.unop.hom)
      (chartLegFst B S hS Q.unop.2) (isEtale_chartLegSnd B S hS φ hφet f.unop.hom)
      (isEtale_chartLegFst B S hS Q.unop.2)
      (chartLeg_condition B S hS φ hφet f.unop.hom).symm (chartTestUnit B S hS Q.unop.2)
      (((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS G.objects.1 G.objects.2).O)).obj.map
        (chartUnitSnd B S hS φ hφet f.unop.hom).op r)
      (Z.F.obj.val.map (chartUnitSnd B S hS φ hφet f.unop.hom).op m))

/-- The restricted scalar acting on the restricted section is the same read through either of
the two module structures on the sections over the target chart: the one of the structure ring
of that chart of `U`, and the one of the restricted structure sheaf of the site given by
`AlgebraicGeometry.Space.moduleMemberPresheaf`. -/
theorem smul_memberSectMap {P Q : (SingleSite B S hS φ hφet)ᵒᵖ} (f : P ⟶ Q)
    (r : (singleRing B S hS φ hφet).obj.obj P)
    (m : (memberPresheaf B S hS G φ hφet hpb Z).obj P) :
    (id ((singleRing B S hS φ hφet).obj.map f r) :
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS G.objects.1
            G.objects.2).O)).obj.obj (.op Q.unop.2)) •
        memberSectMap B S hS G φ hφet hpb Z f.unop m =
      (singleRing B S hS φ hφet).obj.map f r •
        (id (memberSectMap B S hS G φ hφet hpb Z f.unop m) :
          (memberPresheaf B S hS G φ hφet hpb Z).obj Q) :=
  rfl

/-- The restriction maps of `AlgebraicGeometry.Space.memberPresheaf` are semilinear over the
restricted structure sheaf. -/
theorem memberPresheaf_map_smul {P Q : (SingleSite B S hS φ hφet)ᵒᵖ} (f : P ⟶ Q)
    (r : (singleRing B S hS φ hφet).obj.obj P)
    (m : (memberPresheaf B S hS G φ hφet hpb Z).obj P) :
    (memberPresheaf B S hS G φ hφet hpb Z).map f (r • m) =
      (singleRing B S hS φ hφet).obj.map f r •
        (memberPresheaf B S hS G φ hφet hpb Z).map f m :=
  ((memberPresheaf_map_apply B S hS G φ hφet hpb Z f (r • m)).trans
      ((memberSectMap_smul B S hS G φ hφet hpb Z f r m).trans
        (smul_memberSectMap B S hS G φ hφet hpb Z f r m))).trans
    (congrArg (fun y : (memberPresheaf B S hS G φ hφet hpb Z).obj Q =>
        (singleRing B S hS φ hφet).obj.map f r • y)
      (memberPresheaf_map_apply B S hS G φ hφet hpb Z f m).symm)

/-- A quasi-coherent module on a kernel-pair groupoid, read as a sheaf of modules on the site
of the charts of `φ`. Its sections over a chart of `U` are the sections of `ℱ` over that
chart, and its restriction maps are `AlgebraicGeometry.Space.memberSectMap`. -/
def memberModule : SheafOfModules.{u} (singleRing B S hS φ hφet) where
  val := PresheafOfModules.ofPresheaf (memberPresheaf B S hS G φ hφet hpb Z)
    (fun {_ _} f r m => memberPresheaf_map_smul B S hS G φ hφet hpb Z f r m)
  isSheaf := isSheaf_memberPresheaf B S hS G φ hφet hpb Z

/-- The sections of the sheaf of modules over a chart of `U` are the sections of `ℱ` over that
chart. -/
theorem memberModule_val_obj (V : SmallEtale B S hS G.objects.1) :
    (memberModule B S hS G φ hφet hpb Z).val.obj (.op (singleObj B S hS φ hφet V)) =
      Z.F.obj.val.obj (.op V) :=
  rfl

/-- The abelian presheaf underlying the sheaf of modules is
`AlgebraicGeometry.Space.memberPresheaf`. -/
theorem memberModule_val_presheaf :
    (memberModule B S hS G φ hφet hpb Z).val.presheaf =
      memberPresheaf B S hS G φ hφet hpb Z :=
  rfl

/-- The restriction map of the sheaf of modules, read on a section, is the restriction map of
the presheaf of abelian groups. -/
theorem memberModule_val_map_apply {p q : SingleSite B S hS φ hφet} (k : p ⟶ q)
    (m : (memberModule B S hS G φ hφet hpb Z).val.obj (.op q)) :
    (memberModule B S hS G φ hφet hpb Z).val.map k.op m =
      (memberPresheaf B S hS G φ hφet hpb Z).map k.op m :=
  rfl

/-- The restriction map of the sheaf of modules is `AlgebraicGeometry.Space.memberSectMap`. -/
theorem memberModule_val_map {p q : SingleSite B S hS φ hφet} (k : p ⟶ q)
    (m : (memberModule B S hS G φ hφet hpb Z).val.obj (.op q)) :
    (memberModule B S hS G φ hφet hpb Z).val.map k.op m =
      memberSectMap B S hS G φ hφet hpb Z k m :=
  (memberModule_val_map_apply B S hS G φ hφet hpb Z k m).trans
    (memberPresheaf_map_apply B S hS G φ hφet hpb Z k.op m)

/-- The abelian presheaf of the sheaf of modules, restricted along the charts of `U`, is
isomorphic to the abelian presheaf of `ℱ`. -/
def memberModuleRestrict :
    (singleInclusion B S hS φ hφet).op ⋙ (memberModule B S hS G φ hφet hpb Z).val.presheaf ≅
      Z.F.obj.val.presheaf :=
  memberPresheafRestrict B S hS G φ hφet hpb Z

end CoverDense

end AlgebraicGeometry.Space

end
