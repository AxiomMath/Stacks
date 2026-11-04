module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.EtaleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackAssoc

/-!
# Iterated étale restriction against the comparison of inverse images along a composite

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces. The inverse image of `𝒪_Y`-modules along
`f` is étale restriction, by `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`.
Étale restriction composes strictly, whereas the inverse image composes only up to the comparison
`AlgebraicGeometry.Space.modulePullbackCompIso`. This file shows that the two are compatible, in
the sense of `AlgebraicGeometry.Space.QuasiCoherentDescent.ModulePullbackCompIsoEtaleRestriction`,
provided the two adjunctions between étale restriction along a composite and the direct image
along that composite have the same unit.

## Main definitions

* `AlgebraicGeometry.Space.etaleRestrictionRingMap`: the structure map along which étale
  restriction of modules is taken, the identity.
* `AlgebraicGeometry.Space.etaleModulePullbackComp`: the identification of iterated étale
  restriction of modules with étale restriction along the composite chart.
* `AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction`: the adjunction between étale
  restriction along a composite and the direct image along the composite, assembled from the two
  factors.

## Main results

* `CategoryTheory.Adjunction.leftAdjointUniq_hom_congr_unit`: the comparison of two left
  adjoints of one functor depends on the second adjunction only through its unit.
* `CategoryTheory.Adjunction.leftAdjointUniq_hom_ofNatIsoLeft`: transporting the second left
  adjoint along a natural isomorphism composes that isomorphism onto the comparison.
* `SheafOfModules.val_app_apply_congr`: equal morphisms of sheaves of modules agree on
  sections.
* `AlgebraicGeometry.Space.etaleRestrictionRingMap_comp` and
  `AlgebraicGeometry.Space.etaleModulePullbackComp_hom_app_val_app`: iterated étale restriction
  is restriction along the composite chart, with the identity on sections.
* `AlgebraicGeometry.Space.modulePullbackCompIso_hom_comp_etaleRestriction`: granted the
  equality of the two units, `modulePullbackCompIso` followed by
  `modulePullbackIsoEtaleModulePullback` is `modulePullbackIsoEtaleModulePullback` in each factor
  followed by the strict composition of étale restrictions.
* `AlgebraicGeometry.Space.etaleRestrictionComp_of_unit`: the same statement read on sections,
  at a single composable pair for which the two units agree.
* `AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction_of_unit`: granted the same
  equality at every composable pair,
  `AlgebraicGeometry.Space.QuasiCoherentDescent.ModulePullbackCompIsoEtaleRestriction` holds.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace CategoryTheory.Adjunction

universe v₁ v₂ u₁ u₂

variable {CC : Type u₁} [Category.{v₁} CC] {DD : Type u₂} [Category.{v₂} DD]

/-- The comparison of two left adjoints of one functor depends on the second adjunction only
through its unit. -/
theorem leftAdjointUniq_hom_congr_unit {F F' : CC ⥤ DD} {G : DD ⥤ CC} (adj1 : F ⊣ G)
    (adj2 adj3 : F' ⊣ G) (hu : adj2.unit = adj3.unit) :
    (leftAdjointUniq adj1 adj2).hom = (leftAdjointUniq adj1 adj3).hom := by
  refine natTrans_ext adj1 fun A ↦ ?_
  rw [unit_leftAdjointUniq_hom_app, unit_leftAdjointUniq_hom_app, hu]

/-- The comparison of a left adjoint with a transport of a second one along a natural
isomorphism is the comparison with the second one, followed by that isomorphism. -/
theorem leftAdjointUniq_hom_ofNatIsoLeft {F F' F'' : CC ⥤ DD} {G : DD ⥤ CC} (adj1 : F ⊣ G)
    (adj2 : F' ⊣ G) (iso : F' ≅ F'') :
    (leftAdjointUniq adj1 (adj2.ofNatIsoLeft iso)).hom =
      (leftAdjointUniq adj1 adj2).hom ≫ iso.hom := by
  refine natTrans_ext adj1 fun A ↦ ?_
  rw [unit_leftAdjointUniq_hom_app, NatTrans.comp_app, G.map_comp, ← Category.assoc,
    unit_leftAdjointUniq_hom_app, ofNatIsoLeft_unit, NatTrans.comp_app,
    Functor.whiskerRight_app]

end CategoryTheory.Adjunction

namespace SheafOfModules

universe w vv uu

variable {T : Type uu} [Category.{vv} T] {J : GrothendieckTopology T} {O : Sheaf J RingCat.{w}}

/-- Equal morphisms of sheaves of modules agree on sections. -/
theorem val_app_apply_congr {M N : SheafOfModules.{w} O} {x y : M ⟶ N} (e : x = y) (U : Tᵒᵖ)
    (m : M.val.obj U) :
    x.val.app U m = y.val.app U m := by
  rw [e]

end SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {A C D X Y : AlgebraicSpaces B S hS}

/-- The structure map along which étale restriction of modules along an étale `f : X ⟶ Y` is
taken: the identity of the structure sheaf of `X`. -/
def etaleRestrictionRingMap (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) ⟶
      ((smallEtalePostcomp B S hS f hf).sheafPushforwardContinuous RingCat.{u}
          (smallEtaleRingedSite B S hS X.1 X.2).J
          (smallEtaleRingedSite B S hS Y.1 Y.2).J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) :=
  𝟙 _

/-- Étale restriction of modules is the pushforward of sheaves of modules along
postcomposition of charts, taken at the identity structure map. -/
theorem pushforward_etaleRestrictionRingMap (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    SheafOfModules.pushforward.{u} (F := smallEtalePostcomp B S hS f hf)
        (etaleRestrictionRingMap B S hS f hf) =
      etaleModulePullback.{u, u} B S hS f hf :=
  rfl

/-- Reading a section of an inverse image along an étale morphism is
`modulePullbackIsoEtaleModulePullback` evaluated on that section. -/
theorem etaleSect_eq (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (U : SmallEtale B S hS X.1)
    (m : ((modulePullback B S hS f).obj M).val.obj (op U)) :
    QuasiCoherentDescent.etaleSect B S hS f hf M U m =
      ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app M).val.app (op U) m :=
  rfl

section Comp

variable (h : D ⟶ A) (g : A ⟶ C) (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g.hom)
    (hhg : IsEtale B S hS (h ≫ g).hom)

/-- The composite of postcomposition along `h` and postcomposition along `g` is continuous for
the étale topologies of the small étale sites. -/
local instance smallEtaleRingedSite_isContinuous_smallEtalePostcomp_comp :
    (smallEtalePostcomp B S hS h hh ⋙ smallEtalePostcomp B S hS g hg).IsContinuous
      (smallEtaleRingedSite B S hS D.1 D.2).J (smallEtaleRingedSite B S hS C.1 C.2).J :=
  Functor.isContinuous_comp (smallEtalePostcomp B S hS h hh)
    (smallEtalePostcomp B S hS g hg) (smallEtaleRingedSite B S hS D.1 D.2).J
    (smallEtaleRingedSite B S hS A.1 A.2).J (smallEtaleRingedSite B S hS C.1 C.2).J

/-- Postcomposition of charts composes: postcomposing along `h` and then along `g` is
postcomposing along `h ≫ g`, as functors between the small étale sites. -/
theorem smallEtalePostcomp_comp :
    smallEtalePostcomp B S hS h hh ⋙ smallEtalePostcomp B S hS g hg =
      smallEtalePostcomp B S hS (h ≫ g) hhg :=
  rfl

/-- The structure map along which étale restriction along a composite of charts is taken. -/
def etaleRestrictionRingMapComp :
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS D.1 D.2).O) ⟶
      ((smallEtalePostcomp B S hS h hh ⋙
            smallEtalePostcomp B S hS g hg).sheafPushforwardContinuous RingCat.{u}
          (smallEtaleRingedSite B S hS D.1 D.2).J
          (smallEtaleRingedSite B S hS C.1 C.2).J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS C.1 C.2).O) :=
  𝟙 _

/-- The two structure maps of an iterated étale restriction agree: both are the identity. -/
theorem etaleRestrictionRingMap_comp :
    etaleRestrictionRingMap B S hS h hh ≫
        ((smallEtalePostcomp B S hS h hh).sheafPushforwardContinuous RingCat.{u}
          (smallEtaleRingedSite B S hS D.1 D.2).J
          (smallEtaleRingedSite B S hS A.1 A.2).J).map
            (etaleRestrictionRingMap B S hS g hg) =
      etaleRestrictionRingMapComp B S hS h g hh hg :=
  rfl

/-- Iterated étale restriction of modules is étale restriction along the composite. -/
def etaleModulePullbackComp :
    etaleModulePullback.{u, u} B S hS g hg ⋙ etaleModulePullback.{u, u} B S hS h hh ≅
      etaleModulePullback.{u, u} B S hS (h ≫ g) hhg :=
  (SheafOfModules.pushforwardComp (F := smallEtalePostcomp B S hS h hh)
      (G := smallEtalePostcomp B S hS g hg) (etaleRestrictionRingMap B S hS h hh)
      (etaleRestrictionRingMap B S hS g hg) :
    etaleModulePullback.{u, u} B S hS g hg ⋙ etaleModulePullback.{u, u} B S hS h hh ≅
      SheafOfModules.pushforward
        (F := smallEtalePostcomp B S hS h hh ⋙ smallEtalePostcomp B S hS g hg)
        (etaleRestrictionRingMapComp B S hS h g hh hg))

/-- Iterated étale restriction is restriction along the composite, on sections. -/
theorem etaleModulePullbackComp_hom_app_val_app (M : Modules.{u, u} B S hS C.1 C.2)
    (U : SmallEtale B S hS D.1)
    (m : ((etaleModulePullback.{u, u} B S hS g hg).obj M).val.obj
      (op ((smallEtalePostcomp B S hS h hh).obj U))) :
    ((etaleModulePullbackComp B S hS h g hh hg hhg).hom.app M).val.app (op U) m = m :=
  rfl

/-- The adjunction between étale restriction along a composite and the direct image along the
composite, assembled from the two étale restriction adjunctions and the comparison
`modulePushforwardCompIso` of direct images. -/
def etaleModulePullbackCompAdjunction :
    etaleModulePullback.{u, u} B S hS (h ≫ g) hhg ⊣ modulePushforward B S hS (h ≫ g) :=
  (((etaleModulePullbackAdjunction B S hS g hg).comp
        (etaleModulePullbackAdjunction B S hS h hh)).ofNatIsoRight
      (modulePushforwardCompIso B S hS h g)).ofNatIsoLeft
    (etaleModulePullbackComp B S hS h g hh hg hhg)

/-- If the two adjunctions of étale restriction along the composite `h ≫ g` have the same unit,
then `modulePullbackCompIso` followed by `modulePullbackIsoEtaleModulePullback` is
`modulePullbackIsoEtaleModulePullback` in each factor, followed by the strict composition
`etaleModulePullbackComp` of étale restrictions. -/
theorem modulePullbackCompIso_hom_comp_etaleRestriction
    (hu : (etaleModulePullbackCompAdjunction B S hS h g hh hg hhg).unit =
      (etaleModulePullbackAdjunction B S hS (h ≫ g) hhg).unit) :
    (modulePullbackCompIso B S hS h g).hom ≫
        (modulePullbackIsoEtaleModulePullback B S hS (h ≫ g) hhg).hom =
      Functor.whiskerLeft (modulePullback B S hS g)
          (modulePullbackIsoEtaleModulePullback B S hS h hh).hom ≫
        Functor.whiskerRight (modulePullbackIsoEtaleModulePullback B S hS g hg).hom
            (etaleModulePullback.{u, u} B S hS h hh) ≫
          (etaleModulePullbackComp B S hS h g hh hg hhg).hom := by
  have hΦ : ∀ {X' Y' : AlgebraicSpaces B S hS} (f : X' ⟶ Y') (hf : IsEtale B S hS f.hom),
      (Adjunction.leftAdjointUniq (modulePullbackAdjunction B S hS f)
          (etaleModulePullbackAdjunction B S hS f hf)).hom =
        (modulePullbackIsoEtaleModulePullback B S hS f hf).hom := by
    intro X' Y' f hf
    rw [show etaleModulePullbackAdjunction B S hS f hf =
        (modulePullbackAdjunction B S hS f).ofNatIsoLeft
          (modulePullbackIsoEtaleModulePullback B S hS f hf) from rfl,
      Adjunction.leftAdjointUniq_hom_ofNatIsoLeft, Adjunction.leftAdjointUniq_refl,
      Category.id_comp]
  have hC : modulePullbackCompIso B S hS h g =
      Adjunction.leftAdjointUniq (moduleCompAdjunction B S hS h g)
        (modulePullbackAdjunction B S hS (h ≫ g)) := rfl
  rw [hC, ← hΦ (h ≫ g) hhg, Adjunction.leftAdjointUniq_trans, ← hΦ h hh, ← hΦ g hg,
    Adjunction.whiskerLeft_leftAdjointUniq_hom _ _ (modulePullbackAdjunction B S hS g),
    Adjunction.whiskerRight_leftAdjointUniq_hom _ _
      (etaleModulePullbackAdjunction B S hS h hh),
    Adjunction.leftAdjointUniq_trans_assoc,
    ← Adjunction.leftAdjointUniq_hom_ofNatIsoRight _ _ (modulePushforwardCompIso B S hS h g),
    ← Adjunction.leftAdjointUniq_hom_ofNatIsoLeft]
  exact Adjunction.leftAdjointUniq_hom_congr_unit _ _ _ hu.symm

/-- Étale restriction of a morphism of modules is that morphism read over the composite
chart. -/
theorem etaleModulePullback_map_val_app {M N : Modules.{u, u} B S hS A.1 A.2} (φ : M ⟶ N)
    (U : SmallEtale B S hS D.1)
    (m : ((etaleModulePullback.{u, u} B S hS h hh).obj M).val.obj (op U)) :
    ((etaleModulePullback.{u, u} B S hS h hh).map φ).val.app (op U) m =
      φ.val.app (op ((smallEtalePostcomp B S hS h hh).obj U)) m := rfl

/-- If the two adjunctions of étale restriction along the composite `h ≫ g` have the same unit,
then reading a section of the iterated inverse image along `h` and `g` through
`modulePullbackCompIso` is reading it over the two charts in turn. -/
theorem etaleRestrictionComp_of_unit
    (hu : (etaleModulePullbackCompAdjunction B S hS h g hh hg hhg).unit =
      (etaleModulePullbackAdjunction B S hS (h ≫ g) hhg).unit) :
    QuasiCoherentDescent.EtaleRestrictionComp B S hS h g hh hg hhg where
  comp_app M U m := by
    have key := CategoryTheory.NatTrans.congr_app
      (modulePullbackCompIso_hom_comp_etaleRestriction B S hS h g hh hg hhg hu) M
    rw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app] at key
    have key2 := SheafOfModules.val_app_apply_congr key (op U) m
    simp only [SheafOfModules.comp_val_app_apply,
      etaleModulePullbackComp_hom_app_val_app B S hS h g hh hg hhg,
      etaleModulePullback_map_val_app B S hS h hh] at key2
    rwa [← etaleSect_eq B S hS h hh ((modulePullback B S hS g).obj M) U m,
      ← etaleSect_eq B S hS g hg M ((smallEtalePostcomp B S hS h hh).obj U),
      ← etaleSect_eq B S hS (h ≫ g) hhg M U] at key2

end Comp

/-- If along every composable pair of étale morphisms the two adjunctions of étale restriction
along the composite have the same unit, then reading a section of an iterated inverse image
through `modulePullbackCompIso` is reading it over the two charts in turn. -/
theorem modulePullbackCompIsoEtaleRestriction_of_unit
    (hu : ∀ {C A D : AlgebraicSpaces B S hS} (h : D ⟶ A) (g : A ⟶ C)
      (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g.hom)
      (hhg : IsEtale B S hS (h ≫ g).hom),
      (etaleModulePullbackCompAdjunction B S hS h g hh hg hhg).unit =
        (etaleModulePullbackAdjunction B S hS (h ≫ g) hhg).unit) :
    QuasiCoherentDescent.ModulePullbackCompIsoEtaleRestriction B S hS where
  comp_app h g hh hg hhg M U m :=
    (etaleRestrictionComp_of_unit B S hS h g hh hg hhg (hu h g hh hg hhg)).comp_app M U m

end AlgebraicGeometry.Space

end
