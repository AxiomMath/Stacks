module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ChartCoversTop
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageUniformBound
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange

/-!
# Condition (1) of Stacks 0E8A is étale local on the target

Let `a : A ⟶ D` be a morphism of algebraic spaces and `{wᵢ : Wᵢ ⟶ D}` an étale covering, with
base changes `aᵢ : A ×_D Wᵢ ⟶ Wᵢ`. If every `R¹aᵢ,*𝒪` vanishes, then so does `R¹a_*𝒪_A`, and if
every structure map `𝒪_{Wᵢ} ⟶ aᵢ,*𝒪` is an isomorphism, then so is `𝒪_D ⟶ a_*𝒪_A`. These are the
two halves of condition (1) of Stacks 0E8A, so the condition can be checked étale locally on the
target.

## Main results

* `AlgebraicGeometry.C1590Private.isZero_of_isZero_etaleModulePullback_of_isEtaleCovering`: a
  module whose restrictions to the members of an étale covering vanish is zero.
* `AlgebraicGeometry.C1590Private.isZero_firstDirectImage_of_isPullback_etale`: the vanishing of
  `R¹a_*𝒪_A` is étale local on the target.
* `AlgebraicGeometry.C1590Private.isIso_of_isIso_smallEtaleRingRestriction`: a morphism of
  sheaves of rings on the small étale site whose restrictions to the members of an étale covering
  are isomorphisms is an isomorphism.
* `AlgebraicGeometry.C1590Private.isIso_smallEtaleRingRestriction_structureSharp`: the
  restriction of the structure map along an étale morphism is, up to isomorphism, the structure
  map of the base change (Stacks 03LR).
* `AlgebraicGeometry.C1590Private.isIso_structureSharp_of_isPullback_etale`: the invertibility of
  `𝒪_D ⟶ a_*𝒪_A` is étale local on the target.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

namespace AlgebraicGeometry.C1590Private

universe u v

section General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A chart of `D` lying over a member chart of an étale covering is, up to isomorphism, the
composite of a chart of that member. -/
private theorem exists_smallEtalePostcomp_iso_aux {D : AlgebraicSpaces B S hS}
    {ι : Type v} (W : ι → AlgebraicSpaces B S hS) (w : ∀ i, W i ⟶ D)
    (hw : ∀ i, Space.IsEtale B S hS (w i).hom) {V' : Space.SmallEtale B S hS D.1}
    (p : Σ i, Space.SmallEtale B S hS (W i).1) (φ : V' ⟶ Space.memberChart B S hS W w hw p) :
    ∃ W'' : Space.SmallEtale B S hS (W p.1).1,
      Nonempty ((Space.smallEtalePostcomp B S hS (w p.1) (hw p.1)).obj W'' ≅ V') := by
  have hφ : Etale ((BigFppfOver.toScheme B S hS).map φ.hom.left) :=
    Space.etale_toScheme_toOver_map B S hS D.1 φ
  have hW'' : Space.IsEtale B S hS (yoneda.map φ.hom.left ≫ p.2.1.hom) :=
    Space.isEtale_of_presheaf_etale B S hS (Space.etale_comp_of_scheme B S hS φ.hom.left
      p.2.1.hom hφ p.2.2)
  exact ⟨⟨CostructuredArrow.mk (yoneda.map φ.hom.left ≫ p.2.1.hom),
      (Space.isEtale_iff_presheaf_of_yoneda B S hS _).1 hW''⟩,
    ⟨ObjectProperty.isoMk _ (CostructuredArrow.isoMk (Iso.refl _) (by
      exact (Category.id_comp _).trans
        ((CostructuredArrow.w φ.hom).symm.trans (Category.assoc _ _ _).symm)))⟩⟩

/-- **A module whose restrictions to the members of an étale covering vanish is zero.** The
charts of the members cover the final object of the small étale site
(`AlgebraicGeometry.Space.coversTop_of_isEtaleCovering`). A chart lying over one of them is the
composite of a chart of a member, so the sections of the module over it are sections of the
restriction to that member, which vanish. -/
theorem isZero_of_isZero_etaleModulePullback_of_isEtaleCovering {D : AlgebraicSpaces B S hS}
    {ι : Type v} (W : ι → AlgebraicSpaces B S hS) (w : ∀ i, W i ⟶ D)
    (hcov : Space.IsEtaleCovering B S hS (fun i => (W i).1) (fun i => (w i).hom))
    (M : Space.Modules.{u, u} B S hS D.1 D.2)
    (hM : ∀ i, IsZero ((Space.etaleModulePullback.{u, u} B S hS (w i) (hcov.etale i)).obj M)) :
    IsZero M := by
  have hc := Space.coversTop_of_isEtaleCovering B S hS W w hcov
  rw [SheafOfModules.isZero_iff_forall_isZero_obj]
  intro V
  suffices hAb : IsZero (((SheafOfModules.toSheaf _).obj M).obj.obj (Opposite.op V)) by
    have : Subsingleton (M.val.obj (Opposite.op V)) := AddCommGrpCat.isZero_iff_subsingleton.1 hAb
    exact ModuleCat.isZero_iff_subsingleton.2 this
  refine CategoryTheory.Sheaf.isZero_obj_of_mem_of_forall_isZero
    ((SheafOfModules.toSheaf _).obj M) (hc V) ?_
  rintro V' g ⟨p, ⟨φ⟩⟩
  obtain ⟨W'', ⟨e⟩⟩ := exists_smallEtalePostcomp_iso_aux B S hS W w hcov.etale p φ
  have h0 : IsZero (M.val.obj (Opposite.op
      ((Space.smallEtalePostcomp B S hS (w p.1) (hcov.etale p.1)).obj W''))) :=
    (SheafOfModules.isZero_iff_forall_isZero_obj _ _).1 (hM p.1) W''
  have : Subsingleton (M.val.obj (Opposite.op
      ((Space.smallEtalePostcomp B S hS (w p.1) (hcov.etale p.1)).obj W''))) :=
    ModuleCat.isZero_iff_subsingleton.1 h0
  exact (AddCommGrpCat.isZero_iff_subsingleton.2 this).of_iso (M.val.presheaf.mapIso e.op)

/-- A chart of `D` lying over a member chart of an étale covering is, up to isomorphism, the
composite of a chart of that member. -/
theorem exists_smallEtalePostcomp_iso {D : AlgebraicSpaces B S hS}
    {ι : Type v} (W : ι → AlgebraicSpaces B S hS) (w : ∀ i, W i ⟶ D)
    (hw : ∀ i, Space.IsEtale B S hS (w i).hom) {V' : Space.SmallEtale B S hS D.1}
    (p : Σ i, Space.SmallEtale B S hS (W i).1) (φ : V' ⟶ Space.memberChart B S hS W w hw p) :
    ∃ W'' : Space.SmallEtale B S hS (W p.1).1,
      Nonempty ((Space.smallEtalePostcomp B S hS (w p.1) (hw p.1)).obj W'' ≅ V') :=
    exists_smallEtalePostcomp_iso_aux B S hS W w hw p φ

/-- **A morphism of sheaves of rings on the small étale site whose restrictions to the members
of an étale covering are isomorphisms is an isomorphism.** On every chart lying over a member
chart the morphism is bijective, being a component of an isomorphism up to the identification of
such a chart with the composite of a chart of the member. Those charts form a covering sieve of
every chart, so the morphism is locally injective and locally surjective, hence an isomorphism
(`CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`). -/
theorem isIso_of_isIso_smallEtaleRingRestriction {D : AlgebraicSpaces B S hS}
    {ι : Type v} (W : ι → AlgebraicSpaces B S hS) (w : ∀ i, W i ⟶ D)
    (hcov : Space.IsEtaleCovering B S hS (fun i => (W i).1) (fun i => (w i).hom))
    {F G : Sheaf (Space.SmallEtale.topology B S hS D.1) RingCat.{u}} (φ : F ⟶ G)
    (h : ∀ i, IsIso ((Space.smallEtaleRingRestriction B S hS (w i) (hcov.etale i)).map φ)) :
    IsIso φ := by
  have hc := Space.coversTop_of_isEtaleCovering B S hS W w hcov
  have hbij : ∀ (V' : Space.SmallEtale B S hS D.1) (p : Σ i, Space.SmallEtale B S hS (W i).1)
      (_ : V' ⟶ Space.memberChart B S hS W w hcov.etale p),
      Function.Bijective (φ.hom.app (Opposite.op V')) := by
    intro V' p ψ
    obtain ⟨W'', ⟨e⟩⟩ := exists_smallEtalePostcomp_iso B S hS W w hcov.etale p ψ
    have hi : IsIso (((Space.smallEtaleRingRestriction B S hS (w p.1)
        (hcov.etale p.1)).map φ).hom.app (Opposite.op W'')) := by
      have := h p.1
      infer_instance
    have hi' : IsIso (φ.hom.app (Opposite.op
        ((Space.smallEtalePostcomp B S hS (w p.1) (hcov.etale p.1)).obj W''))) := hi
    have hsq := φ.hom.naturality e.hom.op
    have hiso : IsIso (φ.hom.app (Opposite.op V')) := by
      have : φ.hom.app (Opposite.op V') = F.obj.map e.hom.op ≫
          φ.hom.app (Opposite.op ((Space.smallEtalePostcomp B S hS (w p.1)
            (hcov.etale p.1)).obj W'')) ≫ inv (G.obj.map e.hom.op) := by
        rw [reassoc_of% hsq, IsIso.hom_inv_id, Category.comp_id]
      rw [this]
      infer_instance
    exact ConcreteCategory.bijective_of_isIso _
  refine (Sheaf.isLocallyBijective_iff_isIso φ).1 ⟨⟨fun {V} x y hxy => ?_⟩, ⟨fun {V} s => ?_⟩⟩
  · refine (Space.SmallEtale.topology B S hS D.1).superset_covering ?_ (hc V.unop)
    rintro V' g ⟨p, ⟨ψ⟩⟩
    apply (hbij V' p ψ).1
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, φ.hom.naturality,
      ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hxy]
  · refine (Space.SmallEtale.topology B S hS D.1).superset_covering ?_ (hc V)
    rintro V' g ⟨p, ⟨ψ⟩⟩
    obtain ⟨t, ht⟩ := (hbij V' p ψ).2 (G.obj.map g.op s)
    exact ⟨t, ht⟩

end General

section BaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X' X Y' Y : AlgebraicSpaces B S hS} (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

set_option maxHeartbeats 1600000 in
-- `rw` through the topos-pullback ring-sheaf maps of the Stacks 03LR base-change isomorphism
set_option synthInstance.maxHeartbeats 400000 in
/-- The comparison `AlgebraicGeometry.Space.baseChangeRingMap` of the two transports of `𝒪_X` is
an isomorphism: it is induced by the isomorphism of Stacks 03LR. -/
theorem isIso_baseChangeRingMap (sq : IsPullback i f' f g) (hg : Space.IsEtale B S hS g.hom) :
    IsIso (Space.baseChangeRingMap B S hS i f' f g sq hg) := by
  let e : Space.baseChangeRightRingSheaf B S hS f g hg ⟶
      Space.baseChangeLeftRingSheaf B S hS i f'
        (Space.isEtale_of_isPullback B S hS f' i g f sq.flip hg) :=
    Stacks.Sheaves.ToposPullback.pullbackRingSheafMapOfNatTrans
      (Space.SmallEtale.topology B S hS Y'.1) (Space.structureRingSheaf B S hS X)
      (Space.smallEtaleSetPushforwardBaseChangeIso B S hS i f' f g sq hg).inv
  refine ⟨e, ?_, ?_⟩
  · apply (sheafCompose (Space.SmallEtale.topology B S hS Y'.1)
      (forget RingCat.{u})).map_injective
    rw [CategoryTheory.Functor.map_comp, Space.baseChangeRingMap,
      Stacks.Sheaves.ToposPullback.ringSheafMap_pullbackRingSheafMapOfNatTrans,
      Stacks.Sheaves.ToposPullback.ringSheafMap_pullbackRingSheafMapOfNatTrans,
      CategoryTheory.Functor.map_id]
    exact (Space.smallEtaleSetPushforwardBaseChangeIso B S hS i f' f g sq hg).hom_inv_id_app _
  · apply (sheafCompose (Space.SmallEtale.topology B S hS Y'.1)
      (forget RingCat.{u})).map_injective
    rw [CategoryTheory.Functor.map_comp,
      Stacks.Sheaves.ToposPullback.ringSheafMap_pullbackRingSheafMapOfNatTrans,
      Space.baseChangeRingMap,
      Stacks.Sheaves.ToposPullback.ringSheafMap_pullbackRingSheafMapOfNatTrans,
      CategoryTheory.Functor.map_id]
    exact (Space.smallEtaleSetPushforwardBaseChangeIso B S hS i f' f g sq hg).inv_hom_id_app _

/-- **The structure map of a base change along an étale morphism is the restriction of the
structure map.** If the structure map of `f'` is an isomorphism, then so is the restriction of
the structure map of `f` along `g`: by Stacks 03LR
(`AlgebraicGeometry.Space.baseChangeStructureSharp_comp_baseChangeRingMap`) the two differ by
isomorphisms. -/
theorem isIso_smallEtaleRingRestriction_structureSharp (sq : IsPullback i f' f g)
    (hg : Space.IsEtale B S hS g.hom) (h : IsIso (Space.structureSharp B S hS f')) :
    IsIso ((Space.smallEtaleRingRestriction B S hS g hg).map (Space.structureSharp B S hS f)) := by
  have hA : IsIso (Space.baseChangeStructureSharp B S hS i f'
      (Space.isEtale_of_isPullback B S hS f' i g f sq.flip hg)) := by
    rw [Space.baseChangeStructureSharp]
    infer_instance
  have hB := isIso_baseChangeRingMap B S hS i f' f g sq hg
  rw [← Space.baseChangeStructureSharp_comp_baseChangeRingMap B S hS i f' f g sq hg]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hA hB

end BaseChange

section General'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The invertibility of the structure map is étale local on the target.** Let `a : A ⟶ D` be a
morphism of algebraic spaces and `{wᵢ : Wᵢ ⟶ D}` an étale covering with cartesian squares
`A'ᵢ ⟶ A`, `aᵢ : A'ᵢ ⟶ Wᵢ`. If every `𝒪_{Wᵢ} ⟶ aᵢ,*𝒪_{A'ᵢ}` is an isomorphism, then so is
`𝒪_D ⟶ a_*𝒪_A`. -/
theorem isIso_structureSharp_of_isPullback_etale {A D : AlgebraicSpaces B S hS}
    (a : A ⟶ D) {ι : Type v} {W A' : ι → AlgebraicSpaces B S hS} (w : ∀ i, W i ⟶ D)
    (jA : ∀ i, A' i ⟶ A) (a' : ∀ i, A' i ⟶ W i)
    (hcov : Space.IsEtaleCovering B S hS (fun i => (W i).1) (fun i => (w i).hom))
    (hsq : ∀ i, IsPullback (jA i) (a' i) a (w i))
    (h : ∀ i, IsIso (Space.structureSharp B S hS (a' i))) :
    IsIso (Space.structureSharp B S hS a) :=
  isIso_of_isIso_smallEtaleRingRestriction B S hS W w hcov _ fun i =>
    isIso_smallEtaleRingRestriction_structureSharp B S hS (jA i) (a' i) a (w i) (hsq i)
      (hcov.etale i) (h i)

end General'

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The vanishing of `R¹a_*𝒪_A` is étale local on the target.** Let `a : A ⟶ D` be a morphism of
algebraic spaces and `{wᵢ : Wᵢ ⟶ D}` an étale covering with cartesian squares
`A'ᵢ ⟶ A`, `aᵢ : A'ᵢ ⟶ Wᵢ`. If `R¹aᵢ,*𝒪_{A'ᵢ} = 0` for every `i`, then `R¹a_*𝒪_A = 0`. The
restriction of `R¹a_*𝒪_A` to `Wᵢ` is `R¹aᵢ,*` of the restriction of `𝒪_A` to `A'ᵢ` (Stacks 03LX,
`AlgebraicGeometry.Space.moduleHigherPushforwardEtaleBaseChangeIso`), which is `R¹aᵢ,*𝒪_{A'ᵢ}`. -/
theorem isZero_firstDirectImage_of_isPullback_etale {A D : AlgebraicSpaces B integerBase hZ}
    (a : A ⟶ D) {ι : Type v} {W A' : ι → AlgebraicSpaces B integerBase hZ} (w : ∀ i, W i ⟶ D)
    (jA : ∀ i, A' i ⟶ A) (a' : ∀ i, A' i ⟶ W i)
    (hcov : Space.IsEtaleCovering B integerBase hZ (fun i => (W i).1) (fun i => (w i).hom))
    (hsq : ∀ i, IsPullback (jA i) (a' i) a (w i))
    (h : ∀ i, IsZero (firstDirectImage B hZ (a' i))) :
    IsZero (firstDirectImage B hZ a) := by
  refine isZero_of_isZero_etaleModulePullback_of_isEtaleCovering B integerBase hZ W w hcov _
    fun i => ?_
  have hj : Space.IsEtale B integerBase hZ (jA i).hom :=
    Space.isEtale_of_isPullback B integerBase hZ (a' i) (jA i) (w i) a (hsq i).flip
      (hcov.etale i)
  have := Space.hasInjectiveResolutions_modules B integerBase hZ A.1 A.2
  have := Space.hasInjectiveResolutions_modules B integerBase hZ (A' i).1 (A' i).2
  have e₁ := (Space.moduleHigherPushforwardEtaleBaseChangeIso B integerBase hZ (jA i) (a' i) a
    (w i) (hsq i) (hcov.etale i) 1).app (Space.structureSheafModule B integerBase hZ A)
  have e₂ := ((Space.modulePushforward B integerBase hZ (a' i)).rightDerived 1).mapIso
    (Space.etaleModulePullbackStructureSheafModuleIso B integerBase hZ (jA i) hj)
  exact (h i).of_iso (e₁.symm ≪≫ e₂)

end AlgebraicGeometry.C1590Private

end
