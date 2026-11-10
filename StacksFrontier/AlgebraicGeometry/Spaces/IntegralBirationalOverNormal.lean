module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.BirationalIsIso
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleCover
public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalEtaleLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.BirationalDominant
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Normal
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.BirationalIsomorphismLocus
public import StacksFrontier.Topology.Irreducible.GenericPoints

/-!
# Integral birational morphisms onto normal algebraic spaces

An integral birational morphism from a reduced algebraic space to a normal algebraic space is
an isomorphism, provided both spaces are decent with finitely many irreducible components.

The proof is the étale localization of the corresponding statement for schemes. Choosing an
affine étale chart `V → Y` of the target, the base change `U = X ×_Y V` is a scheme because
an integral morphism is representable, and Stacks 0B4D makes `U → V` again birational with
`U` and `V` decent and of finitely many irreducible components. Stacks 0357 splits the normal
affine scheme `V` into integral pieces, over each of which the reduced source becomes integral
because birationality carries the unique generic point across; Stacks 0AB1 then applies. Since
being an isomorphism is a local condition on a jointly locally surjective family of charts,
this suffices.

## Main results

* `AlgebraicGeometry.Space.isIso_of_isIntegralHom_of_isBirational_of_isNormal_of_isReduced`
  is Stacks 0B4E: the morphism is an isomorphism.

## Implementation notes

Reducedness of the source and normality of the target are étale-local properties of schemes in
the sense of `AlgebraicGeometry.Space.HasEtaleLocalProperty`, and the finiteness hypotheses are
about `AlgebraicGeometry.Space.points` with `AlgebraicGeometry.Space.pointTopology`.

The scheme-level input `AlgebraicGeometry.isIso_of_isIntegralHom_of_isBirational_of_isNormal`
(Stacks 0AB1) asks for *integral* source and target, whereas the hypotheses here only give a
reduced source and a normal target. The gap is bridged by
`AlgebraicGeometry.isIso_of_isReduced_of_isBirational_of_isNormal`, which decomposes the normal
target with Stacks 0357 and checks the isomorphism property Zariski-locally over each integral
summand; this is the formal counterpart of the source's "thus we may assume `V` is integral".

Birationality of the chart base change is produced by Stacks 0B4D for the *chosen* categorical
pullback, while the integrality hypothesis represents that pullback by an object of the site.
`AlgebraicGeometry.isBirational_toScheme_map_of_yonedaIso` transports birationality along the
comparison isomorphism and down to the underlying morphism of schemes.

## References

* [Stacks Project, Tag 0B4E](https://stacks.math.columbia.edu/tag/0B4E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Recognising an isomorphism of sheaves on a locally surjective family -/

/-- The disjoint union of a family of presheaves of types, used to express joint local
surjectivity of a family of morphisms as local surjectivity of a single morphism. -/
private def familyPresheaf {C : Type*} [Category.{u} C] {I : Type u}
    (F : I → Cᵒᵖ ⥤ Type u) : Cᵒᵖ ⥤ Type u where
  obj T := Σ i, (F i).obj T
  map f := ↾fun x => ⟨x.1, (F x.1).map f x.2⟩
  map_id T := by
    apply ConcreteCategory.hom_ext
    rintro ⟨i, x⟩
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    rintro ⟨i, x⟩
    simp

/-- The morphism out of `AlgebraicGeometry.familyPresheaf` determined by a family of morphisms
with common target. -/
private def familyPresheafDesc {C : Type*} [Category.{u} C] {I : Type u}
    (F : I → Cᵒᵖ ⥤ Type u) {G : Cᵒᵖ ⥤ Type u}
    (g : ∀ i, F i ⟶ G) : familyPresheaf F ⟶ G where
  app T := ↾fun x => (g x.1).app T x.2
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨i, x⟩
    exact (g i).naturality_apply f x

/-- A morphism of sheaves of types is an isomorphism as soon as its base change along each
member of a jointly locally surjective family is an isomorphism.

Local injectivity and local surjectivity are both read off the covering sieve of the family,
and `CategoryTheory.Sheaf.isLocallyBijective_iff_isIso` turns them into the isomorphism. -/
private theorem isIso_of_isIso_familyPullback_snd_of_isLocallySurjective
    {C : Type*} [Category.{u} C] (J : GrothendieckTopology C)
    {I : Type u} {F G : Cᵒᵖ ⥤ Type u} {H : I → Cᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (g : ∀ i, H i ⟶ G)
    (hG : Presheaf.IsLocallySurjective J (familyPresheafDesc H g))
    (hFsheaf : Presheaf.IsSheaf J F) (hGsheaf : Presheaf.IsSheaf J G)
    (hpb : ∀ i, IsIso (pullback.snd f (g i))) : IsIso f := by
  have hLI : Presheaf.IsLocallyInjective J f := by
    refine ⟨?_⟩
    intro T x y hxy
    apply J.superset_covering ?_ (hG.imageSieve_mem (f.app T x))
    rintro T' i ⟨⟨k, a⟩, ha⟩
    have hga : (g k).app (Opposite.op T') a = G.map i.op (f.app T x) := by
      simpa [familyPresheafDesc] using ha
    let α := yonedaEquiv.symm (F.map i.op x)
    let β := yonedaEquiv.symm (F.map i.op y)
    let γ := yonedaEquiv.symm a
    have key : ∀ w : F.obj (Opposite.op T'), f.app (Opposite.op T') w = (g k).app _ a →
        yonedaEquiv.symm w ≫ f = γ ≫ g k := fun w hw => by
      rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right, hw]
    have hα : α ≫ f = γ ≫ g k := key _ (by rw [f.naturality_apply, hga])
    have hβ : β ≫ f = γ ≫ g k :=
      key _ (by rw [f.naturality_apply, hga]; exact congrArg (G.map i.op) (by simpa using hxy.symm))
    have hz : pullback.lift α γ hα ≫ pullback.snd f (g k) =
        pullback.lift β γ hβ ≫ pullback.snd f (g k) := by
      rw [pullback.lift_snd, pullback.lift_snd]
    have := hpb k
    have hfst : α = β := by
      simpa only [pullback.lift_fst] using
        congrArg (fun m => m ≫ pullback.fst f (g k)) ((cancel_mono (pullback.snd f (g k))).1 hz)
    change F.map i.op x = F.map i.op y
    simpa [α, β] using congrArg yonedaEquiv hfst
  have hLS : Presheaf.IsLocallySurjective J f := by
    refine ⟨?_⟩
    intro T s
    apply J.superset_covering ?_ (hG.imageSieve_mem s)
    rintro T' i ⟨⟨k, a⟩, ha⟩
    have hga : (g k).app (Opposite.op T') a = G.map i.op s := by
      simpa [familyPresheafDesc] using ha
    let γ := yonedaEquiv.symm a
    have := hpb k
    let z := γ ≫ inv (pullback.snd f (g k))
    have hfac : (z ≫ pullback.fst f (g k)) ≫ f = yonedaEquiv.symm (G.map i.op s) := by
      calc (z ≫ pullback.fst f (g k)) ≫ f
          = z ≫ (pullback.fst f (g k) ≫ f) := by rw [Category.assoc]
        _ = z ≫ (pullback.snd f (g k) ≫ g k) := by rw [pullback.condition]
        _ = γ ≫ g k := by simp [z]
        _ = yonedaEquiv.symm ((g k).app (Opposite.op T') a) :=
            yonedaEquiv_symm_naturality_right _ _ _
        _ = yonedaEquiv.symm (G.map i.op s) := congrArg yonedaEquiv.symm hga
    refine ⟨yonedaEquiv (z ≫ pullback.fst f (g k)), ?_⟩
    simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using congrArg yonedaEquiv hfac
  let fsheaf : (⟨F, hFsheaf⟩ : Sheaf J (Type u)) ⟶ ⟨G, hGsheaf⟩ := ObjectProperty.homMk f
  have : IsIso fsheaf := (Sheaf.isLocallyBijective_iff_isIso fsheaf).mp
    ⟨(Sheaf.isLocallyInjective_sheafToPresheaf_map_iff fsheaf).2 hLI,
    (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff fsheaf).2 hLS⟩
  change IsIso ((sheafToPresheaf J (Type u)).map fsheaf)
  exact Functor.map_isIso (sheafToPresheaf J (Type u)) fsheaf

/-! ### The scheme-level statement with a merely normal target -/

/-- **Stacks 0AB1 with a merely normal target.** An integral birational morphism from a reduced
scheme to a normal scheme with finitely many irreducible components is an isomorphism.

Stacks 0357 presents the target as a coproduct of normal integral schemes; being an
isomorphism is Zariski-local on the target, and over each summand the reduced source becomes
integral by `AlgebraicGeometry.integral_of_reduced_birational_to_integral`, so
`AlgebraicGeometry.isIso_of_isIntegralHom_of_isBirational_of_isNormal` applies. -/
@[ega "II 8.11.2" "special case",
  ega "IV 17.15.14.1" "(i), special case",
  ega "IV 8.12.10" "special case",
  ega "IV 8.12.10.1" "more general"]
private theorem isIso_of_isReduced_of_isBirational_of_isNormal
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced X] [IsNormal Y] [IsIntegralHom f]
    (hf : IsBirational f) (hfinite : (irreducibleComponents Y).Finite) : IsIso f := by
  obtain ⟨ι, Z, hnormalZ, hintegralZ, ⟨e⟩⟩ :=
    (isNormal_iff_exists_iso_coproduct
      (fun U _ => finite_irreducibleComponents_of_isOpenEmbedding U.ι
        U.ι.isOpenEmbedding hfinite)).mp inferInstance
  have hf' : IsBirational (f ≫ e.hom) := by
    refine ⟨Set.BijOn.mk ?_ ?_ ?_, ?_⟩
    · intro x hx
      exact (Homeomorph.mem_genericPoints_iff e.hom.homeomorph (f x)).2 (hf.bijOn.mapsTo hx)
    · intro x hx x' hx' hxx'
      exact hf.bijOn.injOn hx hx' (e.hom.homeomorph.injective (by simpa using hxx'))
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := hf.bijOn.surjOn
        ((Homeomorph.mem_genericPoints_iff e.hom.homeomorph.symm y).2 hy)
      refine ⟨x, hx, ?_⟩
      change e.hom.homeomorph (f x) = y
      rw [hxy]
      exact e.hom.homeomorph.apply_symm_apply y
    · intro x hx
      have := hf.isIso_stalkMap x hx
      rw [Scheme.Hom.stalkMap_comp]
      exact (asIso ((e.hom).stalkMap (f x)) ≪≫ asIso (f.stalkMap x)).isIso_hom
  let sigma : (∐ Z).OpenCover := sigmaOpenCover Z
  have : IsIso (f ≫ e.hom) :=
    (IsZariskiLocalAtTarget.iff_of_iSup_eq_top
      (P := .isomorphisms Scheme) (fun i => (sigma.f i).opensRange)
      (by simpa using sigma.iSup_opensRange)).2 fun i => by
      let Ui := (sigma.f i).opensRange
      let ei : sigma.X i ≅ Ui.toScheme :=
        IsOpenImmersion.isoOfRangeEq (sigma.f i) Ui.ι (by simp [Ui])
      have : IsIntegral (sigma.X i) := hintegralZ i
      have : IsIntegral Ui.toScheme := IsIntegral.of_isIso ei.hom
      have : IsNormal Ui.toScheme := ObjectProperty.prop_of_iso IsNormal ei (hnormalZ i)
      have : IsIntegralHom ((f ≫ e.hom) ∣_ Ui) :=
        MorphismProperty.IsStableUnderBaseChange.of_isPullback
          (isPullback_morphismRestrict (f ≫ e.hom) Ui).flip inferInstance
      have hbirRes : IsBirational ((f ≫ e.hom) ∣_ Ui) :=
        birational_morphismRestrict (f ≫ e.hom) hf' Ui
      have : IsIntegral ((f ≫ e.hom) ⁻¹ᵁ Ui).toScheme :=
        integral_of_reduced_birational_to_integral _ hbirRes
      exact isIso_of_isIntegralHom_of_isBirational_of_isNormal _ hbirRes
  exact IsIso.of_isIso_comp_right f e.hom

/-! ### Transporting birationality to the underlying morphism of schemes -/

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on the big fppf site times out at the default
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
instance hasPullbacks_presheaf_IntegralBirationalOverNormal
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Shortcut for pullbacks of presheaves on the big fppf site. -/
instance (priority := high) hasPullback_presheaf_IntegralBirationalOverNormal
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
-- instance search while `simpa` unfolds `genericLocalRingMap` to match the stalk map
-- (`HasLimitsOfShape` of presheaves on the big fppf site) times out at the default
/-- Birationality of a morphism of algebraic spaces with representable target and with source
identified with a representable presheaf descends to the underlying morphism of schemes.

The two comparison homeomorphisms of `AlgebraicGeometry.Space.schemePointsHomeomorph` turn the
bijection on generic points into the corresponding bijection of scheme points, and the charts
`c` and `d` built from the identification compute the induced map of local rings through
`AlgebraicGeometry.Space.exists_genericLocalRingMap` as the stalk map of the morphism. -/
private theorem isBirational_toScheme_map_of_yonedaIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U V : BigFppfOver B S hS)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hV : IsAlgebraicSpace B S hS (yoneda.obj V))
    (hdecentF : Space.IsDecentSpace B S hS F)
    (hdecentV : Space.IsDecentSpace B S hS (yoneda.obj V))
    (hfiniteF : letI := Space.pointTopology B S hS F
      (irreducibleComponents (Space.points B S hS F)).Finite)
    (hfiniteV : letI := Space.pointTopology B S hS (yoneda.obj V)
      (irreducibleComponents (Space.points B S hS (yoneda.obj V))).Finite)
    (e : yoneda.obj U ≅ F) (f : F ⟶ yoneda.obj V) (g : U ⟶ V)
    (hcomm : e.hom ≫ f = yoneda.map g)
    (hbir : Space.IsBirational B S hS hF hV hdecentF hdecentV hfiniteF hfiniteV f) :
    IsBirational ((BigFppfOver.toScheme B S hS).map g) := by
  have hdenseF := Space.hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hF hdecentF
  have hdenseV := Space.hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hV hdecentV
  let _ : TopologicalSpace (Space.points B S hS F) := Space.pointTopology B S hS F
  let _ : TopologicalSpace (Space.points B S hS (yoneda.obj U)) :=
    Space.pointTopology B S hS (yoneda.obj U)
  let _ : TopologicalSpace (Space.points B S hS (yoneda.obj V)) :=
    Space.pointTopology B S hS (yoneda.obj V)
  let q := (BigFppfOver.toScheme B S hS).map g
  let eU := Space.schemePointsHomeomorph B S hS U
  let eV := Space.schemePointsHomeomorph B S hS V
  let ePointsEquiv : Space.points B S hS (yoneda.obj U) ≃ Space.points B S hS F :=
    { toFun := Space.pointsMap B S hS (yoneda.obj U) e.hom
      invFun := Space.pointsMap B S hS F e.inv
      left_inv := fun x => by
        have h := congrFun (Space.pointsMap_comp B S hS (yoneda.obj U) e.hom e.inv) x
        rw [e.hom_inv_id, Space.pointsMap_id] at h
        exact h.symm
      right_inv := fun x => by
        have h := congrFun (Space.pointsMap_comp B S hS F e.inv e.hom) x
        rw [e.inv_hom_id, Space.pointsMap_id] at h
        exact h.symm }
  let ePoints : Space.points B S hS (yoneda.obj U) ≃ₜ Space.points B S hS F :=
    { toEquiv := ePointsEquiv
      continuous_toFun := Space.continuous_pointsMap B S hS e.hom
      continuous_invFun := Space.continuous_pointsMap B S hS e.inv }
  let eSource : ((BigFppfOver.toScheme B S hS).obj U : Type u) ≃ₜ Space.points B S hS F :=
    eU.symm.trans ePoints
  have h1 : Space.pointsMap B S hS (yoneda.obj U) (yoneda.map g) =
      Space.pointsMap B S hS F f ∘ Space.pointsMap B S hS (yoneda.obj U) e.hom := by
    rw [← hcomm, Space.pointsMap_comp]
  have h2 := Space.pointsMap_yoneda_eq_conj B S hS g
  have hqeq : ∀ x, eV (Space.pointsMap B S hS F f (eSource x)) = q x := by
    intro x
    have h4 : Space.pointsMap B S hS F f
        (Space.pointsMap B S hS (yoneda.obj U) e.hom (eU.symm x)) =
        eV.symm (q (eU (eU.symm x))) :=
      (congrFun h1 (eU.symm x)).symm.trans (congrFun h2 (eU.symm x))
    have h5 : eSource x = Space.pointsMap B S hS (yoneda.obj U) e.hom (eU.symm x) := rfl
    rw [h5, h4, eU.apply_symm_apply, eV.apply_symm_apply]
  obtain ⟨hbijAlg, hstalkAlg⟩ := hbir
  refine ⟨?_, ?_⟩
  · have hcomp : Set.BijOn ((eV : _ → _) ∘ (Space.pointsMap B S hS F f ∘ eSource))
        (genericPoints ((BigFppfOver.toScheme B S hS).obj U))
        (genericPoints ((BigFppfOver.toScheme B S hS).obj V)) :=
      (Homeomorph.bijOn_genericPoints eV).comp
        (hbijAlg.comp (Homeomorph.bijOn_genericPoints eSource))
    exact hcomp.congr (fun x _ => hqeq x)
  · intro x hx
    have hxF : eSource x ∈ genericPoints (Space.points B S hS F) :=
      (eSource.mem_genericPoints_iff x).2 hx
    have hyF := hbijAlg.mapsTo hxF
    obtain ⟨pX, hpX⟩ := Space.exists_fieldValuedPoint_schemePoint_eq B S hS U x
    obtain ⟨pY, hpY⟩ := Space.exists_fieldValuedPoint_schemePoint_eq B S hS V (q x)
    have hclassX : pX.class B S hS (yoneda.obj U) = eU.symm x := by
      apply eU.injective
      rw [eU.apply_symm_apply]
      change Space.pointsToScheme B S hS U (pX.class B S hS (yoneda.obj U)) = x
      rw [Space.pointsToScheme_class]
      exact hpX
    have hclassY : pY.class B S hS (yoneda.obj V) =
        Space.pointsMap B S hS F f (eSource x) := by
      apply eV.injective
      rw [hqeq x]
      change Space.pointsToScheme B S hS V (pY.class B S hS (yoneda.obj V)) = q x
      rw [Space.pointsToScheme_class]
      exact hpY
    let c : Space.GenericChart B S hS (eSource x) :=
      { U := U
        immersion := e.hom
        isOpen := by
          change (MorphismProperty.presheaf (MorphismProperty.inverseImage
            (@IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS))) e.hom
          exact MorphismProperty.of_isIso _ e.hom
        point := pX
        mapsTo := by
          rw [hclassX]
          rfl }
    let d : Space.GenericChart B S hS (Space.pointsMap B S hS F f (eSource x)) :=
      { U := V
        immersion := 𝟙 _
        isOpen := by
          change (MorphismProperty.presheaf (MorphismProperty.inverseImage
            (@IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS))) (𝟙 (yoneda.obj V))
          exact MorphismProperty.of_isIso _ (𝟙 (yoneda.obj V))
        point := pY
        mapsTo := by
          rw [Space.pointsMap_id]
          exact hclassY }
    have hcommCharts : c.immersion ≫ f = yoneda.map g ≫ d.immersion := by
      simp only [c, d, Category.comp_id]
      exact hcomm
    have hpoint : q (Space.schemePoint B S hS c.U c.point) =
        Space.schemePoint B S hS d.U d.point := by
      change q (Space.schemePoint B S hS U pX) = Space.schemePoint B S hS V pY
      rw [hpX, hpY]
    let hgeneric := Space.exists_genericLocalRingMap B S hS hF hV hdenseF hdenseV
      hfiniteF hfiniteV f (eSource x) hxF hyF
    have hformula := hgeneric.choose_spec c d g hcommCharts hpoint
    have hIsoφ : IsIso hgeneric.choose := by
      simpa [Space.genericLocalRingMap] using hstalkAlg (eSource x) hxF
    rw [hformula] at hIsoφ
    let _ := hIsoφ
    let _ : IsIso (eqToHom (congrArg
        (fun z => ((BigFppfOver.toScheme B S hS).obj d.U).presheaf.stalk z) hpoint.symm) ≫
        (q.stalkMap (Space.schemePoint B S hS c.U c.point) ≫
        (Space.chartStalkIso B S hS hF hdenseF hfiniteF (eSource x) hxF c).hom)) := by
      simpa only [Category.assoc] using
        (IsIso.of_isIso_comp_left
          (Space.chartStalkIso B S hS hV hdenseV hfiniteV _ hyF d).inv _)
    have hIso2 : IsIso (q.stalkMap (Space.schemePoint B S hS c.U c.point) ≫
        (Space.chartStalkIso B S hS hF hdenseF hfiniteF (eSource x) hxF c).hom) :=
      IsIso.of_isIso_comp_left (eqToHom (congrArg
        (fun z => ((BigFppfOver.toScheme B S hS).obj d.U).presheaf.stalk z) hpoint.symm)) _
    have hIso3 : IsIso (q.stalkMap (Space.schemePoint B S hS c.U c.point)) :=
      IsIso.of_isIso_comp_right _
        (Space.chartStalkIso B S hS hF hdenseF hfiniteF (eSource x) hxF c).hom
    change IsIso (q.stalkMap x)
    rw [← hpX]
    exact hIso3

/-! ### A jointly locally surjective family of affine étale charts -/

/-- An algebraic space admits a family of affine étale charts which is jointly locally
surjective for the fppf topology.

A surjective étale atlas is refined by affine objects of the site, and the two covering sieves
compose: the atlas base-changes to a surjective étale morphism of the site over any test
object, and the affine refinement of the atlas pulls back to that base change. -/
private theorem exists_affine_etale_family_isLocallySurjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y) :
    ∃ (I : Type u) (V : I → BigFppfOver B S hS) (g : ∀ i, yoneda.obj (V i) ⟶ Y),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (V i))) ∧
      (∀ i, Space.IsEtale B S hS (g i)) ∧
      Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
        (familyPresheafDesc (fun i => yoneda.obj (V i)) g) := by
  obtain ⟨U, a, hasurj, haetale⟩ := hY.exists_atlas
  obtain ⟨I, V, π, haff, hπetale, hπcover⟩ := BigFppfOver.exists_affine_etale_cover B S hS U
  refine ⟨I, V, fun i => yoneda.map (π i) ≫ a, haff, ?_, ?_⟩
  · intro i
    refine (Space.isEtale_iff_presheaf_of_yoneda B S hS _).2 ?_
    exact Space.etale_comp_of_scheme B S hS (π i) a
      ((Space.presheaf_yoneda_map_etale_iff B S hS (π i)).1
        ((Space.isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map (π i))).1 (hπetale i)))
      haetale
  · refine ⟨?_⟩
    intro T s
    let w : yoneda.obj T ⟶ Y := yonedaEquiv.symm s
    have hrep := haetale.rep
    let u₀ : hrep.pullback w ⟶ U := Yoneda.fullyFaithful.preimage (hrep.fst w)
    have hu₀ : yoneda.map u₀ = hrep.fst w := Yoneda.fullyFaithful.map_preimage _
    have hEt : Etale ((BigFppfOver.toScheme B S hS).map (hrep.snd w)) :=
      haetale.property w (hrep.fst w) (hrep.snd w) (hrep.isPullback w)
    have hSu : Surjective ((BigFppfOver.toScheme B S hS).map (hrep.snd w)) :=
      hasurj.property w (hrep.fst w) (hrep.snd w) (hrep.isPullback w)
    have hsq : yoneda.map u₀ ≫ a = yoneda.map (hrep.snd w) ≫ w := by
      rw [hu₀]
      exact (hrep.isPullback w).w
    refine (BigFppfOver.topology B S hS).transitive
      (Space.sieve_generate_singleton_mem_topology_over B S hS (hrep.snd w) hSu hEt) _ ?_
    rintro T₁ k ⟨T₂, c, d, hd, hfac⟩
    cases hd
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      ((BigFppfOver.topology B S hS).pullback_stable (c ≫ u₀) hπcover)
    rintro T₃ m ⟨T₄, t, p, hp, hfacm⟩
    cases hp with
    | mk i =>
      refine ⟨⟨i, t⟩, ?_⟩
      have hmor : yoneda.map t ≫ (yoneda.map (π i) ≫ a) = yoneda.map (m ≫ k) ≫ w := by
        calc yoneda.map t ≫ (yoneda.map (π i) ≫ a)
            = yoneda.map (t ≫ π i) ≫ a := by rw [Functor.map_comp, Category.assoc]
          _ = yoneda.map (m ≫ c ≫ u₀) ≫ a := by rw [hfacm]
          _ = yoneda.map m ≫ yoneda.map c ≫ yoneda.map u₀ ≫ a := by
              rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
          _ = yoneda.map m ≫ yoneda.map c ≫ yoneda.map (hrep.snd w) ≫ w := by rw [hsq]
          _ = yoneda.map m ≫ yoneda.map (c ≫ hrep.snd w) ≫ w := by
              rw [Functor.map_comp, Category.assoc]
          _ = yoneda.map (m ≫ k) ≫ w := by
              rw [hfac, Functor.map_comp, Category.assoc]
      have hleft : (yoneda.map (π i) ≫ a).app (Opposite.op T₃) t =
          yonedaEquiv (yoneda.map t ≫ (yoneda.map (π i) ≫ a)) := by
        rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
      have hright : Y.map (m ≫ k).op s = yonedaEquiv (yoneda.map (m ≫ k) ≫ w) := by
        rw [← yonedaEquiv_naturality]
        congr 1
        exact (Equiv.apply_symm_apply yonedaEquiv s).symm
      change (yoneda.map (π i) ≫ a).app (Opposite.op T₃) t = Y.map (m ≫ k).op s
      rw [hleft, hright, hmor]

namespace Space

/-- **Stacks 0B4E.** An integral birational morphism from a reduced algebraic space to a normal
algebraic space is an isomorphism, provided both are decent with finitely many irreducible
components.

Being an isomorphism is checked on the jointly locally surjective family of affine étale charts
`V i → Y` supplied by
`AlgebraicGeometry.exists_affine_etale_family_isLocallySurjective`. Integrality of `f`
represents the base change `X ×_Y V i` by an affine object `W` of the site, so the chart base
change is a morphism of schemes `W → V i`; it is birational by Stacks 0B4D together with
`AlgebraicGeometry.isBirational_toScheme_map_of_yonedaIso`, its source is reduced and its
target normal with finitely many irreducible components, whence it is an isomorphism by
`AlgebraicGeometry.isIso_of_isReduced_of_isBirational_of_isNormal`. -/
@[stacks 0B4E, ega "IV 8.12.10.1"]
theorem isIso_of_isIntegralHom_of_isBirational_of_isNormal_of_isReduced
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hdecentX : IsDecentSpace B S hS X) (hdecentY : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (f : X ⟶ Y)
    (hintegral : IsIntegralHom B S hS f)
    (hbirational : IsBirational B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY f)
    (hnormalY : IsNormal B S hS Y)
    (hreducedX : HasEtaleLocalProperty B S hS X
      (fun Z : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced Z)) :
    IsIso f := by
  obtain ⟨I, V, g, haff, hgetale, hls⟩ :=
    exists_affine_etale_family_isLocallySurjective B S hS hY
  refine isIso_of_isIso_familyPullback_snd_of_isLocallySurjective
    (BigFppfOver.topology B S hS) f g hls hX.isSheaf hY.isSheaf ?_
  intro i
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj (V i)) := haff i
  obtain ⟨W, p, q, hpb, haffW, hintp⟩ := hintegral (V i) (haff i) (g i)
  -- the chart base change is reduced, because it is étale over the reduced source
  have hWred : _root_.AlgebraicGeometry.IsReduced
      ((BigFppfOver.toScheme B S hS).obj W) :=
    (exists_atlas_iff_forall_etale B S hS X
      (fun Z : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced Z) hX).mp hreducedX W q
      ((isEtale_iff_presheaf_of_yoneda B S hS q).1
        (isEtale_of_isPullback_yoneda B S hS hpb.flip (hgetale i)))
  -- the chart is normal, being étale over the normal target
  have hVnormal : _root_.AlgebraicGeometry.IsNormal
      ((BigFppfOver.toScheme B S hS).obj (V i)) :=
    (isNormal_iff_forall_etale B S hS Y hY).mp hnormalY (V i) (g i)
      ((isEtale_iff_presheaf_of_yoneda B S hS (g i)).1 (hgetale i))
  -- the chart has finitely many irreducible components
  have hVfin : (irreducibleComponents
      ((BigFppfOver.toScheme B S hS).obj (V i) : Type u)).Finite := by
    let _ : TopologicalSpace (points B S hS (yoneda.obj (V i))) :=
      pointTopology B S hS (yoneda.obj (V i))
    exact finite_irreducibleComponents_of_isOpenEmbedding
      (schemePointsHomeomorph B S hS (V i)).symm
      (schemePointsHomeomorph B S hS (V i)).symm.isOpenEmbedding
      (finite_irreducibleComponents_of_isEtale_of_isAffine B S hS hY hdecentY hfiniteY
        (V i) (g i) (hgetale i))
  -- birationality descends to the underlying morphism of schemes
  have hbirp : _root_.AlgebraicGeometry.IsBirational
      ((BigFppfOver.toScheme B S hS).map p) :=
    isBirational_toScheme_map_of_yonedaIso B S hS W (V i) _ _ _ _ _ _
      hpb.isoPullback (pullback.snd f (g i)) p hpb.isoPullback_hom_snd
      (isBirational_pullback_snd_of_isEtale B S hS hX hY hdecentX hdecentY
        hfiniteX hfiniteY f hbirational (V i) (g i) (hgetale i))
  -- the scheme-level criterion applies
  have _ : _root_.AlgebraicGeometry.IsIntegralHom
    ((BigFppfOver.toScheme B S hS).map p) := hintp
  have _ : IsIso ((BigFppfOver.toScheme B S hS).map p) :=
    isIso_of_isReduced_of_isBirational_of_isNormal _ hbirp hVfin
  have _ : IsIso p := isIso_of_reflects_iso p (BigFppfOver.toScheme B S hS)
  have : IsIso (hpb.isoPullback.hom ≫ pullback.snd f (g i)) := by
    rw [hpb.isoPullback_hom_snd]
    infer_instance
  exact IsIso.of_isIso_comp_left hpb.isoPullback.hom _

end Space

end AlgebraicGeometry

end
