module

public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRingFlatChart
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRingFlatMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalChartSmoothNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSmoothClosure
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparableChartPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRingFieldExtension

/-!
# A point of a smooth chart, and the closed fibre of its completion (Stacks 0DR2, Step III)

Step III of the proof of **Stacks 0DR2** moves the point `x₀ : Spec k ⟶ 𝒳` to a point
`u₀ ⟶ U ⟶ 𝒳` of a smooth chart, at which the versal ring is the completed local ring
`𝒪^∧_{U, u₀}` and the morphism to `𝒳` is the composition `Spec(𝒪^∧_{U, u₀}) ⟶ U ⟶ 𝒳`, flat as a
composition of flat morphisms. This file supplies the chart side of that move: for a smooth
chart object `x` over `U`, a finite type point `u₀ ∈ U`, and an object `xₗ` over `Spec l` mapping
to `x` over a morphism `Spec l ⟶ U` through `u₀`, it produces the complete local restriction
`xR` of `x` over `𝒪^∧_{U, u₀}` (flat, with versal formal object `ξ`) together with a morphism
`xₗ ⟶ ξ_0` to the closed fibre of `ξ` lying over a field extension `κ(ξ) ⟶ l`.

## Main results

* `AlgebraicGeometry.Stack.isRelativelySmooth_objectMorphism_of_smoothObject`: a smooth object is
  smooth in the sense of Stacks 04XB (Stacks 06FM).
* `AlgebraicGeometry.Stack.exists_eq_specMap_comp_fromSpecResidueField`: a morphism from the
  spectrum of a field factors through the residue field of the image of the closed point.
* `AlgebraicGeometry.Stack.exists_closedFibre_hom_of_smoothObject`: the chart side of Step III.
* `AlgebraicGeometry.Stack.exists_closedFibre_hom_of_smoothObject_completedLocalRing` and
  `AlgebraicGeometry.Stack.exists_chartPoint_closedFibre_completedLocalRing`: the same, together
  with the chart and the identification of the versal ring with its completed local ring, used
  for Stacks 0DZS.

## References

* [Stacks Project, Tag 0DR2](https://stacks.math.columbia.edu/tag/0DR2)
* [Stacks Project, Tag 0DQZ](https://stacks.math.columbia.edu/tag/0DQZ)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Stack

universe u w

/-- **A smooth object names a smooth 1-morphism in the sense of Stacks 04XB.** The 1-morphism is
representable by algebraic spaces, its source being a scheme and its target an algebraic stack,
and the existential smooth-diagram test of Stacks 075U is the relative property of Stacks 03YK
by Stacks 06FM. -/
theorem isRelativelySmooth_objectMorphism_of_smoothObject (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)
    {x : 𝒳.val.val.obj} (hx : smoothObject.{u, w} B S hS 𝒳 x) :
    IsRelativelySmooth B S hS (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl)) := by
  let smoothP : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ h => Space.IsSmooth B S hS h
  have hsm : Space.IsSmoothLocalOnSourceAndTarget B S hS smoothP :=
    Space.isSmoothLocalOnSourceAndTarget_smooth B S hS
  let : (spaceProperty B S hS smoothP).IsStableUnderBaseChange :=
    Space.isSmooth_isStableUnderBaseChange B S hS
  let : (spaceProperty B S hS smoothP).IsLocalAtTarget
      (Space.Topology.fpqc.precoverage.{u, u + 1} B S hS) :=
    Space.smooth_isLocalAtTarget_fpqc B S hS
  let : (spaceProperty B S hS smoothP).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le
      (L := Space.Topology.fpqc.precoverage.{u, u + 1} B S hS)
      (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  have hrx : Stack.IsRepresentableByAlgebraicSpaces B S hS
      (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl)).hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS _) _
  exact ⟨hrx, hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram.{u, u + 1} B S hS smoothP hsm
    _ hrx hx⟩

/-- **A morphism from the spectrum of a field factors through the residue field of the image of
the closed point.** This is `AlgebraicGeometry.Scheme.SpecToEquivOfField` read at a prescribed
image point. -/
theorem exists_eq_specMap_comp_fromSpecResidueField {K : Type u} [Field K] {X : Scheme.{u}}
    (a : Spec (.of K) ⟶ X) {x : X} (ha : a.base (closedPoint K) = x) :
    ∃ φ : X.residueField x ⟶ CommRingCat.of K, a = Spec.map φ ≫ X.fromSpecResidueField x := by
  subst ha
  exact ⟨_, ((Scheme.SpecToEquivOfField K X).symm_apply_apply a).symm⟩

/-- The morphism of schemes underlying a morphism of `𝒳`, followed by the structure morphism of
its target, is the structure morphism of its source. -/
theorem schemeMap_comp_hom {S : Scheme.{u}} {F : Type*} [Category F] (q : F ⥤ Over S)
    {y z : F} {Y Z : Over S} (hy : q.obj y = Y) (hz : q.obj z = Z) (f : y ⟶ z) :
    Deformation.Artin.schemeMap q hy hz f ≫ Z.hom = Y.hom := by
  subst hy hz
  simp [Deformation.Artin.schemeMap]

/-- The morphism of schemes underlying a morphism of `𝒳` is locally of finite type when the
structure morphism of its source is. -/
private theorem locallyOfFiniteType_schemeMap {S : Scheme.{u}} {F : Type*} [Category F]
    (q : F ⥤ Over S) {y z : F} {Y Z : Over S} (hy : q.obj y = Y) (hz : q.obj z = Z) (f : y ⟶ z)
    (h : LocallyOfFiniteType Y.hom) :
    LocallyOfFiniteType (Deformation.Artin.schemeMap q hy hz f) := by
  rw [← schemeMap_comp_hom q hy hz f] at h
  exact locallyOfFiniteType_of_comp _ Z.hom

/-- The left part of a morphism of `Over S` is recovered from its underlying morphism of schemes
read through identifications of the endpoints. -/
theorem map_left_eq_schemeMap {S : Scheme.{u}} {F : Type*} [Category F] (q : F ⥤ Over S)
    {y z : F} {Y Z : Over S} (hy : q.obj y = Y) (hz : q.obj z = Z) (f : y ⟶ z) :
    (q.map f).left = eqToHom (congrArg Over.left hy) ≫ Deformation.Artin.schemeMap q hy hz f ≫
      eqToHom (congrArg Over.left hz).symm := by
  subst hy hz
  simp [Deformation.Artin.schemeMap]

/-- **The chart side of Step III of the proof of Stacks 0DR2, with the completed local ring.**
This is `AlgebraicGeometry.Stack.exists_closedFibre_hom_of_smoothObject` together with the
identification of the base of `ξ` with `𝒪^∧_{U, u₀}` over `S`, which Step III of the proof of
Stacks 0DZS uses. The rest of the statement is the following. In the versal situation, let `x`
be a smooth object of `𝒳` over a scheme `U` locally of finite type and quasi-compact over `S`, let
`u₀ ∈ U` be a finite type point whose completed local ring lies in the site and whose image lies
in an affine open `Spec Λ ⊆ S`, and let `τ : xₗ ⟶ x` be a morphism from an object over
`Spec l ⟶ Spec Λ ⟶ S` lying over a morphism `Spec l ⟶ U` through `u₀`. Then the complete local
restriction `xR` of `x` over `𝒪^∧_{U, u₀}` is a flat object whose formal object `ξ` is versal,
and `τ` factors through a morphism `η' : xₗ ⟶ ξ_0` to the closed fibre of `ξ`, lying over the
spectrum of a finite field extension `κ(ξ) ⟶ l` compatible with the `Λ`-algebra structures.
Moreover `xR` maps to `x` by a morphism lying over a flat morphism of schemes, the canonical
`Spec(𝒪^∧_{U, u₀}) ⟶ U`. -/
theorem exists_closedFibre_hom_of_smoothObject_completedLocalRing (D : VersalSituation.{u, w})
    (U : Over D.S) [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (x : D.𝒳.val.val.obj) (hx : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x = U)
    (hxsm : smoothObject.{u, w} D.B D.S D.hS D.𝒳 x)
    (u₀ : U.left) (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    (hC : D.B.Contains (Spec (.of (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))))
    {Λ : Type u} [CommRing Λ] (iΛ : Spec (.of Λ) ⟶ D.S)
    (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (H : Set.range (U.left.fromSpecResidueField u₀ ≫ U.hom).base ⊆ Set.range iΛ.base)
    {l : Type u} [Field l] [Algebra Λ l]
    (hfinite_l : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (xₗ : D.𝒳.val.val.obj)
    (hxₗ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj xₗ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (τ : xₗ ⟶ x)
    (hτ : (eqToHom (congrArg Over.left hxₗ).symm ≫
        ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map τ).left ≫
          eqToHom (congrArg Over.left hx)).base (closedPoint l) = u₀) :
    ∃ (xR : Deformation.Artin.CompleteLocalObjects D.B D.S D.hS D.𝒳.val.val.p)
      (ξ : Deformation.Artin.FormalObject D.B D.S D.hS D.𝒳.val.val.p)
      (_hξ : ξ = (Deformation.Artin.approximationFunctor D.B D.S D.hS D.𝒳.val.val.p
        D.𝒳.val.property).obj xR)
      (_alg : Algebra Λ ξ.base.R)
      (hΛ : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS),
      (∃ e : AlgebraicGeometry.Scheme.completedLocalRing U.left u₀ ≃+* ξ.base.R,
        ξ.base.toS = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap (U.left.presheaf.stalk u₀)
            (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
              U.left.fromSpecStalk u₀ ≫ U.hom) ∧
      flatObject D.B D.S D.hS D.𝒳.val xR.obj.1 ∧
      (∃ r : xR.obj.1 ⟶ x, Flat (D.B.inclusion.map (D.𝒳.val.val.p.map r).left)) ∧
      Deformation.Artin.FormalObject.IsVersal D.B D.S D.hS D.𝒳.val.val.p D.𝒳.val.property
        ξ Λ iΛ hΛ ∧
      ∃ (_ : Algebra (ResidueField ξ.base.R) l) (_ : IsScalarTower Λ (ResidueField ξ.base.R) l),
        Module.Finite (ResidueField ξ.base.R) l ∧
        ∃ η' : xₗ ⟶ ξ.level 0,
          eqToHom (congrArg Over.left hxₗ).symm ≫
              ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map η').left ≫
            eqToHom (congrArg Over.left (ξ.basePoint Λ iΛ hΛ)) =
          Spec.map (CommRingCat.ofHom (algebraMap (ResidueField ξ.base.R) l)) := by
  classical
  have hp := D.𝒳.val.property
  let : D.𝒳.val.val.p.IsFibered := hp.isFibered
  have : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  set q := D.𝒳.val.val.p ⋙ Over.post D.B.inclusion
  obtain ⟨xR, r, e₀, hr, hrbase₀, hbase₀⟩ :=
    Deformation.Artin.exists_completeLocalObject_of_isFiniteTypePoint D.B D.S D.hS
      D.𝒳.val.val.p hp U x hx u₀ hu₀ hC
  set ξ := (Deformation.Artin.approximationFunctor D.B D.S D.hS D.𝒳.val.val.p hp).obj xR
    with hξdef
  obtain ⟨e, hrbase, hbase, hs⟩ := Deformation.Artin.exists_approximationBase_presentation
    D.B D.S D.hS D.𝒳.val.val.p hp U x hx u₀ xR ξ rfl r e₀ hrbase₀ hbase₀
  have hmem : Deformation.Artin.basePoint U u₀ ∈ Set.range iΛ.base :=
    H ⟨IsLocalRing.closedPoint (U.left.residueField u₀), rfl⟩
  obtain ⟨alg, hΛ⟩ := exists_algebra_of_formalBase_mem_range ξ.base iΛ hiΛ (hs ▸ hmem)
  obtain ⟨t, ht⟩ := hmem
  let := alg
  let := Deformation.Artin.chartResidueAlgebra iΛ U u₀ H
  have hcompat := Deformation.Artin.algebraMap_chartResidueAlgebra iΛ U u₀ H
  set g : Spec (.of ξ.base.R) ⟶ U.left := Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (U.left.presheaf.stalk u₀)
      (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
    U.left.fromSpecStalk u₀ with hg
  -- versality of `x` at `u₀`, from smoothness of the chart, and of `ξ`
  have hrelsm := isRelativelySmooth_objectMorphism_of_smoothObject D.B D.S D.hS D.𝒳 hxsm
  have hft : LocallyOfFiniteType (U.left.fromSpecResidueField u₀ ≫ U.hom) := by
    have := hu₀.1
    infer_instance
  have hversal : Deformation.Artin.IsVersalAt U q u₀ x hx := by
    subst hx
    exact isVersalAt_of_isRelativelySmooth_objectMorphism D.B D.S D.hS D.𝒳.val x hrelsm u₀ hft
  have hξversal := (isVersalAt_iff_isVersal_completion D U x hx u₀ xR ξ rfl e g hg hbase r hr
    hrbase Λ iΛ hiΛ hΛ t ht hcompat).mp hversal
  have hflat := flatObject_completeLocalRestriction_of_smoothObject D U x hx u₀ xR r e₀
    hrbase₀ hxsm
  refine ⟨xR, ξ, rfl, alg, hΛ, ⟨e, by rw [hbase, Category.assoc, Category.assoc]⟩, hflat,
    ⟨r, flat_schemeMap_completeLocalRestriction D U x hx u₀ xR r e₀ hrbase₀⟩, hξversal, ?_⟩
  -- the closed fibre of `ξ` maps to `x` over the residue point of `u₀`
  set lam := Deformation.Artin.approximationLevelToOriginal D.B D.S D.hS D.𝒳.val.val.p hp xR ξ
    rfl r 0 with hlam
  have hres : Deformation.Artin.schemeMap q (ξ.basePoint Λ iΛ hΛ) hx lam =
      Spec.map (CommRingCat.ofHom (residue ξ.base.R)) ≫ g :=
    schemeMap_closedFibre_eq_residuePoint D U x hx xR ξ rfl g r hrbase Λ iΛ hΛ
  set E := Deformation.Artin.completionResidueEquiv U.left u₀ e
  have hE : Spec.map (CommRingCat.ofHom E.toRingHom) ≫ U.left.fromSpecResidueField u₀ =
      Spec.map (CommRingCat.ofHom (residue ξ.base.R)) ≫ g :=
    Deformation.Artin.completionResidueEquiv_spec U.left u₀ e
  -- the point `Spec l ⟶ U` factors through the residue field of `u₀`
  set a := Deformation.Artin.schemeMap q hxₗ hx τ with ha
  obtain ⟨φ, hφ⟩ := exists_eq_specMap_comp_fromSpecResidueField a hτ
  let ψ : CommRingCat.of (ResidueField ξ.base.R) ⟶ CommRingCat.of l :=
    CommRingCat.ofHom E.symm.toRingHom ≫ φ
  let : Algebra (ResidueField ξ.base.R) l := ψ.hom.toAlgebra
  have hψ : Spec.map ψ ≫ Deformation.Artin.schemeMap q (ξ.basePoint Λ iΛ hΛ) hx lam = a := by
    rw [hres, ← hE, hφ, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext z
    show φ (E.symm (E z)) = φ z
    rw [RingEquiv.symm_apply_apply]
  have hw : Spec.map ψ ≫ (Spec.map (CommRingCat.ofHom
      (algebraMap Λ (ResidueField ξ.base.R))) ≫ iΛ) =
        Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ := by
    have h₁ := schemeMap_comp_hom q (ξ.basePoint Λ iΛ hΛ) hx lam
    have h₂ := schemeMap_comp_hom q hxₗ hx τ
    simp only [Over.mk_hom] at h₁ h₂
    rw [← h₁, ← Category.assoc, hψ]
    exact h₂
  -- the morphism of the site between the bases
  let b' : q.obj xₗ ⟶ q.obj (ξ.level 0) :=
    eqToHom hxₗ ≫ Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
      (V := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ (ResidueField ξ.base.R))) ≫ iΛ))
      (Spec.map ψ) hw ≫ eqToHom (ξ.basePoint Λ iΛ hΛ).symm
  let b : D.𝒳.val.val.p.obj xₗ ⟶ D.𝒳.val.val.p.obj (ξ.level 0) :=
    (Over.post D.B.inclusion).preimage b'
  have hb' : (Over.post D.B.inclusion).map b = b' := (Over.post D.B.inclusion).map_preimage _
  have hb'left : b'.left = eqToHom (congrArg Over.left hxₗ) ≫ Spec.map ψ ≫
      eqToHom (congrArg Over.left (ξ.basePoint Λ iΛ hΛ)).symm := by
    simp [b', Over.comp_left, Over.eqToHom_left]
  have hb : b ≫ D.𝒳.val.val.p.map lam = D.𝒳.val.val.p.map τ := by
    apply (Over.post D.B.inclusion).map_injective
    apply Over.OverMorphism.ext
    rw [Functor.map_comp, Over.comp_left, hb']
    show b'.left ≫ (q.map lam).left = (q.map τ).left
    apply (cancel_epi (eqToHom (congrArg Over.left hxₗ).symm)).1
    apply (cancel_mono (eqToHom (congrArg Over.left hx))).1
    calc eqToHom (congrArg Over.left hxₗ).symm ≫ (b'.left ≫ (q.map lam).left) ≫
          eqToHom (congrArg Over.left hx)
        = (eqToHom (congrArg Over.left hxₗ).symm ≫ b'.left ≫
            eqToHom (congrArg Over.left (ξ.basePoint Λ iΛ hΛ))) ≫
          Deformation.Artin.schemeMap q (ξ.basePoint Λ iΛ hΛ) hx lam := by
          simp [Deformation.Artin.schemeMap, Category.assoc]
      _ = Spec.map ψ ≫ Deformation.Artin.schemeMap q (ξ.basePoint Λ iΛ hΛ) hx lam := by
          rw [hb'left]; simp
      _ = eqToHom (congrArg Over.left hxₗ).symm ≫ (q.map τ).left ≫
          eqToHom (congrArg Over.left hx) := hψ
  let η' := hp.fill (f := D.𝒳.val.val.p.map lam) (g := b) (f' := D.𝒳.val.val.p.map τ) hb.symm
    lam τ
  have hη'lift : D.𝒳.val.val.p.IsHomLift b η' := hp.fill_isHomLift _ _ _
  have hη' : D.𝒳.val.val.p.map η' = b := (IsHomLift.eq_of_isHomLift (p := D.𝒳.val.val.p) b η').symm
  -- the compatibilities of the field extension
  have hring : ψ.hom.comp (algebraMap Λ (ResidueField ξ.base.R)) = algebraMap Λ l := by
    have h : Spec.map (CommRingCat.ofHom (ψ.hom.comp (algebraMap Λ (ResidueField ξ.base.R)))) ≫
        iΛ = Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      exact hw
    have := Spec.map_injective ((cancel_mono iΛ).1 h)
    exact congrArg CommRingCat.Hom.hom this
  have htower : IsScalarTower Λ (ResidueField ξ.base.R) l :=
    IsScalarTower.of_algebraMap_eq fun z => (congrArg (fun f => f z) hring).symm
  have hfin : Module.Finite (ResidueField ξ.base.R) l := by
    have : LocallyOfFiniteType a := locallyOfFiniteType_schemeMap q hxₗ hx τ hfinite_l
    have : LocallyOfFiniteType (Spec.map ψ ≫
        Deformation.Artin.schemeMap q (ξ.basePoint Λ iΛ hΛ) hx lam) := by
      rw [hψ]; infer_instance
    have : LocallyOfFiniteType (Spec.map ψ) := locallyOfFiniteType_of_comp (Spec.map ψ)
      (Deformation.Artin.schemeMap q (ξ.basePoint Λ iΛ hΛ) hx lam)
    have hft : ψ.hom.FiniteType := HasRingHomProperty.Spec_iff.mp this
    have : Algebra.FiniteType (ResidueField ξ.base.R) l := hft
    exact finite_of_finite_type_of_isJacobsonRing (ResidueField ξ.base.R) l
  refine ⟨inferInstance, htower, hfin, η', ?_⟩
  show eqToHom (congrArg Over.left hxₗ).symm ≫ ((Over.post D.B.inclusion).map
      (D.𝒳.val.val.p.map η')).left ≫ eqToHom (congrArg Over.left (ξ.basePoint Λ iΛ hΛ)) = _
  rw [hη', hb', hb'left]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    eqToHom_trans, Category.comp_id]
  rfl

/-- **The chart side of Step III of the proof of Stacks 0DR2.** In the versal situation, let `x`
be a smooth object of `𝒳` over a scheme `U` locally of finite type and quasi-compact over `S`, let
`u₀ ∈ U` be a finite type point whose completed local ring lies in the site and whose image lies
in an affine open `Spec Λ ⊆ S`, and let `τ : xₗ ⟶ x` be a morphism from an object over
`Spec l ⟶ Spec Λ ⟶ S` lying over a morphism `Spec l ⟶ U` through `u₀`. Then the complete local
restriction `xR` of `x` over `𝒪^∧_{U, u₀}` is a flat object whose formal object `ξ` is versal,
and `τ` factors through a morphism `η' : xₗ ⟶ ξ_0` to the closed fibre of `ξ`, lying over the
spectrum of a finite field extension `κ(ξ) ⟶ l` compatible with the `Λ`-algebra structures.
Moreover `xR` maps to `x` by a morphism lying over a flat morphism of schemes, the canonical
`Spec(𝒪^∧_{U, u₀}) ⟶ U`. -/
theorem exists_closedFibre_hom_and_restriction_of_smoothObject (D : VersalSituation.{u, w})
    (U : Over D.S) [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (x : D.𝒳.val.val.obj) (hx : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x = U)
    (hxsm : smoothObject.{u, w} D.B D.S D.hS D.𝒳 x)
    (u₀ : U.left) (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    (hC : D.B.Contains (Spec (.of (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))))
    {Λ : Type u} [CommRing Λ] (iΛ : Spec (.of Λ) ⟶ D.S)
    (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (H : Set.range (U.left.fromSpecResidueField u₀ ≫ U.hom).base ⊆ Set.range iΛ.base)
    {l : Type u} [Field l] [Algebra Λ l]
    (hfinite_l : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (xₗ : D.𝒳.val.val.obj)
    (hxₗ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj xₗ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (τ : xₗ ⟶ x)
    (hτ : (eqToHom (congrArg Over.left hxₗ).symm ≫
        ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map τ).left ≫
          eqToHom (congrArg Over.left hx)).base (closedPoint l) = u₀) :
    ∃ (xR : Deformation.Artin.CompleteLocalObjects D.B D.S D.hS D.𝒳.val.val.p)
      (ξ : Deformation.Artin.FormalObject D.B D.S D.hS D.𝒳.val.val.p)
      (_hξ : ξ = (Deformation.Artin.approximationFunctor D.B D.S D.hS D.𝒳.val.val.p
        D.𝒳.val.property).obj xR)
      (_alg : Algebra Λ ξ.base.R)
      (hΛ : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS),
      flatObject D.B D.S D.hS D.𝒳.val xR.obj.1 ∧
      (∃ r : xR.obj.1 ⟶ x, Flat (D.B.inclusion.map (D.𝒳.val.val.p.map r).left)) ∧
      Deformation.Artin.FormalObject.IsVersal D.B D.S D.hS D.𝒳.val.val.p D.𝒳.val.property
        ξ Λ iΛ hΛ ∧
      ∃ (_ : Algebra (ResidueField ξ.base.R) l) (_ : IsScalarTower Λ (ResidueField ξ.base.R) l),
        Module.Finite (ResidueField ξ.base.R) l ∧
        ∃ η' : xₗ ⟶ ξ.level 0,
          eqToHom (congrArg Over.left hxₗ).symm ≫
              ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map η').left ≫
            eqToHom (congrArg Over.left (ξ.basePoint Λ iΛ hΛ)) =
          Spec.map (CommRingCat.ofHom (algebraMap (ResidueField ξ.base.R) l)) := by
  obtain ⟨xR, ξ, hξ, alg, hΛ, -, h⟩ :=
    exists_closedFibre_hom_of_smoothObject_completedLocalRing D U x hx hxsm u₀ hu₀ hC iΛ hiΛ H
      hfinite_l xₗ hxₗ τ hτ
  exact ⟨xR, ξ, hξ, alg, hΛ, h⟩

/-- **The chart side of Step III of the proof of Stacks 0DR2.** In the versal situation, let `x`
be a smooth object of `𝒳` over a scheme `U` locally of finite type and quasi-compact over `S`, let
`u₀ ∈ U` be a finite type point whose completed local ring lies in the site and whose image lies
in an affine open `Spec Λ ⊆ S`, and let `τ : xₗ ⟶ x` be a morphism from an object over
`Spec l ⟶ Spec Λ ⟶ S` lying over a morphism `Spec l ⟶ U` through `u₀`. Then the complete local
restriction `xR` of `x` over `𝒪^∧_{U, u₀}` is a flat object whose formal object `ξ` is versal,
and `τ` factors through a morphism `η' : xₗ ⟶ ξ_0` to the closed fibre of `ξ`, lying over the
spectrum of a finite field extension `κ(ξ) ⟶ l` compatible with the `Λ`-algebra structures. -/
theorem exists_closedFibre_hom_of_smoothObject (D : VersalSituation.{u, w})
    (U : Over D.S) [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (x : D.𝒳.val.val.obj) (hx : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x = U)
    (hxsm : smoothObject.{u, w} D.B D.S D.hS D.𝒳 x)
    (u₀ : U.left) (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    (hC : D.B.Contains (Spec (.of (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))))
    {Λ : Type u} [CommRing Λ] (iΛ : Spec (.of Λ) ⟶ D.S)
    (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (H : Set.range (U.left.fromSpecResidueField u₀ ≫ U.hom).base ⊆ Set.range iΛ.base)
    {l : Type u} [Field l] [Algebra Λ l]
    (hfinite_l : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (xₗ : D.𝒳.val.val.obj)
    (hxₗ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj xₗ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (τ : xₗ ⟶ x)
    (hτ : (eqToHom (congrArg Over.left hxₗ).symm ≫
        ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map τ).left ≫
          eqToHom (congrArg Over.left hx)).base (closedPoint l) = u₀) :
    ∃ (xR : Deformation.Artin.CompleteLocalObjects D.B D.S D.hS D.𝒳.val.val.p)
      (ξ : Deformation.Artin.FormalObject D.B D.S D.hS D.𝒳.val.val.p)
      (_hξ : ξ = (Deformation.Artin.approximationFunctor D.B D.S D.hS D.𝒳.val.val.p
        D.𝒳.val.property).obj xR)
      (_alg : Algebra Λ ξ.base.R)
      (hΛ : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS),
      flatObject D.B D.S D.hS D.𝒳.val xR.obj.1 ∧
      Deformation.Artin.FormalObject.IsVersal D.B D.S D.hS D.𝒳.val.val.p D.𝒳.val.property
        ξ Λ iΛ hΛ ∧
      ∃ (_ : Algebra (ResidueField ξ.base.R) l) (_ : IsScalarTower Λ (ResidueField ξ.base.R) l),
        Module.Finite (ResidueField ξ.base.R) l ∧
        ∃ η' : xₗ ⟶ ξ.level 0,
          eqToHom (congrArg Over.left hxₗ).symm ≫
              ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map η').left ≫
            eqToHom (congrArg Over.left (ξ.basePoint Λ iΛ hΛ)) =
          Spec.map (CommRingCat.ofHom (algebraMap (ResidueField ξ.base.R) l)) := by
  obtain ⟨xR, ξ, hξ, alg, hΛ, hflat, -, hv, rest⟩ :=
    exists_closedFibre_hom_and_restriction_of_smoothObject D U x hx hxsm u₀ hu₀ hC iΛ hiΛ H
      hfinite_l xₗ hxₗ τ hτ
  exact ⟨xR, ξ, hξ, alg, hΛ, hflat, hv, rest⟩

/-- A property of morphisms of schemes respecting isomorphisms holds for the morphism of
schemes underlying a morphism of `𝒳` as soon as it holds for the morphism of the site it lies
over. -/
theorem prop_map_left_of_isHomLift {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : Type*} [Category F] (p : F ⥤ BigFppfOver B S hS)
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {U V : BigFppfOver B S hS} (j : U ⟶ V) {a b : F} (ρ : a ⟶ b) [p.IsHomLift j ρ]
    (hj : P (B.inclusion.map j.left)) : P (B.inclusion.map (p.map ρ).left) := by
  have hfac := IsHomLift.fac' p j ρ
  generalize IsHomLift.domain_eq p j ρ = h₁ at hfac
  generalize IsHomLift.codomain_eq p j ρ = h₂ at hfac
  subst h₁ h₂
  rw [hfac]
  simpa using hj

/-- On a scheme which is the spectrum of a field, every point is the closed point. -/
theorem apply_eq_of_eq_spec_field {T : Scheme.{u}} {l : Type u} [Field l]
    (h : T = Spec (.of l)) {Y : Scheme.{u}} (m : T ⟶ Y) (t : T) :
    m t = (eqToHom h.symm ≫ m) (closedPoint l) := by
  subst h
  simp only [eqToHom_refl, Category.id_comp]
  exact congrArg m (Subsingleton.elim t (closedPoint l))

attribute [local implicit_reducible]
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.mk
  CategoryTheory.Functor.Fiber.fiberInclusion in
/-- **The point of Step III of the proof of Stacks 0DR2, with the chart.** This is
`AlgebraicGeometry.Stack.exists_chartPoint_closedFibre` together with the smooth chart `x'`
receiving `τ : xₗ ⟶ x'`, the point `u₀'` of its scheme under the image of `xₗ`, and the
identification of the base of `ξ` with `𝒪^∧_{U, u₀'}` over `S`, which Step III of the proof of
Stacks 0DZS uses. The rest of the statement is the following. In the versal situation, let `x₀`
be a point of `𝒳` over `Spec k ⟶ Spec Λ ⟶ S` with `k` of finite type over `S`. Then there are a
finite extension `l/k`, a point `xₗ` over `Spec l ⟶ Spec Λ ⟶ S` with a morphism `η : xₗ ⟶ x₀` over
`Spec l ⟶ Spec k`, and a flat complete local object `xR` (the restriction of a smooth chart over
the spectrum of a completed local ring) whose formal object `ξ` is versal, together with a
morphism `η' : xₗ ⟶ ξ_0` to the closed fibre of `ξ` lying over a finite extension `κ(ξ) ⟶ l`.
Moreover `xR` maps, over a flat morphism of schemes, to a smooth object of `𝒳`. -/
theorem exists_chartPoint_closedFibre_completedLocalRing (D : VersalSituation.{u, w})
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    ∃ (l : Type u) (_ : Field l) (_ : Algebra k l) (_ : Algebra Λ l) (_ : IsScalarTower Λ k l),
      Module.Finite k l ∧
      ∃ (xₗ : D.𝒳.val.val.obj)
        (hxₗ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj xₗ =
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
        (η : xₗ ⟶ x₀),
        eqToHom (congrArg Over.left hxₗ).symm ≫
            ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map η).left ≫
          eqToHom (congrArg Over.left hx₀) = Spec.map (CommRingCat.ofHom (algebraMap k l)) ∧
      ∃ (xR : Deformation.Artin.CompleteLocalObjects D.B D.S D.hS D.𝒳.val.val.p)
        (ξ : Deformation.Artin.FormalObject D.B D.S D.hS D.𝒳.val.val.p)
        (_hξ : ξ = (Deformation.Artin.approximationFunctor D.B D.S D.hS D.𝒳.val.val.p
          D.𝒳.val.property).obj xR)
        (_alg : Algebra Λ ξ.base.R)
        (hΛ : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS),
        (∃ (x' : D.𝒳.val.val.obj) (τ : xₗ ⟶ x'), smoothObject.{u, w} D.B D.S D.hS D.𝒳 x' ∧
          LocallyOfFiniteType ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x').hom ∧
          ∃ u₀' : ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x').left,
            (∀ t : (BigFppfOver.toScheme D.B D.S D.hS).obj (D.𝒳.val.val.p.obj xₗ),
              (BigFppfOver.toScheme D.B D.S D.hS).map (D.𝒳.val.val.p.map τ) t = u₀') ∧
            ∃ e : AlgebraicGeometry.Scheme.completedLocalRing
                ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x').left u₀' ≃+* ξ.base.R,
              ξ.base.toS = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
                Spec.map (CommRingCat.ofHom (algebraMap
                  (((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x').left.presheaf.stalk u₀')
                    (AlgebraicGeometry.Scheme.completedLocalRing
                      ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x').left u₀'))) ≫
                  ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x').left.fromSpecStalk u₀' ≫
                    ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x').hom) ∧
        flatObject D.B D.S D.hS D.𝒳.val xR.obj.1 ∧
        (∃ (x : D.𝒳.val.val.obj) (_ : smoothObject.{u, w} D.B D.S D.hS D.𝒳 x)
          (r : xR.obj.1 ⟶ x), Flat (D.B.inclusion.map (D.𝒳.val.val.p.map r).left)) ∧
        Deformation.Artin.FormalObject.IsVersal D.B D.S D.hS D.𝒳.val.val.p D.𝒳.val.property
          ξ Λ iΛ hΛ ∧
        ∃ (_ : Algebra (ResidueField ξ.base.R) l)
          (_ : IsScalarTower Λ (ResidueField ξ.base.R) l),
          Module.Finite (ResidueField ξ.base.R) l ∧
          ∃ η' : xₗ ⟶ ξ.level 0,
            eqToHom (congrArg Over.left hxₗ).symm ≫
                ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map η').left ≫
              eqToHom (congrArg Over.left (ξ.basePoint Λ iΛ hΛ)) =
            Spec.map (CommRingCat.ofHom (algebraMap (ResidueField ξ.base.R) l)) := by
  classical
  let : _root_.AlgebraicGeometry.IsOpenImmersion iΛ := hiΛ
  obtain ⟨l, _, _, _, _, hkl, -, V, g, hgsm, hVlft, u₀, hu₀, hxₗ, η, hη, ⟨c⟩, -, hres⟩ :=
    exists_smoothChart_point_residueField_eq D iΛ hiΛ x₀ hx₀ hfinite
  refine ⟨l, inferInstance, inferInstance, inferInstance, inferInstance, hkl, _, hxₗ, η, hη, ?_⟩
  have hp := D.𝒳.val.property
  let : D.𝒳.val.val.p.IsFibered := hp.isFibered
  set q := D.𝒳.val.val.p ⋙ Over.post D.B.inclusion
  have hfinite_l : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ) :=
    (locallyOfFiniteType_and_quasiCompact_fieldExtension iΛ hfinite).1
  have : IsLocallyNoetherian (D.B.inclusion.obj (D.B.obj D.hS)) := D.locallyNoetherian
  have : IsLocallyNoetherian (D.B.inclusion.obj V.left) :=
    LocallyOfFiniteType.isLocallyNoetherian (D.B.inclusion.map V.hom)
  -- the point `ν` of `V` and an affine open neighbourhood of it
  set ν := (Deformation.Artin.SliceTangent.pointMap hu₀).base
    (Deformation.Artin.SliceTangent.closedPt (.of l)) with hν
  obtain ⟨_, ⟨Vaff, hV', rfl⟩, hνV', -⟩ :=
    (D.B.inclusion.obj V.left).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ ν) isOpen_univ
  let V' : (D.B.inclusion.obj V.left).Opens := Vaff
  let U₁ := BigFppfOver.openSubObj D.B D.S D.hS V V'
  let j := BigFppfOver.openSubHom D.B D.S D.hS V V'
  -- the point `u₀` factors through the open
  have hpm : D.B.inclusion.map u₀.hom.left =
      eqToHom (congrArg Over.left hu₀) ≫ Deformation.Artin.SliceTangent.pointMap hu₀ := by
    simp [Deformation.Artin.SliceTangent.pointMap]
  have hrange : Set.range (D.B.inclusion.map u₀.hom.left).base ⊆ Set.range V'.ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hz : (eqToHom (congrArg Over.left hu₀)).base z =
        Deformation.Artin.SliceTangent.closedPt (.of l) :=
      Subsingleton.elim (α := Spec (CommRingCat.of l)) _ _
    rw [hpm, Scheme.Hom.comp_apply, hz]
    exact hνV'
  let t₀ : u₀.left ⟶ U₁ := Over.homMk (ObjectProperty.homMk
    (X := u₀.left.left) (Y := U₁.left)
    (IsOpenImmersion.lift V'.ι (D.B.inclusion.map u₀.hom.left) hrange)) (by
      apply ObjectProperty.hom_ext
      show IsOpenImmersion.lift V'.ι (D.B.inclusion.map u₀.hom.left) hrange ≫
        (V'.ι ≫ D.B.inclusion.map V.hom) = D.B.inclusion.map u₀.left.hom
      rw [← Category.assoc, IsOpenImmersion.lift_fac, ← Functor.map_comp, Over.w])
  have ht₀ : t₀ ≫ j = u₀.hom := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact IsOpenImmersion.lift_fac _ _ _
  let x' := (CatFiberedInGroupoids.homFunctor g.hom).obj (Over.mk j)
  let τ : (CatFiberedInGroupoids.homFunctor g.hom).obj u₀ ⟶ x' :=
    (CatFiberedInGroupoids.homFunctor g.hom).map (Over.homMk t₀ ht₀)
  have hx'sm : smoothObject.{u, w} D.B D.S D.hS D.𝒳 x' := by
    have hj : smoothObject.{u, w} D.B D.S D.hS (schemeStack.{u, w} D.B D.S D.hS V) (Over.mk j) := by
      rw [smoothObject_schemeStack_iff]
      show Smooth V'.ι
      infer_instance
    exact LisseEtale.smoothObject_map.{u, w} D.B D.S D.hS g hgsm ⟨Over.mk j, hj⟩
  set U := q.obj x' with hUdef
  have hU₁ : D.𝒳.val.val.p.obj x' = U₁ := Functor.congr_obj g.hom.hom.w (Over.mk j)
  have hUeq : U = (Over.post D.B.inclusion).obj U₁ := congrArg (Over.post D.B.inclusion).obj hU₁
  -- the chart `U` is affine, of finite type and Noetherian
  have hlft : LocallyOfFiniteType ((Over.post D.B.inclusion).obj U₁).hom := by
    show LocallyOfFiniteType (V'.ι ≫ D.B.inclusion.map V.hom)
    infer_instance
  have : IsNoetherianRing Γ(D.B.inclusion.obj V.left, V') :=
    IsLocallyNoetherian.component_noetherian ⟨V', hV'⟩
  have hnoeth : TopologicalSpace.NoetherianSpace ((Over.post D.B.inclusion).obj U₁).left := by
    show TopologicalSpace.NoetherianSpace V'
    exact noetherianSpace_of_isAffineOpen V' hV'
  have : LocallyOfFiniteType U.hom := by rwa [hUeq]
  have : TopologicalSpace.NoetherianSpace U.left := by rwa [hUeq]
  have : QuasiCompact U.hom := inferInstance
  have : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  have : IsNoetherian U.left := ⟨⟩
  -- the point `u₀'` of `U` through which `τ` factors
  set a := Deformation.Artin.schemeMap q hxₗ (rfl : q.obj x' = U) τ with ha
  have ha_lft : LocallyOfFiniteType a :=
    locallyOfFiniteType_schemeMap q hxₗ (rfl : q.obj x' = U) τ hfinite_l
  set u₀' := a.base (closedPoint l) with hu₀'
  have hft : AlgebraicGeometry.IsFiniteTypePoint u₀' := by
    have hcl : AlgebraicGeometry.IsFiniteTypePoint
        (Deformation.Artin.SliceTangent.closedPt (.of l)) :=
      isFiniteTypePoint_of_isClosed_singleton
        (IsLocalRing.isClosed_singleton_closedPoint (CommRingCat.of l))
    exact mapsTo_finiteTypePoints a hcl
  have hC : D.B.Contains (Spec (.of (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀'))) := by
    have : IsNoetherian (D.𝒳.val.val.p.obj x').left.obj := ‹IsNoetherian U.left›
    exact D.B.contains_spec_completedLocalRing (D.𝒳.val.val.p.obj x').left.2 u₀'
  have H : Set.range (U.left.fromSpecResidueField u₀' ≫ U.hom).base ⊆ Set.range iΛ.base := by
    rintro _ ⟨z, rfl⟩
    have h₂ := schemeMap_comp_hom q hxₗ (rfl : q.obj x' = U) τ
    simp only [Over.mk_hom] at h₂
    refine ⟨(Spec.map (CommRingCat.ofHom (algebraMap Λ l))).base (closedPoint l), ?_⟩
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply, hu₀']
    show (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ).base (closedPoint l) =
      (Deformation.Artin.schemeMap q hxₗ rfl τ ≫ U.hom).base (closedPoint l)
    rw [h₂]
  obtain ⟨xR, ξ, hξ, alg, hΛ, he, hflat, ⟨r, hr⟩, rest⟩ :=
    exists_closedFibre_hom_of_smoothObject_completedLocalRing D U x' rfl hx'sm u₀' hft hC iΛ hiΛ H
      hfinite_l _ hxₗ τ rfl
  refine ⟨xR, ξ, hξ, alg, hΛ, ⟨x', τ, hx'sm, ‹LocallyOfFiniteType U.hom›, u₀', fun t => ?_, he⟩,
    hflat, ⟨x', hx'sm, r, hr⟩, rest⟩
  have ha' : a = eqToHom (congrArg Over.left hxₗ).symm ≫ (q.map τ).left := by
    rw [ha]
    show eqToHom _ ≫ (q.map τ).left ≫ eqToHom _ = _
    rw [eqToHom_refl, Category.comp_id]
  rw [hu₀', ha']
  exact apply_eq_of_eq_spec_field (congrArg Over.left hxₗ) (q.map τ).left t


attribute [local implicit_reducible]
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.mk
  CategoryTheory.Functor.Fiber.fiberInclusion in
/-- **The point of Step III of the proof of Stacks 0DR2.** In the versal situation, let `x₀` be a
point of `𝒳` over `Spec k ⟶ Spec Λ ⟶ S` with `k` of finite type over `S`. Then there are a finite
extension `l/k`, a point `xₗ` over `Spec l ⟶ Spec Λ ⟶ S` with a morphism `η : xₗ ⟶ x₀` over
`Spec l ⟶ Spec k`, and a flat complete local object `xR` (the restriction of a smooth chart over
the spectrum of a completed local ring) whose formal object `ξ` is versal, together with a
morphism `η' : xₗ ⟶ ξ_0` to the closed fibre of `ξ` lying over a finite extension `κ(ξ) ⟶ l`.
Moreover `xR` maps, over a flat morphism of schemes, to a smooth object of `𝒳`. -/
theorem exists_chartPoint_closedFibre_and_restriction (D : VersalSituation.{u, w})
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    ∃ (l : Type u) (_ : Field l) (_ : Algebra k l) (_ : Algebra Λ l) (_ : IsScalarTower Λ k l),
      Module.Finite k l ∧
      ∃ (xₗ : D.𝒳.val.val.obj)
        (hxₗ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj xₗ =
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
        (η : xₗ ⟶ x₀),
        eqToHom (congrArg Over.left hxₗ).symm ≫
            ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map η).left ≫
          eqToHom (congrArg Over.left hx₀) = Spec.map (CommRingCat.ofHom (algebraMap k l)) ∧
      ∃ (xR : Deformation.Artin.CompleteLocalObjects D.B D.S D.hS D.𝒳.val.val.p)
        (ξ : Deformation.Artin.FormalObject D.B D.S D.hS D.𝒳.val.val.p)
        (_hξ : ξ = (Deformation.Artin.approximationFunctor D.B D.S D.hS D.𝒳.val.val.p
          D.𝒳.val.property).obj xR)
        (_alg : Algebra Λ ξ.base.R)
        (hΛ : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS),
        flatObject D.B D.S D.hS D.𝒳.val xR.obj.1 ∧
        (∃ (x : D.𝒳.val.val.obj) (_ : smoothObject.{u, w} D.B D.S D.hS D.𝒳 x)
          (r : xR.obj.1 ⟶ x), Flat (D.B.inclusion.map (D.𝒳.val.val.p.map r).left)) ∧
        Deformation.Artin.FormalObject.IsVersal D.B D.S D.hS D.𝒳.val.val.p D.𝒳.val.property
          ξ Λ iΛ hΛ ∧
        ∃ (_ : Algebra (ResidueField ξ.base.R) l)
          (_ : IsScalarTower Λ (ResidueField ξ.base.R) l),
          Module.Finite (ResidueField ξ.base.R) l ∧
          ∃ η' : xₗ ⟶ ξ.level 0,
            eqToHom (congrArg Over.left hxₗ).symm ≫
                ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map η').left ≫
              eqToHom (congrArg Over.left (ξ.basePoint Λ iΛ hΛ)) =
            Spec.map (CommRingCat.ofHom (algebraMap (ResidueField ξ.base.R) l)) := by
  obtain ⟨l, i₁, i₂, i₃, i₄, hkl, xₗ, hxₗ, η, hη, xR, ξ, hξ, alg, hΛ, -, rest⟩ :=
    exists_chartPoint_closedFibre_completedLocalRing D iΛ hiΛ x₀ hx₀ hfinite
  exact ⟨l, i₁, i₂, i₃, i₄, hkl, xₗ, hxₗ, η, hη, xR, ξ, hξ, alg, hΛ, rest⟩


attribute [local implicit_reducible]
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.mk
  CategoryTheory.Functor.Fiber.fiberInclusion in
/-- **The point of Step III of the proof of Stacks 0DR2.** In the versal situation, let `x₀` be a
point of `𝒳` over `Spec k ⟶ Spec Λ ⟶ S` with `k` of finite type over `S`. Then there are a finite
extension `l/k`, a point `xₗ` over `Spec l ⟶ Spec Λ ⟶ S` with a morphism `η : xₗ ⟶ x₀` over
`Spec l ⟶ Spec k`, and a flat complete local object `xR` (the restriction of a smooth chart over
the spectrum of a completed local ring) whose formal object `ξ` is versal, together with a
morphism `η' : xₗ ⟶ ξ_0` to the closed fibre of `ξ` lying over a finite extension `κ(ξ) ⟶ l`. -/
theorem exists_chartPoint_closedFibre (D : VersalSituation.{u, w})
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    ∃ (l : Type u) (_ : Field l) (_ : Algebra k l) (_ : Algebra Λ l) (_ : IsScalarTower Λ k l),
      Module.Finite k l ∧
      ∃ (xₗ : D.𝒳.val.val.obj)
        (hxₗ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj xₗ =
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
        (η : xₗ ⟶ x₀),
        eqToHom (congrArg Over.left hxₗ).symm ≫
            ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map η).left ≫
          eqToHom (congrArg Over.left hx₀) = Spec.map (CommRingCat.ofHom (algebraMap k l)) ∧
      ∃ (xR : Deformation.Artin.CompleteLocalObjects D.B D.S D.hS D.𝒳.val.val.p)
        (ξ : Deformation.Artin.FormalObject D.B D.S D.hS D.𝒳.val.val.p)
        (_hξ : ξ = (Deformation.Artin.approximationFunctor D.B D.S D.hS D.𝒳.val.val.p
          D.𝒳.val.property).obj xR)
        (_alg : Algebra Λ ξ.base.R)
        (hΛ : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS),
        flatObject D.B D.S D.hS D.𝒳.val xR.obj.1 ∧
        Deformation.Artin.FormalObject.IsVersal D.B D.S D.hS D.𝒳.val.val.p D.𝒳.val.property
          ξ Λ iΛ hΛ ∧
        ∃ (_ : Algebra (ResidueField ξ.base.R) l)
          (_ : IsScalarTower Λ (ResidueField ξ.base.R) l),
          Module.Finite (ResidueField ξ.base.R) l ∧
          ∃ η' : xₗ ⟶ ξ.level 0,
            eqToHom (congrArg Over.left hxₗ).symm ≫
                ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map η').left ≫
              eqToHom (congrArg Over.left (ξ.basePoint Λ iΛ hΛ)) =
            Spec.map (CommRingCat.ofHom (algebraMap (ResidueField ξ.base.R) l)) := by
  obtain ⟨l, i₁, i₂, i₃, i₄, hkl, xₗ, hxₗ, η, hη, xR, ξ, hξ, alg, hΛ, hflat, -, hv, rest⟩ :=
    exists_chartPoint_closedFibre_and_restriction D iΛ hiΛ x₀ hx₀ hfinite
  exact ⟨l, i₁, i₂, i₃, i₄, hkl, xₗ, hxₗ, η, hη, xR, ξ, hξ, alg, hΛ, hflat, hv, rest⟩

end AlgebraicGeometry.Stack

end
