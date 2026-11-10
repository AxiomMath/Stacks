module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSectionsAlongFibre
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhoodFlatness
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.Points
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.TangentProduct
public import StacksFrontier.RingTheory.Module.Kaplansky

/-!
# Free global sections from flatness at a point

Stacks Tag 05KY says: for `f : X ⟶ S` locally of finite presentation, `F` a quasi-coherent
`𝒪_X`-module of finite type and `x ∈ X` a point at which `F` is flat over `S`, there are an
elementary étale neighbourhood `(S', s') ⟶ (S, s)` of the image `s` of `x` and a commutative
diagram of pointed schemes
```
  (X, x) ← (X', x')
    ↓          ↓
  (S, s) ← Spec 𝒪_{S', s'}
```
in which `X' ⟶ X ×_S Spec 𝒪_{S', s'}` is étale, `κ(x) = κ(x')`, `X'` is affine and of finite
presentation over `𝒪_{S', s'}`, the pullback of `F` is of finite presentation, and its global
sections are a *free* `𝒪_{S', s'}`-module.

The source deduces this from two results. Tag 05I5 shrinks the situation so that `F` becomes
finitely presented and flat over the base on an open of `X ×_S Spec 𝒪_{S₀, s₀}` around the unique
point over `x`, for some elementary étale neighbourhood `(S₀, s₀)`. Tag 05ID then supplies a
square of affine elementary étale neighbourhoods over that open with projective global sections;
over a local ring projective means free (Tag 0593). The base Tag 05ID produces is an elementary
étale neighbourhood of `Spec 𝒪_{S₀, s₀}` rather than of `S`, so it has to be descended: it is of
finite presentation over a limit of spectra of rings of sections on the open neighbourhoods of
`s₀`, hence has a model at a finite stage which is étale after shrinking, and shrinking further to
an affine open of `S₀` turns that stage into an elementary étale neighbourhood `(S', s')` of
`(S, s)`.

Tag 05ID enters as
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt`.

`AlgebraicGeometry.exists_etale_neighborhood_with_free_globalSections` in
`StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.FreeGlobalSections05KY` states the
same conclusion from a different assumption: projectivity of the sections already transported to the
local ring of the new base, which leaves flatness at `x` unused.

## Main results

* `AlgebraicGeometry.exists_etale_neighborhood_with_free_globalSections_of_isFiniteType` is
  Tag 05KY, from Tag 05ID and Tag 05I5.

## Implementation notes

`Spec 𝒪_{Y, y}` is presented as the limit of the spectra of the rings of sections `Γ(Y, V)` over
the open neighbourhoods `V` of `y`; those spectra are affine even when the neighbourhoods are not,
which is what makes Tag 01ZM applicable. At an affine neighbourhood the stage of that diagram is
the neighbourhood itself, and the limiting projection is the canonical morphism from the spectrum
of the stalk; this is what identifies the descended neighbourhood as an étale neighbourhood of `S`
and gives the residue field clause, since the projection is a preimmersion.

The freeness of the sections is obtained from the pushout square of global-section rings attached
to the pullback square of affine schemes: the sections of the pulled-back module are the base
change of the projective sections Tag 05ID provides, so they are free over the local ring by
Tag 0593. The scalar action on the sections is restriction of scalars along the morphism to the
spectrum of the local ring, composed with the canonical identification of that ring with the
global sections of its spectrum.

## References

* [Stacks Project, Tag 05KY](https://stacks.math.columbia.edu/tag/05KY)
* [Stacks Project, Tag 05ID](https://stacks.math.columbia.edu/tag/05ID)
* [Stacks Project, Tag 05I5](https://stacks.math.columbia.edu/tag/05I5)
* [Stacks Project, Tag 0593](https://stacks.math.columbia.edu/tag/0593)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-! ### The spectrum of a stalk as a limit of spectra of rings of sections -/

/-- The affine diagram over the open neighbourhoods of a point: a neighbourhood is sent to the
spectrum of its ring of sections. -/
private def openNeighborhoodRingDiagram (Y : Scheme.{u}) (y : Y) :
    TopologicalSpace.OpenNhds y ⥤ Scheme.{u} :=
  (((TopologicalSpace.OpenNhds.inclusion y).op ⋙ Y.presheaf).rightOp) ⋙ Scheme.Spec

private instance (Y : Scheme.{u}) (y : Y) (i : TopologicalSpace.OpenNhds y) :
    IsAffine ((openNeighborhoodRingDiagram Y y).obj i) := by
  dsimp [openNeighborhoodRingDiagram]
  infer_instance

private instance (Y : Scheme.{u}) (y : Y) (i : TopologicalSpace.OpenNhds y) :
    CompactSpace ((openNeighborhoodRingDiagram Y y).obj i) := inferInstance

private instance (Y : Scheme.{u}) (y : Y) (i : TopologicalSpace.OpenNhds y) :
    QuasiSeparatedSpace ((openNeighborhoodRingDiagram Y y).obj i) := inferInstance

private instance (Y : Scheme.{u}) (y : Y) {i j : TopologicalSpace.OpenNhds y}
    (g : i ⟶ j) :
    IsAffineHom ((openNeighborhoodRingDiagram Y y).map g) := inferInstance

/-- The cone exhibiting `Spec 𝒪_{Y, y}` over the diagram of spectra of rings of sections on open
neighbourhoods of `y`. -/
private def stalkSpecCone (Y : Scheme.{u}) (y : Y) :
    Cone (openNeighborhoodRingDiagram Y y) :=
  Scheme.Spec.mapCone
    (coneOfCoconeLeftOp
      (colimit.cocone (((TopologicalSpace.OpenNhds.inclusion y).op ⋙ Y.presheaf).rightOp.leftOp)))

/-- The spectrum of a stalk is the inverse limit of the spectra of the rings of sections over the
open neighbourhoods of the point. The neighbourhoods need not be affine: their section-ring
spectra are affine at every stage. -/
private def isLimit_stalkSpecCone (Y : Scheme.{u}) (y : Y) :
    IsLimit (stalkSpecCone Y y) :=
  isLimitOfPreserves Scheme.Spec (isLimitConeOfCoconeLeftOp _ (colimit.isColimit _))

/-- Every open neighbourhood contains an affine neighbourhood of the point. -/
private theorem exists_affine_neighborhood_below
    (Y : Scheme.{u}) (y : Y) (i : TopologicalSpace.OpenNhds y) :
    ∃ U : Y.affineOpens, y ∈ U.1 ∧ U.1 ≤ i.1 := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUi⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open i.property i.1.2
  exact ⟨⟨U, hU⟩, hyU, hUi⟩

/-- At an affine neighbourhood, the stage of the diagram is the neighbourhood itself. -/
private def affineStageIso
    (Y : Scheme.{u}) (y : Y) (U : Y.affineOpens) (hy : y ∈ U.1) :
    (openNeighborhoodRingDiagram Y y).obj ⟨U.1, hy⟩ ≅ U.1.toScheme :=
  U.2.isoSpec.symm

/-- At an affine stage the limiting projection, followed by the open immersion into the original
scheme, is the canonical morphism from the spectrum of the stalk. -/
private theorem affineStage_projection_toBase
    (Y : Scheme.{u}) (y : Y) (U : Y.affineOpens) (hy : y ∈ U.1) :
    (stalkSpecCone Y y).π.app ⟨U.1, hy⟩ ≫ (affineStageIso Y y U hy).hom ≫ U.1.ι =
      Y.fromSpecStalk y :=
  U.2.fromSpecStalk_eq_fromSpecStalk hy

/-- The closed point of the spectrum of the stalk projects to the original point in an affine
neighbourhood. -/
private theorem affineStage_closedPoint
    (Y : Scheme.{u}) (y : Y) (U : Y.affineOpens) (hy : y ∈ U.1) :
    ((stalkSpecCone Y y).π.app ⟨U.1, hy⟩ ≫ (affineStageIso Y y U hy).hom)
        (IsLocalRing.closedPoint (Y.presheaf.stalk y)) = ⟨y, hy⟩ := by
  change U.2.isoSpec.inv
    (Spec.map (Y.presheaf.germ U.1 y hy)
      (IsLocalRing.closedPoint (Y.presheaf.stalk y))) = ⟨y, hy⟩
  have hU : IsAffineOpen U.1 := U.2
  rw [← hU.isoSpec_hom_apply ⟨y, hy⟩]
  exact congrArg (fun f : U.1.toScheme ⟶ U.1.toScheme => f ⟨y, hy⟩) hU.isoSpec.hom_inv_id

/-- The projection from the spectrum of a stalk to an affine stage is a preimmersion. -/
private theorem affineStage_projection_isPreimmersion
    (Y : Scheme.{u}) (y : Y) (U : Y.affineOpens) (hy : y ∈ U.1) :
    IsPreimmersion ((stalkSpecCone Y y).π.app ⟨U.1, hy⟩) := by
  let b := (stalkSpecCone Y y).π.app ⟨U.1, hy⟩
  let k := (affineStageIso Y y U hy).hom ≫ U.1.ι
  have : IsOpenImmersion k := by
    dsimp [k]
    infer_instance
  have : IsPreimmersion (b ≫ k) := by
    change IsPreimmersion ((stalkSpecCone Y y).π.app ⟨U.1, hy⟩ ≫
      (affineStageIso Y y U hy).hom ≫ U.1.ι)
    rw [affineStage_projection_toBase Y y U hy]
    exact (inferInstance : IsPreimmersion (Y.fromSpecStalk y))
  exact @IsPreimmersion.of_comp _ _ _ b k inferInstance inferInstance

/-! ### Residue fields along preimmersions and pullback projections -/

/-- The first pullback projection preserves residue fields if the map on the other side does so at
the projected point. -/
alias pullback_fst_residueFieldMap_isIso := fst_residueFieldMap_isIso_of_snd

/-- Being an isomorphism on residue fields is unchanged when the underlying morphisms of schemes
are equal. -/
private theorem residueFieldMap_isIso_of_eq
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (x : X)
    [IsIso (g.residueFieldMap x)] : IsIso (f.residueFieldMap x) := by
  rw [Scheme.Hom.residueFieldMap_congr h x]
  infer_instance

/-! ### Étale models over a neighbourhood of the point -/

/-- A finitely presented scheme over the spectrum of a stalk is the base change of a finitely
presented scheme over the ring of sections of some open neighbourhood. -/
private theorem exists_model_over_stalk (Y : Scheme.{u}) (y : Y)
    (X : Over (Spec (Y.presheaf.stalk y))) (hX : FinitePresentation X.hom) :
    ∃ (i : TopologicalSpace.OpenNhds y)
      (Xᵢ : Over ((openNeighborhoodRingDiagram Y y).obj i)),
      FinitePresentation Xᵢ.hom ∧
        Nonempty (X ≅ (Over.pullback ((stalkSpecCone Y y).π.app i)).obj Xᵢ) :=
  LimitFPObjectDescent.exists_model_of_finitePresentation
    (openNeighborhoodRingDiagram Y y) _ (isLimit_stalkSpecCone Y y) X hX

/-- Étaleness of an object over a scheme is invariant under an isomorphism in the over
category. -/
private theorem etale_of_over_iso {S : Scheme.{u}} {W Z : Over S}
    [Etale W.hom] (e : W ≅ Z) : Etale Z.hom := by
  have hinv : IsIso ((Over.forget S).map e.inv) := inferInstance
  change IsIso e.inv.left at hinv
  rw [← e.inv.w]
  infer_instance

/-- An étale model pulled back to the local base gives the étaleness hypothesis needed to descend
its structure morphism. -/
private theorem etale_pullback_hom_of_iso
    {S T : Scheme.{u}} (b : S ⟶ T) (X : Over T)
    (W : Over S) [Etale W.hom]
    (e : W ≅ (Over.pullback b).obj X) :
    Etale ((Over.pullback b).map
      (Over.homMk X.hom (show X.hom ≫ (𝟙 T) = X.hom by simp) :
        X ⟶ Over.mk (𝟙 T))).left := by
  let f : X ⟶ Over.mk (𝟙 T) := Over.homMk X.hom (by simp)
  change Etale ((Over.pullback b).map f).left
  have hX : Etale ((Over.pullback b).obj X).hom := etale_of_over_iso e
  refine MorphismProperty.of_postcomp @Etale (W' := @Etale) _ (pullback.snd (𝟙 T) b)
    inferInstance ?_
  change Etale (((Over.pullback b).map f).left ≫ ((Over.pullback b).obj (Over.mk (𝟙 T))).hom)
  rwa [Over.w]

/-- Étaleness of the morphism obtained by pulling back a structure morphism gives étaleness of the
pulled-back object over the new base. -/
private theorem etale_pullback_obj_of_etale_map
    {S T : Scheme.{u}} (b : S ⟶ T) (X : Over T)
    (h : Etale ((Over.pullback b).map
      (Over.homMk X.hom (show X.hom ≫ (𝟙 T) = X.hom by simp) :
        X ⟶ Over.mk (𝟙 T))).left) :
    Etale ((Over.pullback b).obj X).hom := by
  let f : X ⟶ Over.mk (𝟙 T) := Over.homMk X.hom (by simp)
  have : Etale ((Over.pullback b).map f).left := h
  have : Etale ((Over.pullback b).obj (Over.mk (𝟙 T))).hom := by
    change Etale (pullback.snd (𝟙 T) b)
    infer_instance
  rw [← Over.w ((Over.pullback b).map f)]
  infer_instance

/-- An étale finitely presented scheme over the spectrum of a stalk is modelled by a scheme over
the ring of sections of a neighbourhood, and its structure morphism becomes étale at a finite
stage. -/
private theorem exists_etale_model_over_stalk
    (Y : Scheme.{u}) (y : Y)
    (W : Over (Spec (Y.presheaf.stalk y)))
    (hfp : FinitePresentation W.hom) [Etale W.hom] :
    ∃ (i : TopologicalSpace.OpenNhds y)
      (Xᵢ : Over ((openNeighborhoodRingDiagram Y y).obj i)),
      FinitePresentation Xᵢ.hom ∧
      Nonempty (W ≅ (Over.pullback ((stalkSpecCone Y y).π.app i)).obj Xᵢ) ∧
      ∃ j : Over i,
        Etale ((Over.pullback ((openNeighborhoodRingDiagram Y y).map j.hom)).map
          (Over.homMk Xᵢ.hom (by simp) :
            Xᵢ ⟶ Over.mk (𝟙 ((openNeighborhoodRingDiagram Y y).obj i)))).left := by
  obtain ⟨i, Xᵢ, hXi, ⟨e⟩⟩ := exists_model_over_stalk Y y W hfp
  let D := openNeighborhoodRingDiagram Y y
  let f₀ : Xᵢ ⟶ Over.mk (𝟙 (D.obj i)) := Over.homMk Xᵢ.hom (by simp)
  have : QuasiCompact Xᵢ.hom := hXi.quasiCompact
  have : QuasiSeparated Xᵢ.hom := hXi.quasiSeparated
  have : CompactSpace Xᵢ.left := QuasiCompact.compactSpace_of_compactSpace Xᵢ.hom
  have : QuasiSeparatedSpace Xᵢ.left := quasiSeparatedSpace_of_quasiSeparated Xᵢ.hom
  have : CompactSpace (Over.mk (𝟙 (D.obj i))).left := by
    change CompactSpace (D.obj i)
    infer_instance
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i))).left := by
    change QuasiSeparatedSpace (D.obj i)
    infer_instance
  have : LocallyOfFinitePresentation f₀.left := hXi.locallyOfFinitePresentation
  have : Etale ((Over.pullback ((stalkSpecCone Y y).π.app i)).map f₀).left :=
    etale_pullback_hom_of_iso (S := Spec (Y.presheaf.stalk y)) (T := D.obj i)
      ((stalkSpecCone Y y).π.app i) Xᵢ W e
  obtain ⟨j, hj⟩ := exists_etale_pullback_of_isLimit
    D (stalkSpecCone Y y) (isLimit_stalkSpecCone Y y) i Xᵢ (Over.mk (𝟙 (D.obj i))) f₀
  exact ⟨i, Xᵢ, hXi, ⟨e⟩, j, hj⟩

/-! ### Algebraic input -/

/-- Stacks 0593 over the base of a pushout: a module projective over the base becomes free after
the base change to a local ring. -/
private theorem free_of_projective_pushout
    {R A B T M : Type*} [CommRing R] [CommRing A] [CommRing B]
    [CommRing T] [Algebra R A] [Algebra R B] [Algebra R T]
    [Algebra A T] [Algebra B T] [IsScalarTower R A T]
    [IsScalarTower R B T] [Algebra.IsPushout R B A T]
    [IsLocalRing B] [AddCommGroup M] [Module A M]
    [Module R M] [IsScalarTower R A M] [Module.Projective R M] :
    Module.Free B (T ⊗[A] M) := by
  have : Module.Free B (B ⊗[R] M) := Module.free_of_projective_of_isLocalRing
  exact Module.Free.of_equiv (Algebra.IsPushout.cancelBaseChange R B A T M).symm

/-- On affine schemes the global sections of the pullback of a quasi-coherent module are the
extension of scalars of its global sections. -/
private def affinePullbackSectionsEquiv {Y Z : Scheme.{u}} [IsAffine Y] [IsAffine Z]
    (a : Z ⟶ Y) (N : Y.Modules) [N.IsQuasicoherent] :
    letI : Algebra Γ(Y, ⊤) Γ(Z, ⊤) := a.appTop.hom.toAlgebra
    Γ(Z, ⊤) ⊗[Γ(Y, ⊤)] Γ(N, ⊤) ≃ₗ[Γ(Z, ⊤)]
      Γ((Scheme.Modules.pullback a).obj N, ⊤) := by
  have happ : a.appTop = a.appLE ⊤ ⊤ le_rfl := (Scheme.Hom.appLE_eq_app a).symm
  rw [happ]
  exact (affinePullbackSectionsBaseChangeIso a N (isAffineOpen_top Y)
    (isAffineOpen_top Z) le_rfl).toLinearEquiv

/-! ### Geometric input -/

/-- If an open subscheme contains the unique point above `x`, that point lies above every
prescribed point in the base fibre. -/
private theorem unique_fiber_open_point_maps_to
    {X S T : Scheme.{u}} (f : X ⟶ S) (b : T ⟶ S)
    (x : X) (s : T) (hxs : f x = b s)
    (V : (pullback f b).Opens) (v : V)
    (hfiber : pullback.fst f b ⁻¹' {x} = {V.ι v}) :
    (V.ι ≫ pullback.snd f b) v = s := by
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x s hxs
  obtain rfl : z = V.ι v := by
    have hmem : z ∈ pullback.fst f b ⁻¹' {x} := by simpa using hz₁
    simpa [hfiber] using hmem
  exact hz₂

/-- The morphism between two pullbacks induced by a morphism of their first factors is itself a
base change of that morphism. -/
private theorem pullback_map_first_isPullback
    {A B T T' : Scheme.{u}} (a : A ⟶ B) (u : A ⟶ T)
    (v : B ⟶ T) (r : T' ⟶ T) (h : a ≫ v = u) :
    IsPullback
      (pullback.lift (pullback.fst u r ≫ a) (pullback.snd u r)
        (by rw [Category.assoc, h, pullback.condition]))
      (pullback.fst u r) (pullback.fst v r) a := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback v r).flip
  rw [pullback.lift_snd, h]
  exact (IsPullback.of_hasPullback u r).flip

/-- If `t` is the base change of `w` along `c ≫ d`, then its lift `P ⟶ W ×_B B'` is the base change
of the second projection of `W ×_B B'` along `c`. -/
private theorem isPullback_lift_snd_of_comp
    {P W B B' Z : Scheme.{u}} (t : P ⟶ W) (τ : P ⟶ Z) (w : W ⟶ B) (d : B' ⟶ B) (c : Z ⟶ B')
    (hp : IsPullback t τ w (c ≫ d)) (h : t ≫ w = (τ ≫ c) ≫ d) :
    IsPullback (pullback.lift t (τ ≫ c) h) τ (pullback.snd w d) c := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback w d)
  rwa [pullback.lift_fst]

/-- The freeness of the global sections in Tag 05KY. On the pullback square of affine schemes
produced by Tag 05ID, the global sections of the pulled-back module are the base change of
sections projective over the lower-left corner, hence free over the local ring of the lower-right
corner (Stacks 0593). -/
private theorem free_globalSections_pullback_of_projective
    {V₁ U₁ : Scheme.{u}} [IsAffine V₁] [IsAffine U₁]
    (A : Type u) [CommRing A] (hA : IsLocalRing A)
    (h₁ : U₁ ⟶ V₁) (ρ : Spec (.of A) ⟶ V₁)
    (M₁ : U₁.Modules) [M₁.IsQuasicoherent]
    (hproj : letI : Module Γ(V₁, ⊤) Γ(M₁, ⊤) := Module.compHom _ h₁.appTop.hom
      Module.Projective Γ(V₁, ⊤) Γ(M₁, ⊤)) :
    letI : Module A Γ((Scheme.Modules.pullback (pullback.fst h₁ ρ)).obj M₁, ⊤) :=
      Module.compHom _
        ((Scheme.ΓSpecIso (.of A)).inv ≫ (pullback.snd h₁ ρ).appTop).hom
    Module.Free A Γ((Scheme.Modules.pullback (pullback.fst h₁ ρ)).obj M₁, ⊤) := by
  have := hA
  let p₁ : pullback h₁ ρ ⟶ U₁ := pullback.fst h₁ ρ
  let q : pullback h₁ ρ ⟶ Spec (.of A) := pullback.snd h₁ ρ
  have : IsAffine (pullback h₁ ρ) := by
    have : IsAffineHom h₁ := isAffineHom_of_isAffine h₁
    exact isAffine_of_isAffineHom q
  let M₂ : (pullback h₁ ρ).Modules := (Scheme.Modules.pullback p₁).obj M₁
  let R := Γ(V₁, ⊤)
  let B := Γ(U₁, ⊤)
  let I := Γ(Spec (.of A), ⊤)
  let T := Γ(pullback h₁ ρ, ⊤)
  let σ : A ≃+* I := (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv
  have : IsLocalRing I := σ.isLocalRing
  let : Algebra R B := h₁.appTop.hom.toAlgebra
  let : Algebra R I := ρ.appTop.hom.toAlgebra
  let : Algebra B T := p₁.appTop.hom.toAlgebra
  let : Algebra I T := q.appTop.hom.toAlgebra
  let : Algebra R T := (h₁.appTop ≫ p₁.appTop).hom.toAlgebra
  have hPush : IsPushout h₁.appTop ρ.appTop p₁.appTop q.appTop :=
    isPushout_appTop_of_isPullback (IsPullback.of_hasPullback h₁ ρ)
  have : IsScalarTower R B T := .of_algebraMap_eq' rfl
  have : IsScalarTower R I T := .of_algebraMap_eq' <| congr($(hPush.1.1).hom)
  have : Algebra.IsPushout R I B T := (CommRingCat.isPushout_iff_isPushout.mp hPush).symm
  let : Module R Γ(M₁, ⊤) := Module.compHom _ h₁.appTop.hom
  have : IsScalarTower R B Γ(M₁, ⊤) := ⟨fun r b m => mul_smul (h₁.appTop.hom r) b m⟩
  have : Module.Projective R Γ(M₁, ⊤) := hproj
  have hFreeTensor : Module.Free I (T ⊗[B] Γ(M₁, ⊤)) :=
    free_of_projective_pushout (R := R) (A := B) (B := I) (T := T) (M := Γ(M₁, ⊤))
  let eAffine := affinePullbackSectionsEquiv p₁ M₁
  let : Module I Γ(M₂, ⊤) := Module.compHom _ q.appTop.hom
  have : LinearMap.CompatibleSMul (T ⊗[B] Γ(M₁, ⊤)) Γ(M₂, ⊤) I T :=
    ⟨fun e r z => e.map_smul (q.appTop.hom r) z⟩
  have hFreeI : Module.Free I Γ(M₂, ⊤) := Module.Free.of_equiv (eAffine.restrictScalars I)
  let : Module A Γ(M₂, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (.of A)).inv ≫ q.appTop).hom
  have : RingHomInvPair σ.toRingHom σ.symm.toRingHom := ⟨σ.symm_comp, σ.comp_symm⟩
  have : RingHomInvPair σ.symm.toRingHom σ.toRingHom := ⟨σ.comp_symm, σ.symm_comp⟩
  let eσ : Γ(M₂, ⊤) ≃ₛₗ[σ.toRingHom] Γ(M₂, ⊤) :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Free.of_equiv (R := I) (R' := A) (M := Γ(M₂, ⊤)) (M' := Γ(M₂, ⊤)) eσ.symm

/-- Freeness of the global sections transports along an isomorphism of modules, for the scalar
action of a ring restricted along a morphism to its spectrum. -/
private theorem free_globalSections_of_iso {X' : Scheme.{u}} (A : Type u) [CommRing A]
    (q : X' ⟶ Spec (.of A)) {M N : X'.Modules} (e : M ≅ N)
    (hM : letI : Module A Γ(M, ⊤) :=
        Module.compHom _ ((Scheme.ΓSpecIso (.of A)).inv ≫ q.appTop).hom
      Module.Free A Γ(M, ⊤)) :
    letI : Module A Γ(N, ⊤) :=
      Module.compHom _ ((Scheme.ΓSpecIso (.of A)).inv ≫ q.appTop).hom
    Module.Free A Γ(N, ⊤) := by
  let φ := ((Scheme.ΓSpecIso (.of A)).inv ≫ q.appTop).hom
  let : Module A Γ(M, ⊤) := Module.compHom _ φ
  let : Module A Γ(N, ⊤) := Module.compHom _ φ
  have : Module.Free A Γ(M, ⊤) := hM
  have : LinearMap.CompatibleSMul Γ(M, ⊤) Γ(N, ⊤) A Γ(X', ⊤) :=
    ⟨fun k r z => k.map_smul (φ r) z⟩
  exact Module.Free.of_equiv ((sectionsLinearEquivOfIso e ⊤).restrictScalars A)

/-- Base change of the étale comparison morphism. If `t : U ⟶ X ×_S V` is étale with second
component `h`, then for every `ρ : W ⟶ V` the induced morphism `U ×_V W ⟶ X ×_S W` is étale. -/
private theorem etale_pullbackLift_baseChange
    {X S V W U : Scheme.{u}} (f : X ⟶ S) (bV : V ⟶ S) (ρ : W ⟶ V)
    (h : U ⟶ V) (t : U ⟶ pullback f bV) [Etale t]
    (ht : t ≫ pullback.snd f bV = h)
    (hcomm : (pullback.fst h ρ ≫ t ≫ pullback.fst f bV) ≫ f =
      pullback.snd h ρ ≫ ρ ≫ bV) :
    Etale (pullback.lift (pullback.fst h ρ ≫ t ≫ pullback.fst f bV)
      (pullback.snd h ρ) hcomm) := by
  let a₂ : pullback h ρ ⟶ pullback (pullback.snd f bV) ρ :=
    pullback.lift (pullback.fst h ρ ≫ t) (pullback.snd h ρ) (by
      rw [Category.assoc, ht]
      exact pullback.condition)
  have ha₂PB : IsPullback a₂ (pullback.fst h ρ) (pullback.fst (pullback.snd f bV) ρ) t :=
    pullback_map_first_isPullback t h (pullback.snd f bV) ρ ht
  have ha₂ : Etale a₂ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback ha₂PB.flip inferInstance
  have hl : pullback.lift (pullback.fst h ρ ≫ t ≫ pullback.fst f bV)
      (pullback.snd h ρ) hcomm = a₂ ≫ (pullbackLeftPullbackSndIso f bV ρ).hom := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
        ← Category.assoc a₂ (pullback.fst (pullback.snd f bV) ρ) (pullback.fst f bV),
        show a₂ ≫ pullback.fst (pullback.snd f bV) ρ = pullback.fst h ρ ≫ t from
          pullback.lift_fst _ _ _]
      exact (Category.assoc _ _ _).symm
    · rw [pullback.lift_snd, Category.assoc, pullbackLeftPullbackSndIso_hom_snd]
      exact (pullback.lift_snd _ _ _).symm
  rw [hl]
  infer_instance

/-- Descent of an elementary étale neighbourhood along the spectrum of a local ring. An affine
elementary étale neighbourhood of the closed point of `Spec 𝒪_{U, u}`, for `U` an elementary étale
neighbourhood of `(S, s)`, is dominated by an elementary étale neighbourhood `U'` of `(S, s)`: the
spectrum of the local ring of `U'` maps to it by a preimmersion carrying the closed point to its
distinguished point and commuting with the structure morphisms to `S`.

The neighbourhood is of finite presentation over `Spec 𝒪_{U, u}`, which is the limit of the
spectra of the rings of sections on the open neighbourhoods of `u`, so it has a model at a finite
stage, étale after shrinking (Tag 01ZM); shrinking further to an affine open of `U` makes that
stage an elementary étale neighbourhood of `(S, s)`. -/
private theorem exists_elementaryNeighborhood_stalkDescent
    {S : Scheme.{u}} {s : S} (U : EtaleNeighborhood S s) (hU : U.IsElementary)
    {z : (Spec (U.scheme.presheaf.stalk U.point) : Scheme.{u})}
    (V : EtaleNeighborhood (Spec (U.scheme.presheaf.stalk U.point)) z)
    (hV : V.IsElementary) (hVaff : IsAffine V.scheme)
    (hz : z = IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point)) :
    ∃ (U' : EtaleNeighborhood S s) (_ : U'.IsElementary)
      (ρ : Spec (U'.scheme.presheaf.stalk U'.point) ⟶ V.scheme),
      IsPreimmersion ρ ∧
      ρ (IsLocalRing.closedPoint (U'.scheme.presheaf.stalk U'.point)) = V.point ∧
      ρ ≫ V.toBase ≫ U.scheme.fromSpecStalk U.point ≫ U.toBase =
        U'.scheme.fromSpecStalk U'.point ≫ U'.toBase := by
  have : IsAffine V.scheme := hVaff
  have hVfp : FinitePresentation V.toBase :=
    FinitePresentation.mk inferInstance inferInstance inferInstance
  have : Etale (Over.mk V.toBase).hom := by
    change Etale V.toBase; infer_instance
  obtain ⟨i₁, Wᵢ, hWᵢfp, ⟨eWᵢ⟩, j₁, hWⱼEtale⟩ :=
    exists_etale_model_over_stalk U.scheme U.point (Over.mk V.toBase) hVfp
  let D := openNeighborhoodRingDiagram U.scheme U.point
  let Wⱼ : Over (D.obj j₁.left) := (Over.pullback (D.map j₁.hom)).obj Wᵢ
  have hWⱼ : Etale Wⱼ.hom := etale_pullback_obj_of_etale_map (D.map j₁.hom) Wᵢ hWⱼEtale
  obtain ⟨A, hApoint, hAle⟩ :=
    exists_affine_neighborhood_below U.scheme U.point j₁.left
  let a : TopologicalSpace.OpenNhds U.point := ⟨A.1, hApoint⟩
  let α : a ⟶ j₁.left := homOfLE hAle
  let Wₐ : Over (D.obj a) := (Over.pullback (D.map α)).obj Wⱼ
  have hWₐ : Etale Wₐ.hom := by
    change Etale (pullback.snd Wⱼ.hom (D.map α)); infer_instance
  let c : Cone D := stalkSpecCone U.scheme U.point
  let tᵢ : V.scheme ⟶ Wᵢ.left :=
    eWᵢ.hom.left ≫ pullback.fst Wᵢ.hom (c.π.app i₁)
  have heWᵢ : eWᵢ.hom.left ≫ pullback.snd Wᵢ.hom (c.π.app i₁) = V.toBase := eWᵢ.hom.w
  have htᵢ : tᵢ ≫ Wᵢ.hom = V.toBase ≫ c.π.app i₁ := by
    dsimp only [tᵢ]
    rw [Category.assoc, pullback.condition, ← Category.assoc, heWᵢ]
    rfl
  have hcⱼ : c.π.app j₁.left ≫ D.map j₁.hom = c.π.app i₁ := c.w j₁.hom
  have hcₐ : c.π.app a ≫ D.map α = c.π.app j₁.left := c.w α
  have htᵢPB : IsPullback tᵢ V.toBase Wᵢ.hom (c.π.app i₁) :=
    IsPullback.of_iso_pullback ⟨htᵢ⟩ ((Over.forget _).mapIso eWᵢ) rfl heWᵢ
  have htⱼ : tᵢ ≫ Wᵢ.hom = (V.toBase ≫ c.π.app j₁.left) ≫ D.map j₁.hom := by
    rw [htᵢ, ← hcⱼ]
    exact (Category.assoc _ _ _).symm
  let γⱼ : V.scheme ⟶ Wⱼ.left := pullback.lift tᵢ (V.toBase ≫ c.π.app j₁.left) htⱼ
  have hγⱼ : γⱼ ≫ Wⱼ.hom = V.toBase ≫ c.π.app j₁.left := pullback.lift_snd _ _ _
  have hγⱼPB : IsPullback γⱼ V.toBase Wⱼ.hom (c.π.app j₁.left) :=
    isPullback_lift_snd_of_comp tᵢ V.toBase Wᵢ.hom (D.map j₁.hom) (c.π.app j₁.left)
      (by rw [← hcⱼ] at htᵢPB; exact htᵢPB) htⱼ
  have htₐ : γⱼ ≫ Wⱼ.hom = (V.toBase ≫ c.π.app a) ≫ D.map α := by
    rw [hγⱼ, ← hcₐ]
    exact (Category.assoc _ _ _).symm
  let γₐ : V.scheme ⟶ Wₐ.left := pullback.lift γⱼ (V.toBase ≫ c.π.app a) htₐ
  have hγₐ : γₐ ≫ Wₐ.hom = V.toBase ≫ c.π.app a := pullback.lift_snd _ _ _
  have hγₐPB : IsPullback γₐ V.toBase Wₐ.hom (c.π.app a) :=
    isPullback_lift_snd_of_comp γⱼ V.toBase Wⱼ.hom (D.map α) (c.π.app a)
      (by rw [← hcₐ] at hγⱼPB; exact hγⱼPB) htₐ
  have hcₐPre : IsPreimmersion (c.π.app a) :=
    affineStage_projection_isPreimmersion U.scheme U.point A hApoint
  have hγₐPre : IsPreimmersion γₐ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hγₐPB.flip hcₐPre
  have hγₐres : IsIso (γₐ.residueFieldMap V.point) :=
    isIso_residueFieldMap_of_isPreimmersion γₐ V.point
  have hVres : IsIso (V.toBase.residueFieldMap V.point) :=
    (V.isElementary_iff).mp hV
  have hWₐres : IsIso (Wₐ.hom.residueFieldMap (γₐ V.point)) := by
    have hcomp : IsIso ((V.toBase ≫ c.π.app a).residueFieldMap V.point) :=
      isIso_residueFieldMap_comp V.toBase (c.π.app a) V.point hVres
        (isIso_residueFieldMap_of_isPreimmersion (c.π.app a) _)
    have hsplit : IsIso (Wₐ.hom.residueFieldMap (γₐ V.point) ≫
        γₐ.residueFieldMap V.point) := by
      have hone : IsIso ((γₐ ≫ Wₐ.hom).residueFieldMap V.point) :=
        residueFieldMap_isIso_of_eq hγₐ V.point
      rw [Scheme.residueFieldMap_comp γₐ Wₐ.hom V.point] at hone
      exact hone
    exact IsIso.of_isIso_comp_right (Wₐ.hom.residueFieldMap (γₐ V.point))
      (γₐ.residueFieldMap V.point)
  have hγₐpoint : Wₐ.hom (γₐ V.point) = (c.π.app a) (V.toBase V.point) :=
    congrArg (fun h : V.scheme ⟶ D.obj a => h V.point) hγₐ
  have hVpoint : V.toBase V.point =
      IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point) :=
    V.map_point.trans hz
  have hAclosed :
      (affineStageIso U.scheme U.point A hApoint).hom
        ((c.π.app a) (IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point))) =
      (⟨U.point, hApoint⟩ : A.1.toScheme) :=
    affineStage_closedPoint U.scheme U.point A hApoint
  let k : D.obj a ⟶ U.scheme :=
    (affineStageIso U.scheme U.point A hApoint).hom ≫ A.1.ι
  have hkOpen : IsOpenImmersion k := by dsimp [k]; infer_instance
  let m : Wₐ.left ⟶ U.scheme := Wₐ.hom ≫ k
  have hmpoint : m (γₐ V.point) = U.point := by
    change A.1.ι ((affineStageIso U.scheme U.point A hApoint).hom
      (Wₐ.hom (γₐ V.point))) = U.point
    rw [hγₐpoint, hVpoint, hAclosed]
    rfl
  let U' : EtaleNeighborhood S s :=
    { scheme := Wₐ.left
      point := γₐ V.point
      toBase := m ≫ U.toBase
      map_point := by
        change U.toBase (m (γₐ V.point)) = s
        rw [hmpoint]
        exact U.map_point }
  have hUres : IsIso (U.toBase.residueFieldMap U.point) := (U.isElementary_iff).mp hU
  have hkPre : IsPreimmersion k := inferInstance
  have hmres : IsIso (m.residueFieldMap (γₐ V.point)) :=
    isIso_residueFieldMap_comp Wₐ.hom k (γₐ V.point) hWₐres
      (isIso_residueFieldMap_of_isPreimmersion k (Wₐ.hom (γₐ V.point)))
  have hU'res : IsIso (U'.toBase.residueFieldMap U'.point) := by
    refine isIso_residueFieldMap_comp m U.toBase (γₐ V.point) hmres ?_
    rw [hmpoint]
    exact hUres
  have hU' : U'.IsElementary := (U'.isElementary_iff).mpr hU'res
  have hm : m U'.point = U.point := hmpoint
  let r : Spec (U'.scheme.presheaf.stalk U'.point) ⟶
      Spec (U.scheme.presheaf.stalk U.point) :=
    Spec.map (U.scheme.presheaf.stalkSpecializes (specializes_of_eq hm) ≫
      m.stalkMap U'.point)
  have hr : r ≫ U.scheme.fromSpecStalk U.point =
      U'.scheme.fromSpecStalk U'.point ≫ m := by
    dsimp [r]
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  have hck : c.π.app a ≫ k = U.scheme.fromSpecStalk U.point :=
    affineStage_projection_toBase U.scheme U.point A hApoint
  have hrc : U'.scheme.fromSpecStalk U'.point ≫ Wₐ.hom = r ≫ c.π.app a := by
    rw [← cancel_mono k]
    calc
      (U'.scheme.fromSpecStalk U'.point ≫ Wₐ.hom) ≫ k =
          U'.scheme.fromSpecStalk U'.point ≫ m := by simp [m, Category.assoc]
      _ = r ≫ U.scheme.fromSpecStalk U.point := hr.symm
      _ = r ≫ (c.π.app a ≫ k) := congrArg (fun z => r ≫ z) hck.symm
      _ = (r ≫ c.π.app a) ≫ k := (Category.assoc _ _ _).symm
  let ρ : Spec (U'.scheme.presheaf.stalk U'.point) ⟶ V.scheme :=
    pullback.lift (U'.scheme.fromSpecStalk U'.point) r hrc ≫ hγₐPB.isoPullback.inv
  have hργ : ρ ≫ γₐ = U'.scheme.fromSpecStalk U'.point := by
    dsimp [ρ]
    rw [Category.assoc, hγₐPB.isoPullback_inv_fst]
    exact pullback.lift_fst _ _ _
  have hρbase : ρ ≫ V.toBase = r := by
    dsimp [ρ]
    rw [Category.assoc, hγₐPB.isoPullback_inv_snd]
    exact pullback.lift_snd _ _ _
  have hρclosed : ρ (IsLocalRing.closedPoint
      (U'.scheme.presheaf.stalk U'.point)) = V.point := by
    refine γₐ.isEmbedding.injective ?_
    change (ρ ≫ γₐ) (IsLocalRing.closedPoint (U'.scheme.presheaf.stalk U'.point)) =
      γₐ V.point
    rw [hργ, Scheme.fromSpecStalk_closedPoint]
  have hρPre : IsPreimmersion ρ := by
    have : IsPreimmersion (ρ ≫ γₐ) := by rw [hργ]; infer_instance
    exact @IsPreimmersion.of_comp _ _ _ ρ γₐ hγₐPre inferInstance
  refine ⟨U', hU', ρ, hρPre, hρclosed, ?_⟩
  calc ρ ≫ V.toBase ≫ U.scheme.fromSpecStalk U.point ≫ U.toBase
      = (ρ ≫ V.toBase) ≫ U.scheme.fromSpecStalk U.point ≫ U.toBase :=
        (Category.assoc _ _ _).symm
    _ = r ≫ U.scheme.fromSpecStalk U.point ≫ U.toBase := by rw [hρbase]
    _ = (r ≫ U.scheme.fromSpecStalk U.point) ≫ U.toBase := (Category.assoc _ _ _).symm
    _ = (U'.scheme.fromSpecStalk U'.point ≫ m) ≫ U.toBase := by rw [hr]
    _ = U'.scheme.fromSpecStalk U'.point ≫ U'.toBase := Category.assoc _ _ _

/-! ### Tag 05KY -/

/-- **Stacks Project, Tag 05KY.** Let `f : X ⟶ S` be locally of finite presentation, let `F` be a
quasi-coherent `𝒪_X`-module of finite type and let `x ∈ X` be a point at which `F` is flat over
`S`. Then there is an elementary étale neighbourhood `(S', s') ⟶ (S, s)` of the image `s` of `x`
and a commutative diagram of pointed schemes
```
  (X, x) ← (X', x')
    ↓         ↓
  (S, s) ← Spec 𝒪_{S', s'}
```
such that `X' ⟶ X ×_S Spec 𝒪_{S', s'}` is étale, `κ(x) = κ(x')`, `X'` is affine and of finite
presentation over `𝒪_{S', s'}`, `g^*F` is of finite presentation, and `Γ(X', g^*F)` is a free
`𝒪_{S', s'}`-module.

The two inputs are Tag 05ID,
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt`, and
Tag 05I5, `AlgebraicGeometry.existsElementaryEtaleNeighborhoodFinitePresentationFlatOver`. -/
@[stacks 05KY]
theorem exists_etale_neighborhood_with_free_globalSections_of_isFiniteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (x : X) (hflat : IsFlatOverAt f.toLRSHom.toShHom F x) :
    ∃ (U : EtaleNeighborhood S (f x)) (_ : U.IsElementary)
      (X' : Scheme.{u}) (x' : X')
      (g : X' ⟶ X)
      (q : X' ⟶ Spec (.of (U.scheme.presheaf.stalk U.point)))
      (_ : g x' = x)
      (_ : q x' = IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point))
      (hcomm : g ≫ f = q ≫ U.scheme.fromSpecStalk U.point ≫ U.toBase)
      (_ : Etale (pullback.lift g q hcomm))
      (_ : IsIso (g.residueFieldMap x'))
      (_ : IsAffine X')
      (_ : FinitePresentation q)
      (_ : ((Scheme.Modules.pullback g).obj F).IsFinitePresentation),
      letI : Module (U.scheme.presheaf.stalk U.point)
          Γ((Scheme.Modules.pullback g).obj F, ⊤) :=
        Module.compHom _
          ((Scheme.ΓSpecIso (.of (U.scheme.presheaf.stalk U.point))).inv ≫ q.appTop).hom
      Module.Free (U.scheme.presheaf.stalk U.point)
        Γ((Scheme.Modules.pullback g).obj F, ⊤) := by
  obtain ⟨U₀, hU₀, V₀, v₀, hv₀, hfp₀, hflat₀⟩ :=
    (show ExistsElementaryEtaleNeighborhoodFinitePresentationFlatOver.{u} from
          @existsElementaryEtaleNeighborhoodFinitePresentationFlatOver.{u}) f F x hflat
  let b₀ : Spec (U₀.scheme.presheaf.stalk U₀.point) ⟶ S :=
    U₀.scheme.fromSpecStalk U₀.point ≫ U₀.toBase
  let f₀ : V₀.toScheme ⟶ Spec (U₀.scheme.presheaf.stalk U₀.point) :=
    V₀.ι ≫ pullback.snd f b₀
  have hclosed₀ : f₀ v₀ = IsLocalRing.closedPoint
      (U₀.scheme.presheaf.stalk U₀.point) := by
    refine unique_fiber_open_point_maps_to f b₀ x _ ?_ V₀ v₀ hv₀
    change f x = U₀.toBase
      (U₀.scheme.fromSpecStalk U₀.point
        (IsLocalRing.closedPoint (U₀.scheme.presheaf.stalk U₀.point)))
    rw [Scheme.fromSpecStalk_closedPoint, U₀.map_point]
  let F₀ : V₀.toScheme.Modules :=
    (Scheme.Modules.pullback (V₀.ι ≫ pullback.fst f b₀)).obj F
  have : F₀.IsFinitePresentation := hfp₀
  have hF₀qc : F₀.IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ _
      (V₀.ι ≫ pullback.fst f b₀).toLRSHom.toShHom F (show F.IsQuasicoherent from inferInstance)
  have : LocallyOfFinitePresentation f₀ := inferInstance
  have hflatAt₀ : IsFlatOverAt f₀.toLRSHom.toShHom F₀ v₀ := hflat₀ v₀
  have hID : ExistsElementaryEtaleNeighborhoodProjectiveSections.{u} := by
    intro X S f _ F _ _ x hflat
    exact exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt f F x hflat
  obtain ⟨V₁, U₁, h₁, hV₁, hU₁, hcomp₁, hpoint₁, hAffineU₁, hAffineV₁, hProjective₁⟩ :=
    hID f₀ F₀ v₀ hflatAt₀
  have : IsAffine V₁.scheme := hAffineV₁
  obtain ⟨U₂, hU₂, ρ, hρPre, hρclosed, hρb⟩ :=
    exists_elementaryNeighborhood_stalkDescent U₀ hU₀ V₁ hV₁ hAffineV₁ hclosed₀
  let X' : Scheme.{u} := pullback h₁ ρ
  obtain ⟨x', hx'₁, hx'₂⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := h₁) (g := ρ) U₁.point
      (IsLocalRing.closedPoint (U₂.scheme.presheaf.stalk U₂.point))
      (hpoint₁.trans hρclosed.symm)
  let q : X' ⟶ Spec (U₂.scheme.presheaf.stalk U₂.point) := pullback.snd h₁ ρ
  have hfstRes : IsIso ((pullback.fst h₁ ρ).residueFieldMap x') :=
    isIso_residueFieldMap_of_isPreimmersion _ _
  have hqx : q x' = IsLocalRing.closedPoint (U₂.scheme.presheaf.stalk U₂.point) := hx'₂
  have : IsAffine U₁.scheme := hAffineU₁
  have : IsAffine X' := by dsimp [X']; infer_instance
  let g : X' ⟶ X := pullback.fst h₁ ρ ≫ U₁.toBase ≫ V₀.ι ≫ pullback.fst f b₀
  have hv₀x : (pullback.fst f b₀) (V₀.ι v₀) = x := by
    have hv : V₀.ι v₀ ∈ pullback.fst f b₀ ⁻¹' {x} := by rw [hv₀]; rfl
    simpa using hv
  have hgx : g x' = x := by
    change (pullback.fst f b₀) (V₀.ι (U₁.toBase ((pullback.fst h₁ ρ) x'))) = x
    rw [hx'₁, U₁.map_point]
    exact hv₀x
  have hgf₀ : V₀.ι ≫ pullback.fst f b₀ ≫ f = f₀ ≫ b₀ := by
    dsimp [f₀]
    rw [Category.assoc, pullback.condition]
  let b₁ : V₁.scheme ⟶ S := V₁.toBase ≫ b₀
  let k₁ : pullback f b₁ ⟶ pullback f b₀ :=
    (pullbackLeftPullbackSndIso f b₀ V₁.toBase).inv ≫
      pullback.fst (pullback.snd f b₀) V₁.toBase
  have hk₁ : Etale k₁ := by dsimp [k₁]; infer_instance
  have ht₁comm : (U₁.toBase ≫ V₀.ι ≫ pullback.fst f b₀) ≫ f = h₁ ≫ b₁ := by
    calc
      (U₁.toBase ≫ V₀.ι ≫ pullback.fst f b₀) ≫ f = U₁.toBase ≫ f₀ ≫ b₀ := by
        simpa only [Category.assoc] using congrArg (fun z => U₁.toBase ≫ z) hgf₀
      _ = h₁ ≫ V₁.toBase ≫ b₀ := by
        simpa only [Category.assoc] using congrArg (fun z => z ≫ b₀) hcomp₁.symm
      _ = h₁ ≫ b₁ := rfl
  let t₁ : U₁.scheme ⟶ pullback f b₁ :=
    pullback.lift (U₁.toBase ≫ V₀.ι ≫ pullback.fst f b₀) h₁ ht₁comm
  have ht₁snd : t₁ ≫ pullback.snd f b₁ = h₁ := pullback.lift_snd _ _ _
  have ht₁fst : t₁ ≫ pullback.fst f b₁ = U₁.toBase ≫ V₀.ι ≫ pullback.fst f b₀ :=
    pullback.lift_fst _ _ _
  have ht₁k₁ : t₁ ≫ k₁ = U₁.toBase ≫ V₀.ι := by
    refine pullback.hom_ext ?_ ?_
    · dsimp only [k₁]
      simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_fst]
      exact ht₁fst
    · change t₁ ≫ k₁ ≫ pullback.snd f b₀ = U₁.toBase ≫ V₀.ι ≫ pullback.snd f b₀
      simp only [Category.assoc, k₁, pullbackLeftPullbackSndIso_inv_fst_snd]
      change t₁ ≫ pullback.snd f b₁ ≫ V₁.toBase = U₁.toBase ≫ V₀.ι ≫ pullback.snd f b₀
      rw [← Category.assoc, ht₁snd]
      simpa only [f₀, Category.assoc] using hcomp₁
  have : Etale U₁.toBase := U₁.etale_toBase
  have ht₁ : Etale t₁ := by
    have : Etale (t₁ ≫ k₁) := by rw [ht₁k₁]; infer_instance
    exact MorphismProperty.of_postcomp @Etale (W' := @Etale) t₁ k₁ hk₁ inferInstance
  have hρb₁ : ρ ≫ b₁ = U₂.scheme.fromSpecStalk U₂.point ≫ U₂.toBase := hρb
  have hgt : g = pullback.fst h₁ ρ ≫ t₁ ≫ pullback.fst f b₁ := by
    rw [ht₁fst]
  have hcomm₁ : (pullback.fst h₁ ρ ≫ t₁ ≫ pullback.fst f b₁) ≫ f =
      pullback.snd h₁ ρ ≫ ρ ≫ b₁ := by
    simp only [Category.assoc, pullback.condition, reassoc_of% ht₁snd, pullback.condition_assoc]
  have hcomm : g ≫ f = q ≫ U₂.scheme.fromSpecStalk U₂.point ≫ U₂.toBase := by
    rw [hgt, hcomm₁, hρb₁]
  let e₃ : pullback f (ρ ≫ b₁) ≅
      pullback f (U₂.scheme.fromSpecStalk U₂.point ≫ U₂.toBase) :=
    pullback.congrHom rfl hρb₁
  have he₃fst : e₃.hom ≫
      pullback.fst f (U₂.scheme.fromSpecStalk U₂.point ≫ U₂.toBase) =
      pullback.fst f (ρ ≫ b₁) := by
    simp only [e₃, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id]
  have he₃snd : e₃.hom ≫
      pullback.snd f (U₂.scheme.fromSpecStalk U₂.point ≫ U₂.toBase) =
      pullback.snd f (ρ ≫ b₁) := by
    simp only [e₃, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
  have hlEtale : Etale (pullback.lift g q hcomm) := by
    have hbase := etale_pullbackLift_baseChange f b₁ ρ h₁ t₁ ht₁snd hcomm₁
    have heq : pullback.lift g q hcomm =
        pullback.lift (pullback.fst h₁ ρ ≫ t₁ ≫ pullback.fst f b₁)
            (pullback.snd h₁ ρ) hcomm₁ ≫ e₃.hom := by
      refine pullback.hom_ext ?_ ?_
      · rw [pullback.lift_fst, Category.assoc, he₃fst, pullback.lift_fst]
        exact hgt
      · rw [pullback.lift_snd, Category.assoc, he₃snd, pullback.lift_snd]
    rw [heq]
    infer_instance
  have : LocallyOfFinitePresentation (h₁ ≫ V₁.toBase) := by
    rw [hcomp₁]
    exact locallyOfFinitePresentation_comp U₁.toBase f₀
  have : LocallyOfFinitePresentation h₁ := locallyOfFinitePresentation_of_comp h₁ V₁.toBase
  have hqfp : FinitePresentation q :=
    FinitePresentation.mk inferInstance inferInstance inferInstance
  let pr : X' ⟶ V₀.toScheme := pullback.fst h₁ ρ ≫ U₁.toBase
  let d : V₀.toScheme ⟶ X := V₀.ι ≫ pullback.fst f b₀
  have hpd : pr ≫ d = g := by simp only [pr, d, g, Category.assoc]
  have hMfp : ((Scheme.Modules.pullback pr).obj F₀).IsFinitePresentation :=
    @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ pr.toLRSHom.toShHom F₀ hfp₀
  have hgfp : ((Scheme.Modules.pullback g).obj F).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation X'.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.pullbackComp pr d).app F ≪≫ (Scheme.Modules.pullbackCongr hpd).app F)
      hMfp
  have hU₀res : IsIso (U₀.toBase.residueFieldMap U₀.point) := (U₀.isElementary_iff).mp hU₀
  have hb₀Res : IsIso (b₀.residueFieldMap
      (IsLocalRing.closedPoint (U₀.scheme.presheaf.stalk U₀.point))) := by
    refine isIso_residueFieldMap_comp
      (U₀.scheme.fromSpecStalk U₀.point) U₀.toBase _
      (isIso_residueFieldMap_of_isPreimmersion (U₀.scheme.fromSpecStalk U₀.point) _) ?_
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hU₀res
  have hfirst : IsIso ((pullback.fst f b₀).residueFieldMap (V₀.ι v₀)) := by
    refine pullback_fst_residueFieldMap_isIso f b₀ (V₀.ι v₀) ?_
    rw [show (pullback.snd f b₀) (V₀.ι v₀) =
      IsLocalRing.closedPoint (U₀.scheme.presheaf.stalk U₀.point) from hclosed₀]
    exact hb₀Res
  have hV₀res : IsIso ((V₀.ι ≫ pullback.fst f b₀).residueFieldMap v₀) :=
    isIso_residueFieldMap_comp V₀.ι (pullback.fst f b₀) v₀
      (isIso_residueFieldMap_of_isPreimmersion V₀.ι v₀) hfirst
  have hU₁res : IsIso (U₁.toBase.residueFieldMap U₁.point) := (U₁.isElementary_iff).mp hU₁
  have hgRes : IsIso (g.residueFieldMap x') := by
    refine isIso_residueFieldMap_comp (pullback.fst h₁ ρ)
      (U₁.toBase ≫ V₀.ι ≫ pullback.fst f b₀) x' hfstRes ?_
    rw [hx'₁]
    refine isIso_residueFieldMap_comp U₁.toBase
      (V₀.ι ≫ pullback.fst f b₀) U₁.point hU₁res ?_
    rw [U₁.map_point]
    exact hV₀res
  let M₁ : U₁.scheme.Modules := (Scheme.Modules.pullback U₁.toBase).obj F₀
  let M₂ : X'.Modules := (Scheme.Modules.pullback (pullback.fst h₁ ρ)).obj M₁
  have hM₂ : M₂ ≅ (Scheme.Modules.pullback g).obj F :=
    (Scheme.Modules.pullbackComp (pullback.fst h₁ ρ) U₁.toBase).app F₀ ≪≫
      (Scheme.Modules.pullbackComp (pullback.fst h₁ ρ ≫ U₁.toBase)
        (V₀.ι ≫ pullback.fst f b₀)).app F ≪≫
      (Scheme.Modules.pullbackCongr (by simp only [g, Category.assoc] :
        (pullback.fst h₁ ρ ≫ U₁.toBase) ≫ (V₀.ι ≫ pullback.fst f b₀) = g)).app F
  refine ⟨U₂, hU₂, X', x', g, q, hgx, hqx, hcomm, hlEtale, hgRes, inferInstance, hqfp, hgfp, ?_⟩
  have : M₁.IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ _ U₁.toBase.toLRSHom.toShHom F₀ hF₀qc
  have hlocal : IsLocalRing (U₂.scheme.presheaf.stalk U₂.point : Type u) :=
    U₂.scheme.toLocallyRingedSpace.isLocalRing U₂.point
  exact free_globalSections_of_iso _ q hM₂
    (free_globalSections_pullback_of_projective _ hlocal h₁ ρ M₁ hProjective₁)

end AlgebraicGeometry

end
