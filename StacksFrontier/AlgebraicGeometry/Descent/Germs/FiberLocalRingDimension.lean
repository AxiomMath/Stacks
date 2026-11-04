module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.Local
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleStalkDimension

/-!
# The dimension of the local ring of a fibre is étale local

The dimension of the local ring of the scheme-theoretic fibre of a morphism of germs at its
distinguished point is unchanged by étale changes of the source and the target germ.

## Main definitions

* `AlgebraicGeometry.HasFiberLocalRingDimension` says that the local ring of the fibre of a
  morphism of germs at its distinguished point has a given dimension.

## Main results

* `AlgebraicGeometry.fiberLocalRingDimension_isEtaleLocalOnSourceAndTarget` states that this
  property is étale local on the source and the target.
* `AlgebraicGeometry.fiberMap_fiberι` identifies the composite of the morphism of fibres in a
  commutative square with the embedding of the target fibre.
* `AlgebraicGeometry.ringKrullDim_stalk_fiber_eq_of_etale_square`: in a commutative square of
  schemes with étale vertical arrows, the two horizontal arrows have fibres whose local rings at
  corresponding points have the same Krull dimension.

## Implementation notes

A representative of a morphism of germs is a morphism of schemes defined near the
distinguished source point. Its scheme-theoretic fibre over the image point carries a canonical
point `AlgebraicGeometry.Scheme.Hom.asFiber`, and the invariant is the Krull dimension of the
structure-sheaf stalk there. The property of a germ is the existence of a representative with
that dimension, so no representative has to be chosen. The dimension parameter lies in `ℕ∞`,
excluding the bottom value that `ringKrullDim` also admits for a zero ring.

## References

* [Stacks Project, Tag 04NJ](https://stacks.math.columbia.edu/tag/04NJ)
-/

@[expose] public section

universe u


namespace AlgebraicGeometry

open CategoryTheory
open MorphismOfGerms

private noncomputable def representativeFiberKrullDimensionAt
    {X Y : GermOfScheme.{u}} (r : MorphismOfGerms.Representative X Y)
    (x : r.source.toScheme) : WithBot ℕ∞ :=
  ringKrullDim ((r.hom.fiber (r.hom x)).presheaf.stalk (r.hom.asFiber x))

private noncomputable def schemeFiberDimensionAt {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) : WithBot ℕ∞ :=
  ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x))

private noncomputable def representativeFiberKrullDimension
    {X Y : GermOfScheme.{u}} (r : MorphismOfGerms.Representative X Y) : WithBot ℕ∞ :=
  representativeFiberKrullDimensionAt r ⟨X.point, r.mem_source⟩

private theorem fiberι_cast_point {X Y : Scheme.{u}} (f : X ⟶ Y)
    {y₁ y₂ : Y} (e : y₁ = y₂) (p : f.fiber y₁) :
    f.fiberι y₂ (e ▸ p) = f.fiberι y₁ p := by
  cases e
  rfl

private theorem fiberStalkDim_cast {X Y : Scheme.{u}} (f : X ⟶ Y)
    {y₁ y₂ : Y} (e : y₁ = y₂) (p : f.fiber y₁) :
    ringKrullDim ((f.fiber y₂).presheaf.stalk (e ▸ p)) =
      ringKrullDim ((f.fiber y₁).presheaf.stalk p) := by
  cases e
  rfl

/-- The morphism of fibres induced by a commutative square, followed by the embedding of the
target fibre, is the embedding of the source fibre followed by the left vertical arrow. -/
lemma fiberMap_fiberι {U' U V' V : Scheme.{u}}
    (f' : U' ⟶ V') (g' : U' ⟶ U) (g : V' ⟶ V) (f : U ⟶ V)
    (h : g' ≫ f = f' ≫ g) (v' : V') :
    fiberMap f' g' g f h v' ≫ f.fiberι (g v') = f'.fiberι v' ≫ g' :=
  Limits.pullback.lift_fst _ _ _

/-- In a commutative square of schemes whose vertical arrows are étale, the local ring of the
fibre of the top arrow at a point of its source has the same Krull dimension as the local ring
of the fibre of the bottom arrow at the image of that point. -/
theorem ringKrullDim_stalk_fiber_eq_of_etale_square
    {U' U V' V : Scheme.{u}}
    (f' : U' ⟶ V') (g' : U' ⟶ U) (g : V' ⟶ V) (f : U ⟶ V)
    [Etale g'] [Etale g] (h : g' ≫ f = f' ≫ g) (x' : U') :
    ringKrullDim ((f'.fiber (f' x')).presheaf.stalk (f'.asFiber x')) =
      ringKrullDim ((f.fiber (f (g' x'))).presheaf.stalk (f.asFiber (g' x'))) := by
  have hg : g (f' x') = f (g' x') := by
    simpa [Scheme.Hom.comp_apply] using (congrArg (fun q : U' ⟶ V => q x') h).symm
  let fm := fiberMap f' g' g f h (f' x')
  have : Etale fm := etale_fiberMap f' g' g f h (f' x')
  have hp : hg ▸ fm (f'.asFiber x') = f.asFiber (g' x') := by
    apply (f.fiberι (f (g' x'))).isEmbedding.injective
    calc
      f.fiberι (f (g' x')) (hg ▸ fm (f'.asFiber x')) =
          f.fiberι (g (f' x')) (fm (f'.asFiber x')) := fiberι_cast_point f hg _
      _ = g' x' := by
        simpa using congrArg (fun q => q (f'.asFiber x')) (fiberMap_fiberι f' g' g f h (f' x'))
      _ = f.fiberι (f (g' x')) (f.asFiber (g' x')) := by simp
  rw [ringKrullDim_stalk_eq_of_etale fm (f'.asFiber x'), ← fiberStalkDim_cast f hg, hp]

/-- Restricting a representative to a smaller open neighbourhood of the point does not change
the dimension of the local ring of its fibre. -/
private theorem restrictRepresentative_fiberKrullDimension
    {X Y : GermOfScheme.{u}} (f : MorphismOfGerms.Representative X Y)
    (W : X.scheme.Opens) (hxW : X.point ∈ W) (hWf : W ≤ f.source) :
    representativeFiberKrullDimension (restrictRepresentative f W hxW hWf) =
      representativeFiberKrullDimension f := by
  have hpoint : X.scheme.homOfLE hWf ⟨X.point, hxW⟩ = ⟨X.point, f.mem_source⟩ :=
    Subtype.ext (by simp)
  have : Etale (X.scheme.homOfLE hWf) :=
    HasRingHomProperty.of_isOpenImmersion RingHom.Etale.containsIdentities
  have : Etale (𝟙 Y.scheme) := inferInstance
  have hd := @ringKrullDim_stalk_fiber_eq_of_etale_square _ _ _ _
    (restrictRepresentative f W hxW hWf).hom (X.scheme.homOfLE hWf) (𝟙 Y.scheme) f.hom
    (inferInstance : Etale (X.scheme.homOfLE hWf)) (inferInstance : Etale (𝟙 Y.scheme))
    (by rfl) ⟨X.point, hxW⟩
  unfold representativeFiberKrullDimension
  rw [← hpoint]
  exact hd

private theorem representativeFiberKrullDimension_eq_of_agreeNear
    {X Y : GermOfScheme.{u}} (f g : MorphismOfGerms.Representative X Y)
    (h : f.AgreeNear g) :
    representativeFiberKrullDimension f = representativeFiberKrullDimension g := by
  obtain ⟨W, hxW, hWf, hWg, heq⟩ := h
  let fW := restrictRepresentative f W hxW hWf
  let gW := restrictRepresentative g W hxW hWg
  have hfg : fW = gW := representative_ext_of_source_hom (f := fW) (g := gW) rfl
    (by simpa [fW, gW, restrictRepresentative, Scheme.isoOfEq_rfl] using heq)
  rw [← restrictRepresentative_fiberKrullDimension f W hxW hWf,
    ← restrictRepresentative_fiberKrullDimension g W hxW hWg]
  exact congrArg _ hfg

private theorem representativeFiberKrullDimension_comp_source
    {X Y Z : GermOfScheme.{u}}
    (a : MorphismOfGerms.Representative X Y)
    (r : MorphismOfGerms.Representative Y Z) [Etale a.hom] :
    representativeFiberKrullDimension (compRepresentative a r) =
      representativeFiberKrullDimension r := by
  let c := compRepresentative a r
  let k := (a.source.ι.isoImage (a.hom ⁻¹ᵁ r.source)).inv ≫ (a.hom ∣_ r.source)
  have hk : k ≫ r.hom = c.hom := rfl
  have hp : k ⟨X.point, c.mem_source⟩ = ⟨Y.point, r.mem_source⟩ := by
    apply Subtype.ext
    show r.source.ι ((a.hom ∣_ r.source)
      ((a.source.ι.isoImage (a.hom ⁻¹ᵁ r.source)).inv ⟨X.point, _⟩)) = Y.point
    rw [← a.map_point, ← Scheme.Hom.comp_apply, morphismRestrict_ι]
    show (((a.source.ι.isoImage _).inv ≫ (a.hom ⁻¹ᵁ r.source).ι ≫ a.hom)
      ⟨X.point, c.mem_source⟩) = a.hom ⟨X.point, a.mem_source⟩
    rw [← Category.assoc, Scheme.Opens.isoImage_ι_inv_ι]
    show a.hom (X.scheme.homOfLE _ ⟨X.point, c.mem_source⟩) = _
    congr 1
    exact Subtype.ext (Scheme.homOfLE_apply _ ⟨X.point, c.mem_source⟩)
  have : Etale k := by dsimp [k]; infer_instance
  have : Etale (𝟙 Z.scheme) := inferInstance
  let x : c.source.toScheme := ⟨X.point, c.mem_source⟩
  have hd := @ringKrullDim_stalk_fiber_eq_of_etale_square _ _ _ _ c.hom k (𝟙 Z.scheme) r.hom
    (inferInstance : Etale k) (inferInstance : Etale (𝟙 Z.scheme)) hk x
  change representativeFiberKrullDimensionAt c x =
    representativeFiberKrullDimensionAt r (k x) at hd
  have hp' : k x = ⟨Y.point, r.mem_source⟩ := hp
  rw [hp'] at hd
  exact hd

private theorem representativeFiberKrullDimension_comp_target
    {X Y Z : GermOfScheme.{u}}
    (r : MorphismOfGerms.Representative X Y)
    (b : MorphismOfGerms.Representative Y Z) [Etale b.hom] :
    representativeFiberKrullDimension (compRepresentative r b) =
      representativeFiberKrullDimension r := by
  let c := compRepresentative r b
  let W := r.hom ⁻¹ᵁ b.source
  let i := (r.source.ι.isoImage W).inv ≫ W.ι
  let j := (r.source.ι.isoImage W).inv ≫ (r.hom ∣_ b.source)
  have hsquare : i ≫ r.hom = j ≫ b.source.ι := by
    calc
      i ≫ r.hom = (r.source.ι.isoImage W).inv ≫ W.ι ≫ r.hom := by
        simp [i]
      _ = (r.source.ι.isoImage W).inv ≫ ((r.hom ∣_ b.source) ≫ b.source.ι) := by
        rw [morphismRestrict_ι]
      _ = j ≫ b.source.ι := by simp [j, Category.assoc]
  have hcomp : j ≫ b.hom = c.hom := by
    dsimp [j, c, W, compRepresentative]
    rfl
  let x : c.source.toScheme := ⟨X.point, c.mem_source⟩
  have hinc : i ≫ r.source.ι = c.source.ι := by
    dsimp [i, c, W, compRepresentative]
    rw [Scheme.Opens.isoImage_ι_inv_ι]
    simp
  have hi : i x = ⟨X.point, r.mem_source⟩ := by
    apply Subtype.ext
    show (i ≫ r.source.ι) x = X.point
    rw [hinc]
    show c.source.ι x = X.point
    rw [Scheme.Opens.ι_apply]
  have : Etale i := by dsimp [i]; infer_instance
  have : Etale (𝟙 c.source.toScheme) := inferInstance
  have htarget : schemeFiberDimensionAt j x = schemeFiberDimensionAt c.hom x := by
    have hd := @ringKrullDim_stalk_fiber_eq_of_etale_square _ _ _ _ j (𝟙 c.source.toScheme)
      b.hom c.hom (inferInstance : Etale (𝟙 c.source.toScheme))
      (inferInstance : Etale b.hom) hcomp.symm x
    change schemeFiberDimensionAt j x =
      schemeFiberDimensionAt c.hom ((𝟙 c.source.toScheme) x) at hd
    have hxid : (𝟙 c.source.toScheme) x = x := by simp
    simpa only [hxid] using hd
  have hsource : schemeFiberDimensionAt j x = schemeFiberDimensionAt r.hom (i x) := by
    simpa [schemeFiberDimensionAt] using
      @ringKrullDim_stalk_fiber_eq_of_etale_square _ _ _ _ j i b.source.ι r.hom
        (inferInstance : Etale i) (inferInstance : Etale b.source.ι) hsquare x
  show schemeFiberDimensionAt c.hom x =
    schemeFiberDimensionAt r.hom ⟨X.point, r.mem_source⟩
  rw [← hi]
  exact htarget.symm.trans hsource

/-- The local ring of the fibre of a morphism of germs at its distinguished
point has Krull dimension `d`. -/
public abbrev HasFiberLocalRingDimension (d : ℕ∞)
    {X S : GermOfScheme.{u}} (f : MorphismOfGerms X S) : Prop :=
  ∃ g : MorphismOfGerms.Representative X S,
    MorphismOfGerms.mk g = f ∧
      ringKrullDim
          ((g.hom.fiber (g.hom ⟨X.point, g.mem_source⟩)).presheaf.stalk
            (g.hom.asFiber ⟨X.point, g.mem_source⟩)) = (d : WithBot ℕ∞)

private theorem hasFiberLocalRingDimension_iff_representation
    (d : ℕ∞) {X Y : GermOfScheme.{u}} (f : MorphismOfGerms X Y)
    (r : MorphismOfGerms.Representative X Y)
    (hr : MorphismOfGerms.mk r = f) :
    HasFiberLocalRingDimension d f ↔
      representativeFiberKrullDimension r = (d : WithBot ℕ∞) := by
  refine ⟨fun ⟨s, hs, hsd⟩ => ?_, fun h => ⟨r, hr, h⟩⟩
  exact (representativeFiberKrullDimension_eq_of_agreeNear s r
    (MorphismOfGerms.mk_eq_mk_iff.mp (hs.trans hr.symm))).symm.trans hsd

private theorem hasFiberLocalRingDimension_comp_source
    (d : ℕ∞) {X Y Z : GermOfScheme.{u}}
    (a : MorphismOfGerms X Y) (h : MorphismOfGerms Y Z)
    (ha : MorphismOfGerms.IsEtale a) :
    HasFiberLocalRingDimension d (comp a h) ↔
      HasFiberLocalRingDimension d h := by
  obtain ⟨aR, haR, haEtale⟩ := ha
  obtain ⟨r, hr⟩ := MorphismOfGerms.exists_rep h
  let c := compRepresentative aR r
  have hc : MorphismOfGerms.mk c = comp a h := by
    rw [← haR, ← hr]
    exact comp_mk aR r
  have : Etale aR.hom := haEtale
  rw [hasFiberLocalRingDimension_iff_representation d (comp a h) c hc,
    hasFiberLocalRingDimension_iff_representation d h r hr,
    representativeFiberKrullDimension_comp_source aR r]

private theorem hasFiberLocalRingDimension_comp_target
    (d : ℕ∞) {X Y Z : GermOfScheme.{u}}
    (h : MorphismOfGerms X Y) (b : MorphismOfGerms Y Z)
    (hb : MorphismOfGerms.IsEtale b) :
    HasFiberLocalRingDimension d (comp h b) ↔
      HasFiberLocalRingDimension d h := by
  obtain ⟨bR, hbR, hbEtale⟩ := hb
  obtain ⟨r, hr⟩ := MorphismOfGerms.exists_rep h
  let c := compRepresentative r bR
  have hc : MorphismOfGerms.mk c = comp h b := by
    rw [← hr, ← hbR]
    exact comp_mk r bR
  have : Etale bR.hom := hbEtale
  rw [hasFiberLocalRingDimension_iff_representation d (comp h b) c hc,
    hasFiberLocalRingDimension_iff_representation d h r hr,
    representativeFiberKrullDimension_comp_target r bR]

/-- The dimension of the local ring of the fibre of a morphism of germs at its distinguished
point is étale local on the source and target germs. -/
@[stacks 04NJ]
public theorem fiberLocalRingDimension_isEtaleLocalOnSourceAndTarget (d : ℕ∞) :
    MorphismOfGerms.IsEtaleLocalOnSourceAndTarget
      (@HasFiberLocalRingDimension.{u} d) := by
  refine ⟨?_⟩
  intro U' U V' V a b h' h ha hb hsq
  have hsource := hasFiberLocalRingDimension_comp_source d a h ha
  rw [← hsq] at hsource
  exact hsource.symm.trans (hasFiberLocalRingDimension_comp_target d h' b hb)

end AlgebraicGeometry
