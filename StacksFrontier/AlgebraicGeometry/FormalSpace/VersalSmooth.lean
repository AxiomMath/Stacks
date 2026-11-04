module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.VersalLifting
public import StacksFrontier.AlgebraicGeometry.FormalSpace.VersalSmoothAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.SpecField

/-!
# Stacks 0GI9: a morphism out of a completion is smooth near a point of versality

Let `S` be a locally Noetherian scheme, `V` a scheme locally of finite type over `S`, `Z ⊆ V`
closed, `W` a locally Noetherian formal algebraic space over `S` with `W_red` locally of finite
type over `S`, and `g : V_{/Z} ⟶ W` an adic morphism. If `v ∈ V` is a closed point at which `g` is
versal (Section 07XZ), then after replacing `V` by an open neighbourhood of `v` the morphism `g`
is smooth, in the sense of Bootstrap, Definition 03XZ.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_isOpenImmersion_smooth_of_isVersalAtCompletion`:
  **Stacks 0GI9**.

## Implementation notes

The proof follows the source. Versality at the closed point `v` gives the lifting property of
`g` at `v` for small extensions with residue field finite over `κ(v)`
(`liftsAtCompletion_of_isVersalAtCompletion`, by change of fields and condition (RS) of `W`).
An affine open neighbourhood `Spec R` of `v` reduces to the Noetherian affine case
(`exists_isOpenImmersion_smooth_of_liftsAtCompletion_of_isLocallyNoetherian`), which reduces to
an affine formal target `Spf C₀` by an étale chart and Stacks 0AR4, where the stages
`R^∧/bⁿR^∧` over `C₀/bⁿ` are smooth over a common open neighbourhood of `v` by the key step of
the source (`Algebra.exists_notMem_forall_smoothAt_quotient_pow`); smoothness descends along the
étale chart. The hypothesis that `W_red` is locally of finite type over `S` is part of the
source's statement and is not used by the argument.

## References

* [Stacks Project, Tag 0GI9](https://stacks.math.columbia.edu/tag/0GI9)
* [Stacks Project, Tag 07XZ](https://stacks.math.columbia.edu/tag/07XZ)
* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [-instance] CategoryTheory.catToReflQuiver

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- At a closed point `v` of a scheme `U` locally of finite type over `S`, the morphism
`Spec κ(v) ⟶ S` is of finite type and `κ(v)` is finite over the local ring of `S` at the image
of `v` (Tag 01TA). -/
theorem finite_stalkClosedPointTo_of_isClosed (U : Over S)
    [AlgebraicGeometry.LocallyOfFiniteType U.hom] (v : U.left) (hvc : IsClosed ({v} : Set U.left)) :
    (Scheme.stalkClosedPointTo (Deformation.Artin.residueFieldBasePoint U v)).hom.Finite ∧
      AlgebraicGeometry.LocallyOfFiniteType (U.left.fromSpecResidueField v ≫ U.hom) ∧
      QuasiCompact (U.left.fromSpecResidueField v ≫ U.hom) := by
  have : AlgebraicGeometry.IsClosedImmersion (U.left.fromSpecResidueField v) :=
    isClosed_singleton_iff_isClosedImmersion.mp hvc
  let f := U.left.fromSpecResidueField v ≫ U.hom
  have hlft : AlgebraicGeometry.LocallyOfFiniteType f :=
    MorphismProperty.comp_mem (W := @AlgebraicGeometry.LocallyOfFiniteType) _ _ inferInstance
      inferInstance
  have htfae := finiteType_specField_tfae f
  obtain ⟨_, _, _, _, _, hfin⟩ := (htfae.out 2 4).mp hlft
  refine ⟨?_, (htfae.out 1 2).mpr hlft⟩
  have hres := @Scheme.residue_descResidueField (U.left.residueField v) _ S _
    (Scheme.stalkClosedPointTo f) (Scheme.isLocalHom_stalkClosedPointTo f)
  change (Scheme.stalkClosedPointTo f).hom.Finite
  rw [← hres, CommRingCat.hom_comp]
  exact RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ IsLocalRing.residue_surjective)

/-- The completion of a composite is the composite of the completions, up to the identification
of the two inverse images of the set of points. -/
theorem exists_iso_completionSheafMap_yoneda_comp {X₁ X₂ X₃ : BigFppfOver B S hS} (a : X₁ ⟶ X₂)
    (b : X₂ ⟶ X₃) (T : Set (Space.points B S hS (yoneda.obj X₃))) :
    ∃ e : Space.completionSheaf B S hS (yoneda.obj X₁)
        (Space.pointsMap B S hS _ (yoneda.map (a ≫ b)) ⁻¹' T) ≅
      Space.completionSheaf B S hS (yoneda.obj X₁) (Space.pointsMap B S hS _ (yoneda.map a) ⁻¹'
        (Space.pointsMap B S hS _ (yoneda.map b) ⁻¹' T)),
      Space.completionSheafMap B S hS (yoneda.map (a ≫ b)) T =
        e.hom ≫ Space.completionSheafMap B S hS (yoneda.map a) _ ≫
          Space.completionSheafMap B S hS (yoneda.map b) T := by
  have hab : yoneda.map (a ≫ b) = yoneda.map a ≫ yoneda.map b := Functor.map_comp _ _ _
  have hs : Space.pointsMap B S hS _ (yoneda.map (a ≫ b)) ⁻¹' T =
      Space.pointsMap B S hS _ (yoneda.map a) ⁻¹'
        (Space.pointsMap B S hS _ (yoneda.map b) ⁻¹' T) := by
    rw [Space.preimage_pointsMap_preimage_pointsMap, hab]
  refine ⟨eqToIso (congrArg (Space.completionSheaf B S hS (yoneda.obj X₁)) hs), ?_⟩
  rw [Space.completionSheafMap_comp_completionSheafMap,
    ← Space.eqToHom_comp_completionSheafMap hab T]
  simp only [eqToIso.hom, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- A point `v` of a scheme `V` locally of finite type over a locally Noetherian `S` lies in the
image of an open immersion from the spectrum of a Noetherian ring locally of finite type over
`S`. -/
theorem exists_affineOver_isOpenImmersion_of_locallyOfFiniteType
    [AlgebraicGeometry.IsLocallyNoetherian S] (V : BigFppfOver B S hS)
    (hV : AlgebraicGeometry.LocallyOfFiniteType ((Over.post B.inclusion).obj V : Over S).hom)
    (v : ((Over.post B.inclusion).obj V : Over S).left) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsNoetherianRing R) (hR : B.Contains (Spec (.of R)))
      (s : Spec (.of R) ⟶ S) (k : affineOver B S hS hR s ⟶ V)
      (u : (BigFppfOver.toScheme B S hS).obj (affineOver B S hS hR s)),
      IsOpenImmersion ((BigFppfOver.toScheme B S hS).map k) ∧
        (BigFppfOver.toScheme B S hS).map k u = v ∧ AlgebraicGeometry.LocallyOfFiniteType s := by
  let Sch := BigFppfOver.toScheme B S hS
  let U₀ := (Over.post B.inclusion).obj V
  have : AlgebraicGeometry.IsLocallyNoetherian (B.inclusion.obj (B.obj hS)) :=
    inferInstanceAs (AlgebraicGeometry.IsLocallyNoetherian S)
  have : AlgebraicGeometry.IsLocallyNoetherian U₀.left :=
    LocallyOfFiniteType.isLocallyNoetherian U₀.hom
  obtain ⟨_, ⟨O, hO, rfl⟩, hvO, -⟩ :=
    U₀.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ v) isOpen_univ
  let O' : U₀.left.Opens := O
  let Y := BigFppfOver.openSubObj B S hS V O
  let jO : Y ⟶ V := BigFppfOver.openSubHom B S hS V O
  have : IsAffine (Sch.obj Y) := hO
  have : AlgebraicGeometry.IsLocallyNoetherian (Sch.obj Y) :=
    inferInstanceAs (AlgebraicGeometry.IsLocallyNoetherian O'.toScheme)
  have : AlgebraicGeometry.IsNoetherian (Sch.obj Y) := {}
  obtain ⟨R, _, _, hR, s, ιY, hιY⟩ := Space.exists_isIso_affineOver Y
  let k : affineOver B S hS hR s ⟶ V := ιY ≫ jO
  have : IsOpenImmersion (Sch.map jO) := inferInstanceAs (IsOpenImmersion O'.ι)
  have hk' : IsOpenImmersion (Sch.map k) := by
    change IsOpenImmersion (Sch.map (ιY ≫ jO))
    rw [Functor.map_comp]
    infer_instance
  have hinvx : ∀ z, Sch.map ιY ((inv (Sch.map ιY)) z) = z := by
    intro z
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  let vY : Sch.obj Y := ⟨v, hvO⟩
  let u : Sch.obj (affineOver B S hS hR s) := (inv (Sch.map ιY)) vY
  have hku : Sch.map k u = v := by
    change Sch.map jO (Sch.map ιY ((inv (Sch.map ιY)) vY)) = v
    rw [hinvx]
    rfl
  have hsft : AlgebraicGeometry.LocallyOfFiniteType s := by
    have hs : Sch.map ιY ≫ O'.ι ≫ U₀.hom = s :=
      (congrArg B.inclusion.map (Over.w ιY) :
        Sch.map ιY ≫ ((Over.post B.inclusion).obj Y : Over S).hom = s)
    rw [← hs]
    exact MorphismProperty.comp_mem (W := @AlgebraicGeometry.LocallyOfFiniteType) _ _
      (inferInstance : AlgebraicGeometry.LocallyOfFiniteType (Sch.map ιY))
      (MorphismProperty.comp_mem (W := @AlgebraicGeometry.LocallyOfFiniteType) _ _
        (inferInstance : AlgebraicGeometry.LocallyOfFiniteType O'.ι) hV)
  exact ⟨R, inferInstance, inferInstance, hR, s, k, u, hk', hku, hsft⟩

/-- **Stacks 0GI9.** Let `S` be a locally Noetherian scheme, `V` a scheme locally of finite type
over `S`, `Z ⊆ |V|` closed, `W` a locally Noetherian formal algebraic space over `S` with `W_red`
locally of finite type over `S`, and `g : V_{/Z} ⟶ W` an adic morphism. If `v ∈ V` is a closed
point at which `g` is versal (Section 07XZ), then there is an open neighbourhood `U ⊆ V` of `v`
such that the restriction `U_{/Z} ⟶ W` of `g` is smooth in the sense of Bootstrap, Definition
03XZ. -/
@[stacks 0GI9 "an open neighbourhood `U` of the closed point `v` with `U_{/Z} ⟶ W` smooth \
in the sense of Bootstrap, Definition 03XZ"]
theorem exists_isOpenImmersion_smooth_of_isVersalAtCompletion
    [AlgebraicGeometry.IsLocallyNoetherian S] (V : BigFppfOver B S hS)
    (hV : AlgebraicGeometry.LocallyOfFiniteType ((Over.post B.inclusion).obj V : Over S).hom)
    (Z : Set (Space.points B S hS (yoneda.obj V))) (hZ : IsClosed Z)
    (W : FppfSheaf B S hS) (hW : IsLocallyNoetherian B S hS W)
    (Wred : FppfSheaf B S hS) (ι : Wred ⟶ W) (_hι : IsReduction B S hS W Wred ι)
    (_hWred : Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS (terminal.from Wred.obj))
    (g : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ W) (hg : IsAdicMorphism B S hS g)
    (v : ((Over.post B.inclusion).obj V : Over S).left) (hvc : IsClosed ({v} : Set _))
    (hvZ : v ∈ Space.pointsToScheme B S hS V '' Z)
    (hvers : IsVersalAtCompletion B S hS V Z W g v) :
    ∃ (U : BigFppfOver B S hS) (i : U ⟶ V),
      IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i) ∧
      v ∈ Set.range ((BigFppfOver.toScheme B S hS).map i) ∧
      ∃ hrep, Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ a ↦ Space.IsSmoothULift.{u + 1} B S hS a.hom)
        (Space.completionSheafMap B S hS (yoneda.map i) Z ≫ g).hom hrep := by
  classical
  let Sch := BigFppfOver.toScheme B S hS
  let U₀ := (Over.post B.inclusion).obj V
  -- the lifting property at `v`
  obtain ⟨hk, hvft⟩ := finite_stalkClosedPointTo_of_isClosed S U₀ v hvc
  have hlift : LiftsAtCompletion B S hS V Z W g v :=
    liftsAtCompletion_of_isVersalAtCompletion B S hS V Z W hW.1 g v hvZ hk hvft hvers
  obtain ⟨R, _, _, hR, s, k, u, hk', hku, _⟩ :=
    exists_affineOver_isOpenImmersion_of_locallyOfFiniteType B S hS V hV v
  -- the restriction `G` of `g` to `Spec R`, with the lifting property at `u`
  let T := Space.pointsMap B S hS _ (yoneda.map k) ⁻¹' Z
  let G := Space.completionSheafMap B S hS (yoneda.map k) Z ≫ g
  have hG : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS G.hom :=
    Space.isRepresentableByAlgebraicSpacesULift_comp B S hS _ _
      (Space.isRepresentableByAlgebraicSpacesULift_completionMap B S hS
        (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _) (yoneda.map k) Z) hg
  have hliftG : LiftsAtCompletion B S hS (affineOver B S hS hR s) T W G u :=
    liftsAtCompletion_comp_completionSheafMap B S hS k Z W g u (by rwa [hku])
  obtain ⟨q, hq⟩ := Space.surjective_pointsToScheme B S hS (affineOver B S hS hR s) u
  have hqT : q ∈ T := by
    obtain ⟨z₀, hz₀, hz₀v⟩ := hvZ
    change Space.pointsMap B S hS _ (yoneda.map k) q ∈ Z
    have h : Space.pointsToScheme B S hS V (Space.pointsMap B S hS _ (yoneda.map k) q) =
        Space.pointsToScheme B S hS V z₀ := by
      rw [Space.pointsToScheme_pointsMap_yoneda, hq, hku, hz₀v]
    rwa [Space.injective_pointsToScheme B S hS V h]
  -- the Noetherian affine case
  obtain ⟨U, i, hi, ⟨x, hx⟩, hrep, hsm⟩ :=
    exists_isOpenImmersion_smooth_of_liftsAtCompletion_of_isLocallyNoetherian B S hS hR s T
      (hZ.preimage (Space.continuous_pointsMap B S hS _)) hW
      G hG q hqT (by rwa [hq])
  obtain ⟨e, he⟩ := exists_iso_completionSheafMap_yoneda_comp B S hS i k Z
  obtain ⟨hrep', hsm'⟩ := exists_hasPropertyULift_isSmoothULift_iso_comp B S hS e _ hrep hsm
  have heq : e.hom ≫ Space.completionSheafMap B S hS (yoneda.map i) T ≫ G =
      Space.completionSheafMap B S hS (yoneda.map (i ≫ k)) Z ≫ g := by
    rw [he]
    simp only [G, Category.assoc]
    rfl
  refine ⟨U, i ≫ k, ?_, ⟨x, ?_⟩, ?_⟩
  · rw [Functor.map_comp]
    infer_instance
  · change Sch.map k (Sch.map i x) = v
    rwa [hx, hq]
  · rw [← heq]
    exact ⟨hrep', hsm'⟩

end AlgebraicGeometry.FormalSpace
