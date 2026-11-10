module

public import StacksFrontier.AlgebraicGeometry.Quot.ContractionUniquenessComplete
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalCurve.Algebraization
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalNeighbourhood.Flatness
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.FlatLocusOpenness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.LocallyConstant
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.Thickenings.Infinitesimal
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme

/-!
# Extending a contraction of the closed fibre over a complete Noetherian local ring

Let `Λ` be a complete Noetherian local ring with residue field `κ` and closed point
`s : Spec κ ⟶ Spec Λ`, let `fX : X ⟶ Spec Λ` be proper and flat, and let `h₀ : Xₛ ⟶ Y₀` be a
morphism over `κ` to a proper scheme `Y₀` of dimension at most one with `𝒪_{Y₀} ≅ h₀,*𝒪_{Xₛ}` and
`R¹h₀,*𝒪_{Xₛ} = 0`. Then there are a proper flat projective `fY : Y ⟶ Spec Λ`, all of whose fibres
have dimension at most one, and a morphism `h : X ⟶ Y` over `Spec Λ` whose closed fibre is `h₀`:
`Y₀` is the closed fibre of `Y` and `h` restricts to `h₀` on it.

This is the case of a complete Noetherian local base in the proof of [Stacks, Tag 0E7C], proved as
the source proves it:

* the truncations `Xₙ = X ×_Λ Λ/𝔪ⁿ⁺¹` are deformations of `Xₛ`; by [Stacks, Tag 0E3X] each is the
  source of a deformation `Xₙ ⟶ Yₙ` of `h₀` (the construction behind essential surjectivity,
  `Deformation.Examples.exists_pushforwardTarget_isPullback_of_specialFibre`), and fullness of the
  forgetful functor lifts the transition maps `Xₙ ⟶ Xₙ₊₁` to transition maps `Yₙ ⟶ Yₙ₊₁` with
  cartesian squares;
* the formal curve `(Yₙ)` is algebraized by a projective `Y ⟶ Spec Λ` ([Stacks, Tag 0E7R], scheme
  form `Stacks.FormalCurve.exists_isProjectiveMorphism_of_topologicalKrullDim_le_one`); it is
  flat because all its truncations are ([Stacks, Tag 0D4G]), and its fibres have dimension at
  most one because the closed one has ([Stacks, Tag 0D4J]);
* Grothendieck's algebraization of morphisms ([Stacks, Tag 0A42]) gives `h : X ⟶ Y` inducing the
  morphisms `Xₙ ⟶ Yₙ`.

## Main results

* `AlgebraicGeometry.EtaleLocalContraction.exists_contraction_of_isAdicComplete`: the statement
  above.

## References

* [Stacks Project, Tag 0E7C](https://stacks.math.columbia.edu/tag/0E7C)
* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
* [Stacks Project, Tag 0E7R](https://stacks.math.columbia.edu/tag/0E7R)
* [Stacks Project, Tag 0A42](https://stacks.math.columbia.edu/tag/0A42)
* [Stacks Project, Tag 0D4G](https://stacks.math.columbia.edu/tag/0D4G)
* [Stacks Project, Tag 0D4J](https://stacks.math.columbia.edu/tag/0D4J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Deformation Deformation.Examples IsLocalRing

universe u

namespace AlgebraicGeometry

namespace EtaleLocalContraction

open ContractionUniquenessComplete

/-! ### Flatness and fibre dimension of an algebraized family -/

section Algebraized

private theorem forall_of_isOpen_of_closedFibre {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [UniversallyClosed f]
    (P : X → Prop) (hP : IsOpen {x | P x})
    (hfiber : ∀ x, f x = IsLocalRing.closedPoint R → P x) : ∀ x, P x := by
  intro x
  by_contra hx
  obtain ⟨y, hy, hfy⟩ := (specializes_closedPoint (f x)).mem_closed
    (f.isClosedMap _ hP.isClosed_compl) ⟨x, hx, rfl⟩
  exact hy (hfiber y hfy)

private theorem flat_pullback_comp {X S T U : Scheme.{u}} (f : X ⟶ S)
    (g : T ⟶ S) (h : U ⟶ T) [Flat (pullback.snd f g)] :
    Flat (pullback.snd f (h ≫ g)) :=
  MorphismProperty.of_isPullback (P := @Flat)
    ((IsPullback.of_hasPullback f (h ≫ g)).of_right' (IsPullback.of_hasPullback f g)) inferInstance

private theorem comap_pow_equiv {R T : Type u} [CommRing R] [CommRing T]
    (e : R ≃+* T) (I : Ideal T) (n : ℕ) :
    (I ^ n).comap e = (I.comap e) ^ n := by
  have h := Ideal.map_pow (e.symm : T →+* R) I n
  rwa [Ideal.map_comap_of_equiv, Ideal.map_comap_of_equiv] at h

private theorem ker_adicThickeningι (R : Type u) [CommRing R] (I : Ideal R) (n : ℕ) :
    (adicThickeningι R I n).ker =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker ^ (n + 1) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
  rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply]
  change RingHom.ker (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))).appTop.hom =
    RingHom.ker (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop.hom ^ (n + 1)
  rw [Stacks.Smooth.ker_specMap_appTop, Stacks.Smooth.ker_specMap_appTop]
  change (RingHom.ker (Ideal.Quotient.mk (I ^ (n + 1)))).comap _ =
    ((RingHom.ker (Ideal.Quotient.mk I)).comap _) ^ (n + 1)
  rw [Ideal.mk_ker, Ideal.mk_ker]
  exact comap_pow_equiv (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv _ _

private theorem ker_pow_le_nthOrderToBase {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] (n : ℕ) :
    i.ker ^ (n + 1) ≤ (Stacks.Thickenings.nthOrderToBase i n).ker := by
  have hi : i.coborderRange = ⊤ := by
    ext x
    change x ∈ coborder (Set.range i) ↔ x ∈ (Set.univ : Set Y)
    rw [i.isClosedEmbedding.isClosed_range.coborder_eq]
  have : IsIso i.coborderRange.ι := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    simpa using hi
  rw [Stacks.Thickenings.nthOrderToBase, Scheme.Hom.ker_comp,
    Scheme.IdealSheafData.ker_subschemeι]
  conv_lhs => rw [← i.liftCoborder_ι, Scheme.Hom.ker_comp]
  apply Scheme.IdealSheafData.le_def.mpr
  intro U
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Scheme.IdealSheafData.ideal_map _ _ U (U.2.preimage _)]
  exact Ideal.le_comap_pow _ _

private theorem flat_nthOrder_of_flat_adic
    (R : CommRingCat.{u}) (I : Ideal R) {X : Scheme.{u}} (f : X ⟶ Spec R)
    (n : ℕ) (hf : Flat (pullback.snd f (adicThickeningι R I n))) :
    Flat (pullback.snd f (Stacks.Thickenings.nthOrderToBase
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) n)) := by
  have : IsClosedImmersion (adicThickeningι R I n) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  let k := adicThickeningι R I n
  let g := Stacks.Thickenings.nthOrderToBase
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) n
  have hker : k.ker ≤ g.ker := by
    rw [ker_adicThickeningι]
    exact ker_pow_le_nthOrderToBase _ _
  let l := IsClosedImmersion.lift k g hker
  have hl : l ≫ k = g := IsClosedImmersion.lift_fac _ _ _
  have : Flat (pullback.snd f k) := hf
  have H := flat_pullback_comp f k l
  rwa [hl] at H

private theorem flat_of_flat_infinitesimalNeighborhoods
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {X Z : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of R)) [UniversallyClosed f] [LocallyOfFiniteType f]
    (i : Z ⟶ Spec (.of R)) [IsClosedImmersion i]
    (hi : IsLocalRing.closedPoint R ∈ Set.range i)
    (hflat : ∀ n : ℕ, Flat (pullback.snd f (Stacks.Thickenings.nthOrderToBase i n))) :
    Flat f := by
  apply Flat.of_stalkMap
  apply forall_of_isOpen_of_closedFibre f
    (fun x => IsFlatAt f.toLRSHom.toShHom x)
    (isOpen_setOf_isFlatAt_of_isLocallyNoetherian f)
  intro x hx
  exact isFlatAt_of_flat_infinitesimalNeighbourhoods f i hflat x (hx ▸ hi)

/-- The closed point of a local ring lies in the image of `Spec (R / J)` for a maximal ideal `J`. -/
private theorem closedPoint_mem_range_spec_mk {R : Type u} [CommRing R] [IsLocalRing R]
    (J : Ideal R) [J.IsMaximal] :
    IsLocalRing.closedPoint R ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) := by
  let : Field (R ⧸ J) := Ideal.Quotient.field _
  have : IsLocalHom (Ideal.Quotient.mk J) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  exact ⟨IsLocalRing.closedPoint (R ⧸ J), Spec_closedPoint⟩

/-- **Flatness from the truncations** ([Stacks, Tag 0D4G]). A universally closed morphism of
finite type from a locally Noetherian scheme to the spectrum of a Noetherian local ring is flat
as soon as all its base changes to the thickenings `Spec (R / 𝔪ⁿ⁺¹)` are. -/
theorem flat_of_flat_adicThickenings
    (R : CommRingCat.{u}) [IsLocalRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Spec R) [UniversallyClosed f] [LocallyOfFiniteType f]
    (hf : ∀ n, Flat (pullback.snd f (adicThickeningι R (maximalIdeal R) n))) : Flat f := by
  let i : Spec (.of (R ⧸ maximalIdeal R)) ⟶ Spec R :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R)))
  have : IsClosedImmersion i :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  apply flat_of_flat_infinitesimalNeighborhoods f i
  · exact closedPoint_mem_range_spec_mk (maximalIdeal R)
  · intro n
    exact flat_nthOrder_of_flat_adic R (maximalIdeal R) f n (hf n)

/-- **The fibre dimension is constant over a local base** ([Stacks, Tag 0D4J]). For a proper flat
morphism of finite presentation to the spectrum of a local ring, a bound on the dimension of the
closed fibre bounds the dimension of every fibre. -/
theorem fiberDimension_le_of_closedFibre
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
    (hfp : FinitePresentation f) {d : WithBot ℕ∞}
    (hd : f.fiberDimension (IsLocalRing.closedPoint R) ≤ d) :
    ∀ y, f.fiberDimension y ≤ d := by
  intro y
  have heq : f.fiberDimension y = f.fiberDimension (IsLocalRing.closedPoint R) :=
    (specializes_closedPoint y).mem_open
      ((isLocallyConstant_fiberDimension f hfp).isOpen_fiber
        (f.fiberDimension (IsLocalRing.closedPoint R))) rfl
  exact heq ▸ hd

private theorem fiberDimension_le_dimension {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    f.fiberDimension y ≤ topologicalKrullDim X := by
  change topologicalKrullDim (f.fiber y) ≤ _
  rw [(f.fiberHomeo y).isHomeomorph.topologicalKrullDim_eq]
  exact Topology.IsInducing.topologicalKrullDim_le
    (Topology.IsEmbedding.subtypeVal.isInducing)

end Algebraized

/-! ### The deformation tower -/

section Tower

variable {Λ : Type u} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]
  (hc : IsAdicComplete (maximalIdeal Λ) Λ) {X : Scheme.{u}} (fX : X ⟶ Spec (.of Λ)) [Flat fX]

/-- The `n`-th truncation `Xₙ = X ×_Λ Λ/𝔪ⁿ⁺¹`, as a deformation of the closed fibre `Xₛ`. -/
def sourceLevel (n : ℕ) : SchemeDeformationCategory (Λ := Λ) (k := ResidueField Λ)
    (Over.mk (pullback.snd fX (closedPoint Λ))) where
  base := AdicTruncation.obj (selfObj Λ hc) n
  scheme := adicBaseChange Λ (maximalIdeal Λ) fX n
  toBase := pullback.snd fX (adicThickeningι Λ (maximalIdeal Λ) n)
  flat := inferInstanceAs (Flat (pullback.snd fX (adicThickeningι Λ (maximalIdeal Λ) n)))
  specialMap := specialToLevel hc fX n
  specialCartesian := by
    have h := isPullback_specialToLevel hc fX n
    rwa [levelPoint, baseSpecMap_eq_residueSpecMap] at h

/-- The transition `Xₙ ⟶ Xₙ₊₁`, as an arrow of deformations of `Xₛ` from level `n + 1` to
level `n`. -/
def sourceTransition (n : ℕ) : sourceLevel hc fX (n + 1) ⟶ sourceLevel hc fX n where
  base := AdicTruncation.transition (selfObj Λ hc) n
  map := adicBaseChangeSucc Λ (maximalIdeal Λ) fX n
  cartesian := isPullback_adicBaseChangeSucc Λ (maximalIdeal Λ) fX n
  special_compat := specialToLevel_succ hc fX n

variable {Y₀ : Scheme.{u}} (h₀ : pullback fX (closedPoint Λ) ⟶ Y₀)
  (pY₀ : Y₀ ⟶ Spec (.of (ResidueField Λ))) (hh₀ : h₀ ≫ pY₀ = pullback.snd fX (closedPoint Λ))

/-- The output of the construction of [Stacks, Tag 0E3X] for one deformation `S` of `Xₛ`: a
flat `V` over the base of `S`, a morphism `g : S ⟶ V` over the base and a thickening `Y₀ ⟶ V`
identifying `Y₀` with the closed fibre of `V`, such that `Xₛ = Y₀ ×_V S`. -/
structure TargetData (S : SchemeDeformationCategory (Λ := Λ) (k := ResidueField Λ)
    (Over.mk (pullback.snd fX (closedPoint Λ)))) where
  /-- The deformation of `Y₀`. -/
  V : Scheme.{u}
  /-- Its structure morphism. -/
  pV : V ⟶ baseSpec S.base
  /-- The deformation of `h₀`. -/
  g : S.scheme ⟶ V
  /-- The identification of `Y₀` with the closed fibre of `V`. -/
  iY : Y₀ ⟶ V
  /-- It is flat. -/
  flat : Flat pV
  /-- `g` lies over the base. -/
  over_base : g ≫ pV = S.toBase
  /-- `Y₀` is the closed fibre of `V`. -/
  target : IsPullback iY pY₀ pV (residueSpecMap S.base)
  /-- `Xₛ` is the fibre product of `Y₀` and `S` over `V`. -/
  source : IsPullback h₀ S.specialMap iY g

variable (h0 : IsIso (C := Y₀.Modules) (Scheme.Modules.unitToPushforwardUnit h₀))
  (hR : IsZero (((Scheme.Modules.pushforward h₀).rightDerived 1).obj
      (SheafOfModules.unit (pullback fX (closedPoint Λ)).ringCatSheaf)))

include hh₀ h0 hR in
omit [IsNoetherianRing Λ] [Flat fX] in
/-- Every deformation `S` of `Xₛ` admits the data of a `TargetData`: a flat deformation `V` of
`Y₀` over the base of `S` and a deformation `S ⟶ V` of `h₀`. -/
theorem nonempty_targetData (S : SchemeDeformationCategory (Λ := Λ) (k := ResidueField Λ)
    (Over.mk (pullback.snd fX (closedPoint Λ)))) : Nonempty (TargetData fX h₀ pY₀ S) := by
  have := S.flat
  obtain ⟨V, pV, g, iY, hflat, hgp, htgt, hsrc⟩ :=
    exists_pushforwardTarget_isPullback_of_specialFibre S.toBase S.specialCartesian h₀ pY₀
      hh₀ h0 hR
  exact ⟨⟨V, pV, g, iY, hflat, hgp, htgt, hsrc⟩⟩

/-- A choice of the construction of [Stacks, Tag 0E3X] for each deformation of `Xₛ`. -/
def targetData (S : SchemeDeformationCategory (Λ := Λ) (k := ResidueField Λ)
    (Over.mk (pullback.snd fX (closedPoint Λ)))) : TargetData fX h₀ pY₀ S :=
  Classical.choice (nonempty_targetData fX h₀ pY₀ hh₀ h0 hR S)

omit [IsNoetherianRing Λ] [Flat fX] in
/-- `Y₀` is the fibre of the chosen `V` over the closed point of the base of `S`, the closed point
written as the map induced by the morphism from the base of `S` to the residue field. -/
theorem targetData_target_baseSpecMap
    (S : SchemeDeformationCategory (Λ := Λ) (k := ResidueField Λ)
      (Over.mk (pullback.snd fX (closedPoint Λ)))) :
    IsPullback (targetData fX h₀ pY₀ hh₀ h0 hR S).iY pY₀ (targetData fX h₀ pY₀ hh₀ h0 hR S).pV
      (baseSpecMap ((isTerminal_residueFieldBase (Λ := Λ) (k := ResidueField Λ)).from S.base)) := by
  rw [baseSpecMap_eq_residueSpecMap]
  exact (targetData fX h₀ pY₀ hh₀ h0 hR S).target

/-- The flat family of morphisms `S ⟶ V` deforming `h₀`, for a deformation `S` of `Xₛ`. -/
def liftFamily (S : SchemeDeformationCategory (Λ := Λ) (k := ResidueField Λ)
    (Over.mk (pullback.snd fX (closedPoint Λ)))) :
    SchemeMorphismFamily.{u, u} Λ (ResidueField Λ) where
  base := S.base
  source := S.scheme
  target := (targetData fX h₀ pY₀ hh₀ h0 hR S).V
  morphism := (targetData fX h₀ pY₀ hh₀ h0 hR S).g
  sourceToBase := S.toBase
  targetToBase := (targetData fX h₀ pY₀ hh₀ h0 hR S).pV
  over_base := (targetData fX h₀ pY₀ hh₀ h0 hR S).over_base
  source_flat := S.flat
  target_flat := (targetData fX h₀ pY₀ hh₀ h0 hR S).flat

/-- The deformation of `h₀` with source a given deformation `S` of `Xₛ`. -/
def liftObj (S : SchemeDeformationCategory (Λ := Λ) (k := ResidueField Λ)
    (Over.mk (pullback.snd fX (closedPoint Λ)))) :
    schemeMorphismDeformationCategory (Λ := Λ) (k := ResidueField Λ) h₀
      (pullback.snd fX (closedPoint Λ)) pY₀ hh₀ :=
  Over.mk (Y := liftFamily fX h₀ pY₀ hh₀ h0 hR S)
    { base := (isTerminal_residueFieldBase (Λ := Λ) (k := ResidueField Λ)).from S.base
      source := S.specialMap
      target := (targetData fX h₀ pY₀ hh₀ h0 hR S).iY
      source_pullback := (targetData fX h₀ pY₀ hh₀ h0 hR S).source
      target_pullback := targetData_target_baseSpecMap fX h₀ pY₀ hh₀ h0 hR S }

omit [IsNoetherianRing Λ] [Flat fX] in
/-- Forgetting the target of `liftObj S` recovers the deformation `S` of `Xₛ`. -/
theorem forget_obj_liftObj (S : SchemeDeformationCategory (Λ := Λ) (k := ResidueField Λ)
    (Over.mk (pullback.snd fX (closedPoint Λ)))) :
    (schemeMorphismSourceForgetful (Λ := Λ) (k := ResidueField Λ) h₀
        (pullback.snd fX (closedPoint Λ)) pY₀ hh₀).obj
      (liftObj fX h₀ pY₀ hh₀ h0 hR S) = S :=
  rfl

/-- The lift of the transition `Xₙ ⟶ Xₙ₊₁` to the deformations of `h₀`, by fullness of the
forgetful functor ([Stacks, Tag 0E3X]). -/
def liftTransition (n : ℕ) :
    liftObj fX h₀ pY₀ hh₀ h0 hR (sourceLevel hc fX (n + 1)) ⟶
      liftObj fX h₀ pY₀ hh₀ h0 hR (sourceLevel hc fX n) :=
  haveI := schemeMorphismSourceForgetful_full_of_specialFibre (Λ := Λ) (k := ResidueField Λ) h₀
    (pullback.snd fX (closedPoint Λ)) pY₀ hh₀ h0 hR
  (schemeMorphismSourceForgetful (Λ := Λ) (k := ResidueField Λ) h₀
      (pullback.snd fX (closedPoint Λ)) pY₀ hh₀).preimage
    (X := liftObj fX h₀ pY₀ hh₀ h0 hR (sourceLevel hc fX (n + 1)))
    (Y := liftObj fX h₀ pY₀ hh₀ h0 hR (sourceLevel hc fX n)) (sourceTransition hc fX n)

/-- Forgetting the target of `liftTransition n` recovers the transition `sourceTransition n`. -/
theorem forget_map_liftTransition (n : ℕ) :
    (schemeMorphismSourceForgetful (Λ := Λ) (k := ResidueField Λ) h₀
        (pullback.snd fX (closedPoint Λ)) pY₀ hh₀).map
      (liftTransition hc fX h₀ pY₀ hh₀ h0 hR n) = sourceTransition hc fX n :=
  have := schemeMorphismSourceForgetful_full_of_specialFibre (Λ := Λ) (k := ResidueField Λ) h₀
    (pullback.snd fX (closedPoint Λ)) pY₀ hh₀ h0 hR
  Functor.map_preimage _ _

/-- The map of bases of `liftTransition n` is the transition `Λ/𝔪ⁿ⁺² ⟶ Λ/𝔪ⁿ⁺¹`. -/
theorem liftTransition_base (n : ℕ) :
    (liftTransition hc fX h₀ pY₀ hh₀ h0 hR n).left.base =
      AdicTruncation.transition (selfObj Λ hc) n :=
  congrArg SchemeDeformationCategory.Hom.base (forget_map_liftTransition hc fX h₀ pY₀ hh₀ h0 hR n)

/-- The map of sources of `liftTransition n` is the transition `Xₙ ⟶ Xₙ₊₁`. -/
theorem liftTransition_source (n : ℕ) :
    (liftTransition hc fX h₀ pY₀ hh₀ h0 hR n).left.source =
      adicBaseChangeSucc Λ (maximalIdeal Λ) fX n :=
  congrArg SchemeDeformationCategory.Hom.map (forget_map_liftTransition hc fX h₀ pY₀ hh₀ h0 hR n)

/-- The `n`-th member `Yₙ` of the deformation tower of `Y₀`. -/
abbrev level (n : ℕ) : Scheme.{u} := (targetData fX h₀ pY₀ hh₀ h0 hR (sourceLevel hc fX n)).V

/-- The structure morphism `Yₙ ⟶ Spec (Λ / 𝔪ⁿ⁺¹)`. -/
abbrev levelToBase (n : ℕ) : level hc fX h₀ pY₀ hh₀ h0 hR n ⟶ adicThickening Λ (maximalIdeal Λ) n :=
  (targetData fX h₀ pY₀ hh₀ h0 hR (sourceLevel hc fX n)).pV

/-- The transition `Yₙ ⟶ Yₙ₊₁`. -/
abbrev levelSucc (n : ℕ) : level hc fX h₀ pY₀ hh₀ h0 hR n ⟶ level hc fX h₀ pY₀ hh₀ h0 hR (n + 1) :=
  (liftTransition hc fX h₀ pY₀ hh₀ h0 hR n).left.target

/-- `Yₙ` is the base change of `Yₙ₊₁` along `Spec (Λ/𝔪ⁿ⁺¹) ⟶ Spec (Λ/𝔪ⁿ⁺²)`. -/
theorem isPullback_levelSucc (n : ℕ) :
    IsPullback (levelSucc hc fX h₀ pY₀ hh₀ h0 hR n) (levelToBase hc fX h₀ pY₀ hh₀ h0 hR n)
      (levelToBase hc fX h₀ pY₀ hh₀ h0 hR (n + 1)) (adicThickeningSucc Λ (maximalIdeal Λ) n) := by
  have h := (liftTransition hc fX h₀ pY₀ hh₀ h0 hR n).left.target_pullback
  rwa [liftTransition_base] at h

/-- The deformation `Xₙ ⟶ Yₙ` of `h₀`. -/
abbrev levelMap (n : ℕ) :
    adicBaseChange Λ (maximalIdeal Λ) fX n ⟶ level hc fX h₀ pY₀ hh₀ h0 hR n :=
  (targetData fX h₀ pY₀ hh₀ h0 hR (sourceLevel hc fX n)).g

/-- The morphism `Xₙ ⟶ Yₙ` lies over `Spec (Λ/𝔪ⁿ⁺¹)`. -/
theorem levelMap_toBase (n : ℕ) :
    levelMap hc fX h₀ pY₀ hh₀ h0 hR n ≫ levelToBase hc fX h₀ pY₀ hh₀ h0 hR n =
      pullback.snd fX (adicThickeningι Λ (maximalIdeal Λ) n) :=
  (targetData fX h₀ pY₀ hh₀ h0 hR (sourceLevel hc fX n)).over_base

/-- The morphisms `Xₙ ⟶ Yₙ` commute with the transitions `Xₙ ⟶ Xₙ₊₁` and `Yₙ ⟶ Yₙ₊₁`. -/
theorem levelMap_succ (n : ℕ) :
    levelMap hc fX h₀ pY₀ hh₀ h0 hR n ≫ levelSucc hc fX h₀ pY₀ hh₀ h0 hR n =
      adicBaseChangeSucc Λ (maximalIdeal Λ) fX n ≫ levelMap hc fX h₀ pY₀ hh₀ h0 hR (n + 1) := by
  have h := (liftTransition hc fX h₀ pY₀ hh₀ h0 hR n).left.source_pullback.w
  rwa [liftTransition_source] at h

end Tower

/-! ### The algebraization -/

section Main

variable {Λ : Type u} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]
  (hc : IsAdicComplete (maximalIdeal Λ) Λ)

/-- The residue map of the zeroth truncation `Λ / 𝔪` is bijective. -/
theorem bijective_residueMap_truncation_zero :
    Function.Bijective (Artin.residueMap (AdicTruncation.obj (selfObj Λ hc) 0)) := by
  have hfield : IsField (AdicTruncation.obj (selfObj Λ hc) 0) := by
    have hm : (maximalIdeal (selfObj Λ hc) ^ (0 + 1)).IsMaximal := by
      simpa only [zero_add, pow_one] using maximalIdeal.isMaximal (selfObj Λ hc)
    exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient
      (maximalIdeal (selfObj Λ hc) ^ (0 + 1))).mp hm
  have hmax : maximalIdeal (AdicTruncation.obj (selfObj Λ hc) 0) = ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
  refine (AdicTruncation.obj (selfObj Λ hc) 0).residueEquiv.bijective.comp
    ⟨?_, residue_surjective⟩
  rw [injective_iff_map_eq_zero]
  intro a ha
  have h : a ∈ maximalIdeal (AdicTruncation.obj (selfObj Λ hc) 0) :=
    (residue_eq_zero_iff a).mp ha
  rwa [hmax] at h

/-- The closed point of the zeroth truncation `Spec (Λ / 𝔪)` is an isomorphism. -/
theorem isIso_residueSpecMap_truncation_zero :
    IsIso (residueSpecMap (AdicTruncation.obj (selfObj Λ hc) 0)) := by
  have : IsIso (CommRingCat.ofHom (Artin.residueMap (AdicTruncation.obj (selfObj Λ hc) 0))) :=
    (RingEquiv.ofBijective _ (bijective_residueMap_truncation_zero hc)).toCommRingCatIso.isIso_hom
  exact inferInstanceAs (IsIso (Spec.map _))

/-- The closed point of `Spec (Λ/𝔪ⁿ⁺¹)` composed with the inclusion into `Spec Λ` is the closed
point of `Spec Λ`. -/
theorem residueSpecMap_truncation_ι (n : ℕ) :
    residueSpecMap (AdicTruncation.obj (selfObj Λ hc) n) ≫
      adicThickeningι Λ (maximalIdeal Λ) n = ContractionUniquenessComplete.closedPoint Λ := by
  rw [← levelPoint_ι hc n, levelPoint, baseSpecMap_eq_residueSpecMap]
  rfl

variable {X : Scheme.{u}} (fX : X ⟶ Spec (.of Λ)) [Flat fX] [IsProper fX]
  {Y₀ : Scheme.{u}} (h₀ : pullback fX (closedPoint Λ) ⟶ Y₀)
  (pY₀ : Y₀ ⟶ Spec (.of (ResidueField Λ))) (hh₀ : h₀ ≫ pY₀ = pullback.snd fX (closedPoint Λ))
  (h0 : IsIso (C := Y₀.Modules) (Scheme.Modules.unitToPushforwardUnit h₀))
  (hR : IsZero (((Scheme.Modules.pushforward h₀).rightDerived 1).obj
      (SheafOfModules.unit (pullback fX (closedPoint Λ)).ringCatSheaf)))

include hc hh₀ h0 hR in
/-- **Extending a contraction of the closed fibre over a complete Noetherian local ring.** Let
`Λ` be a complete Noetherian local ring with residue field `κ` and closed point `s`, let
`fX : X ⟶ Spec Λ` be proper and flat, and let `h₀ : Xₛ ⟶ Y₀` be a morphism over `κ` to a proper
scheme `Y₀` of dimension at most one with `𝒪_{Y₀} ≅ h₀,*𝒪_{Xₛ}` and `R¹h₀,*𝒪_{Xₛ} = 0`. Then there
are a projective, proper, flat morphism of finite presentation `fY : Y ⟶ Spec Λ` all of whose
fibres have dimension at most one, a morphism `h : X ⟶ Y` over `Spec Λ`, and a morphism
`j : Y₀ ⟶ Y` exhibiting `Y₀` as the closed fibre of `Y`, through which `h` restricts to `h₀`.

This is the case of a complete Noetherian local base in the proof of [Stacks, Tag 0E7C]: the
deformation theory of [Stacks, Tag 0E3X] produces the formal curve `(Yₙ)` and the morphisms
`Xₙ ⟶ Yₙ`, which [Stacks, Tag 0E7R] and [Stacks, Tag 0A42] algebraize. -/
theorem exists_contraction_of_isAdicComplete (hproper : IsProper pY₀)
    (hdim : topologicalKrullDim Y₀ ≤ 1) :
    ∃ (Y : Scheme.{u}) (fY : Y ⟶ Spec (.of Λ)) (h : X ⟶ Y) (j : Y₀ ⟶ Y),
      IsProjectiveMorphism fY ∧ IsProper fY ∧ Flat fY ∧ FinitePresentation fY ∧
      (∀ y, fY.fiberDimension y ≤ 1) ∧ h ≫ fY = fX ∧
      IsPullback j pY₀ fY (closedPoint Λ) ∧ pullback.fst fX (closedPoint Λ) ≫ h = h₀ ≫ j := by
  have := hc
  have := hproper
  set D0 := targetData fX h₀ pY₀ hh₀ h0 hR (sourceLevel hc fX 0)
  have : IsIso (residueSpecMap (sourceLevel hc fX 0).base) :=
    isIso_residueSpecMap_truncation_zero hc
  have hiY : IsIso D0.iY := D0.target.isIso_fst_of_isIso
  have hq0 : D0.pV = inv D0.iY ≫ pY₀ ≫ residueSpecMap (sourceLevel hc fX 0).base := by
    rw [IsIso.eq_inv_comp]
    exact D0.target.w
  have hprop0' : IsProper D0.pV := by
    rw [hq0]
    infer_instance
  have hprop0 : IsProper (levelToBase hc fX h₀ pY₀ hh₀ h0 hR 0) := hprop0'
  have hdim0 : topologicalKrullDim (level hc fX h₀ pY₀ hh₀ h0 hR 0) ≤ 1 := by
    rwa [← (asIso D0.iY).hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
  obtain ⟨Y, fY, hproj, k, hk, hpb⟩ :=
    Stacks.FormalCurve.exists_isProjectiveMorphism_of_topologicalKrullDim_le_one Λ
      (maximalIdeal Λ) (levelToBase hc fX h₀ pY₀ hh₀ h0 hR) (levelSucc hc fX h₀ pY₀ hh₀ h0 hR)
      (isPullback_levelSucc hc fX h₀ pY₀ hh₀ h0 hR) hprop0 hdim0
  have : IsProper fY := (IsProjectiveMorphism.isProjective hproj).isProper
  let g : ∀ n, adicBaseChange Λ (maximalIdeal Λ) fX n ⟶ adicBaseChange Λ (maximalIdeal Λ) fY n :=
    fun n => levelMap hc fX h₀ pY₀ hh₀ h0 hR n ≫ (hpb n).isoPullback.hom
  have g_over : ∀ n, g n ≫ pullback.snd fY (adicThickeningι Λ (maximalIdeal Λ) n) =
      pullback.snd fX (adicThickeningι Λ (maximalIdeal Λ) n) := fun n => by
    simpa only [g, Category.assoc, IsPullback.isoPullback_hom_snd] using
      levelMap_toBase hc fX h₀ pY₀ hh₀ h0 hR n
  have hiso_succ : ∀ n, (hpb n).isoPullback.hom ≫ adicBaseChangeSucc Λ (maximalIdeal Λ) fY n =
      levelSucc hc fX h₀ pY₀ hh₀ h0 hR n ≫ (hpb (n + 1)).isoPullback.hom := fun n => by
    apply pullback.hom_ext
    · simp only [adicBaseChangeSucc, Category.assoc, pullback.lift_fst,
        IsPullback.isoPullback_hom_fst]
      exact (hk n).symm
    · simp only [adicBaseChangeSucc, Category.assoc, pullback.lift_snd,
        IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd_assoc]
      exact (isPullback_levelSucc hc fX h₀ pY₀ hh₀ h0 hR n).w.symm
  have g_compat : ∀ n, adicBaseChangeSucc Λ (maximalIdeal Λ) fX n ≫ g (n + 1) =
      g n ≫ adicBaseChangeSucc Λ (maximalIdeal Λ) fY n := fun n => by
    simp only [g, Category.assoc, hiso_succ]
    rw [← Category.assoc, ← levelMap_succ hc fX h₀ pY₀ hh₀ h0 hR n, Category.assoc]
  obtain ⟨⟨h, hh⟩, hhn, -⟩ := existsUnique_algebraization_adicBaseChangeMap_holds Λ
    (maximalIdeal Λ) hc fX fY g g_over g_compat
  -- flatness ([Stacks, Tag 0D4G])
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian fY
  have hflatn : ∀ n, Flat (pullback.snd fY (adicThickeningι Λ (maximalIdeal Λ) n)) := fun n => by
    have : Flat (levelToBase hc fX h₀ pY₀ hh₀ h0 hR n) :=
      (targetData fX h₀ pY₀ hh₀ h0 hR (sourceLevel hc fX n)).flat
    rw [← (hpb n).isoPullback_inv_snd]
    infer_instance
  have : Flat fY := flat_of_flat_adicThickenings (.of Λ) fY hflatn
  have hfp : FinitePresentation fY := finitePresentation_of_finiteType fY
  -- the dimension of the fibres ([Stacks, Tag 0D4J])
  have hdimClosed : fY.fiberDimension (IsLocalRing.closedPoint Λ) ≤ 1 := by
    have : (maximalIdeal Λ ^ (0 + 1)).IsMaximal := by
      simpa only [zero_add, pow_one] using maximalIdeal.isMaximal Λ
    obtain ⟨x, hx⟩ := closedPoint_mem_range_spec_mk (maximalIdeal Λ ^ (0 + 1))
    have h1 := congrFun (Scheme.Hom.fiberDimension_pullback_snd fY
      (adicThickeningι Λ (maximalIdeal Λ) 0)) x
    change (pullback.snd fY (adicThickeningι Λ (maximalIdeal Λ) 0)).fiberDimension x =
      fY.fiberDimension ((adicThickeningι Λ (maximalIdeal Λ) 0) x) at h1
    rw [show (adicThickeningι Λ (maximalIdeal Λ) 0) x = _ from hx] at h1
    rw [← h1]
    refine (fiberDimension_le_dimension _ _).trans ?_
    rwa [← (hpb 0).isoPullback.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
  refine ⟨Y, fY, h, D0.iY ≫ k 0, hproj, inferInstance, inferInstance, hfp,
    fiberDimension_le_of_closedFibre fY hfp hdimClosed, hh, ?_, ?_⟩
  · have H := D0.target.paste_horiz (hpb 0)
    have e : residueSpecMap (sourceLevel hc fX 0).base ≫ adicThickeningι Λ (maximalIdeal Λ) 0 =
        ContractionUniquenessComplete.closedPoint Λ := residueSpecMap_truncation_ι hc 0
    rwa [e] at H
  · have h1 : pullback.fst fX (adicThickeningι Λ (maximalIdeal Λ) 0) ≫ h =
        levelMap hc fX h₀ pY₀ hh₀ h0 hR 0 ≫ k 0 := by
      simpa only [adicBaseChangeMap, pullback.lift_fst, g, Category.assoc,
        IsPullback.isoPullback_hom_fst] using
        congrArg (· ≫ pullback.fst fY (adicThickeningι Λ (maximalIdeal Λ) 0)) (hhn 0)
    have h2 : specialToLevel hc fX 0 ≫ levelMap hc fX h₀ pY₀ hh₀ h0 hR 0 = h₀ ≫ D0.iY :=
      D0.source.w.symm
    rw [← specialToLevel_fst hc fX 0, Category.assoc, h1, ← Category.assoc, h2, Category.assoc]

end Main

end EtaleLocalContraction

end AlgebraicGeometry

end
