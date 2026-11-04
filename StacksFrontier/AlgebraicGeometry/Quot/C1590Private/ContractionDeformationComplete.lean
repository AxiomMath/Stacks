module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ContractionUniquenessNoetherianLocal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalCurve.Algebraization
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.FlatLocusOpenness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalNeighbourhood.FlatnessKernelPowers
public import StacksFrontier.Deformation.BaseCategory.IdealQuotient

/-!
# Deforming a contraction over a complete local ring (the core of Stacks 0E7C)

Let `Λ` be a complete Noetherian local ring with residue field `κ`, let `X` be a proper flat
scheme over `Spec Λ` with special fibre `Xₛ`, and let `h₀ : Xₛ ⟶ Y₀` be a morphism to a proper
scheme of dimension at most one over `κ` with `𝒪_{Y₀} ≅ h₀,*𝒪_{Xₛ}` and `R¹h₀,*𝒪_{Xₛ} = 0`. Then
there are a proper flat projective scheme `Y` over `Spec Λ`, a morphism `h : X ⟶ Y` over `Spec Λ`
and an identification of the special fibre of `Y` with `Y₀` carrying the special fibre of `h` to
`h₀`.

This is the step "Assume `S = Spec(Λ)` ... complete" of the proof of [Stacks, Tag 0E7C], and it
is proved as the source proves it:

* the truncations `Xₙ` of `X` are deformations of `Xₛ`, and the forgetful functor from
  deformations of `h₀` to deformations of `Xₛ` is an equivalence ([Stacks, Tag 0E3X]), so they
  come with compatible deformations `hₙ : Xₙ ⟶ Yₙ` of `h₀`;
* the tower `(Yₙ)` is algebraized by a projective `Y` ([Stacks, Tag 0E7R] for schemes,
  `Stacks.FormalCurve.exists_isProjectiveMorphism_of_topologicalKrullDim_le_one`), flat because
  every `Yₙ` is ([Stacks, Tag 0D4G]);
* the `hₙ` are algebraized by `h` ([Stacks, Tag 0A42],
  `AlgebraicGeometry.existsUnique_algebraization_adicBaseChangeMap_holds`).

## References

* [Stacks Project, Tag 0E7C](https://stacks.math.columbia.edu/tag/0E7C)
* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
* [Stacks Project, Tag 0E7R](https://stacks.math.columbia.edu/tag/0E7R)
* [Stacks Project, Tag 0A42](https://stacks.math.columbia.edu/tag/0A42)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Deformation Deformation.Examples

universe u

namespace AlgebraicGeometry.C1590Private

open ContractionUniquenessComplete

namespace ContractionDeformation

variable {Λ : Type u} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]
  (hc : IsAdicComplete (maximalIdeal Λ) Λ) {X : Scheme.{u}} (fX : X ⟶ Spec (.of Λ)) [Flat fX]

/-- The `n`-th truncation of `X`, as a deformation of its special fibre. -/
def xLevel (n : ℕ) : SchemeDeformationCategory (Λ := Λ) (k := ResidueField Λ)
    (Over.mk (pullback.snd fX (ContractionUniquenessComplete.closedPoint Λ))) where
  base := AdicTruncation.obj (selfObj Λ hc) n
  scheme := adicBaseChange Λ (maximalIdeal Λ) fX n
  toBase := pullback.snd fX (adicThickeningι Λ (maximalIdeal Λ) n)
  flat := inferInstanceAs (Flat (pullback.snd fX (adicThickeningι Λ (maximalIdeal Λ) n)))
  specialMap := specialToLevel hc fX n
  specialCartesian := by
    have h := isPullback_specialToLevel hc fX n
    rwa [levelPoint, baseSpecMap_eq_residueSpecMap] at h

/-- The transition from the `(n + 1)`-st truncation of `X` to the `n`-th one. -/
def xTransition (n : ℕ) : xLevel hc fX (n + 1) ⟶ xLevel hc fX n where
  base := AdicTruncation.transition (selfObj Λ hc) n
  map := adicBaseChangeSucc Λ (maximalIdeal Λ) fX n
  cartesian := isPullback_adicBaseChangeSucc Λ (maximalIdeal Λ) fX n
  special_compat := specialToLevel_succ hc fX n

variable {Y₀ : Scheme.{u}} (gY₀ : Y₀ ⟶ Spec (.of (ResidueField Λ)))
  (h₀ : pullback fX (ContractionUniquenessComplete.closedPoint Λ) ⟶ Y₀)
  (hh₀ : h₀ ≫ gY₀ = pullback.snd fX (ContractionUniquenessComplete.closedPoint Λ))

include hh₀ in
/-- **The formal deformation of `h₀`.** The truncations `Xₙ` of `X` come with a tower of flat
deformations `Yₙ` of `Y₀` over `Λ / 𝔪ⁿ⁺¹`, with cartesian transitions, and compatible
morphisms `hₙ : Xₙ ⟶ Yₙ` deforming `h₀` ([Stacks, Tag 0E3X]). -/
theorem exists_formalDeformation
    (h0 : IsIso (C := Y₀.Modules) (Scheme.Modules.unitToPushforwardUnit h₀))
    (hR : IsZero (((Scheme.Modules.pushforward h₀).rightDerived 1).obj
      (SheafOfModules.unit
        (pullback fX (ContractionUniquenessComplete.closedPoint Λ)).ringCatSheaf))) :
    ∃ (V : ℕ → Scheme.{u}) (pV : ∀ n, V n ⟶ adicThickening Λ (maximalIdeal Λ) n)
      (i : ∀ n, V n ⟶ V (n + 1)) (g : ∀ n, adicBaseChange Λ (maximalIdeal Λ) fX n ⟶ V n)
      (iY : ∀ n, Y₀ ⟶ V n),
      (∀ n, Flat (pV n)) ∧
      (∀ n, IsPullback (i n) (pV n) (pV (n + 1)) (adicThickeningSucc Λ (maximalIdeal Λ) n)) ∧
      (∀ n, g n ≫ pV n = pullback.snd fX (adicThickeningι Λ (maximalIdeal Λ) n)) ∧
      (∀ n, adicBaseChangeSucc Λ (maximalIdeal Λ) fX n ≫ g (n + 1) = g n ≫ i n) ∧
      (∀ n, IsPullback (iY n) gY₀ (pV n) (levelPoint hc n)) ∧
      (∀ n, h₀ ≫ iY n = specialToLevel hc fX n ≫ g n) := by
  have hD : ∀ n, ∃ (V : Scheme.{u}) (pV : V ⟶ baseSpec (AdicTruncation.obj (selfObj Λ hc) n))
      (g : adicBaseChange Λ (maximalIdeal Λ) fX n ⟶ V) (iY : Y₀ ⟶ V),
      Flat pV ∧ g ≫ pV = pullback.snd fX (adicThickeningι Λ (maximalIdeal Λ) n) ∧
        IsPullback iY gY₀ pV (residueSpecMap (AdicTruncation.obj (selfObj Λ hc) n)) ∧
          IsPullback h₀ (specialToLevel hc fX n) iY g := fun n => by
    have := (xLevel hc fX n).flat
    exact exists_pushforwardTarget_isPullback_of_specialFibre (Λ := Λ) (k := ResidueField Λ)
      (xLevel hc fX n).toBase
      (xLevel hc fX n).specialCartesian h₀ gY₀ hh₀ h0 hR
  choose V pV g iY hflat hgp htgt hsrc using hD
  -- the deformations of `h₀`
  let F := schemeMorphismSourceForgetful (Λ := Λ) (k := ResidueField Λ) h₀
    (pullback.snd fX (ContractionUniquenessComplete.closedPoint Λ)) gY₀ hh₀
  have : F.Full := schemeMorphismSourceForgetful_full_of_specialFibre _ _ _ _ h0 hR
  have htgt' : ∀ n, IsPullback (iY n) gY₀ (pV n)
      (baseSpecMap ((isTerminal_residueFieldBase (Λ := Λ) (k := ResidueField Λ)).from
        (AdicTruncation.obj (selfObj Λ hc) n))) := fun n => by
    rw [baseSpecMap_eq_residueSpecMap]
    exact htgt n
  let D : ∀ n, schemeMorphismDeformationCategory (Λ := Λ) (k := ResidueField Λ) h₀
      (pullback.snd fX (ContractionUniquenessComplete.closedPoint Λ)) gY₀ hh₀ := fun n =>
    Over.mk
      ({ base := (isTerminal_residueFieldBase (Λ := Λ) (k := ResidueField Λ)).from
            (AdicTruncation.obj (selfObj Λ hc) n)
         source := specialToLevel hc fX n
         target := iY n
         source_pullback := hsrc n
         target_pullback := htgt' n } :
        ({ base := AdicTruncation.obj (selfObj Λ hc) n
           source := adicBaseChange Λ (maximalIdeal Λ) fX n
           target := V n
           morphism := g n
           sourceToBase := pullback.snd fX (adicThickeningι Λ (maximalIdeal Λ) n)
           targetToBase := pV n
           over_base := hgp n
           source_flat :=
            inferInstanceAs (Flat (pullback.snd fX (adicThickeningι Λ (maximalIdeal Λ) n)))
           target_flat := hflat n } : SchemeMorphismFamily.{u, u} Λ (ResidueField Λ)) ⟶
          schemeMorphismFamilySpecialFiber (Λ := Λ) (k := ResidueField Λ) h₀
            (pullback.snd fX (ContractionUniquenessComplete.closedPoint Λ)) gY₀ hh₀)
  -- the transitions, by fullness
  let T : ∀ n, D (n + 1) ⟶ D n := fun n => F.preimage (xTransition hc fX n)
  have hT : ∀ n, F.map (T n) = xTransition hc fX n := fun n => F.map_preimage _
  have hTbase : ∀ n, (T n).left.base = AdicTruncation.transition (selfObj Λ hc) n := fun n =>
    congrArg SchemeDeformationCategory.Hom.base (hT n)
  have hTsrc : ∀ n, (T n).left.source = adicBaseChangeSucc Λ (maximalIdeal Λ) fX n := fun n =>
    congrArg SchemeDeformationCategory.Hom.map (hT n)
  refine ⟨V, pV, fun n => (T n).left.target, g, iY, hflat, fun n => ?_, hgp, fun n => ?_,
    fun n => ?_, fun n => ?_⟩
  · have h := (T n).left.target_pullback
    rwa [hTbase] at h
  · have h := (T n).left.source_pullback.w
    rw [hTsrc] at h
    exact h.symm
  · have h := htgt n
    rwa [← baseSpecMap_eq_residueSpecMap _
      ((isTerminal_residueFieldBase (Λ := Λ) (k := ResidueField Λ)).from
        (AdicTruncation.obj (selfObj Λ hc) n))] at h
  · exact (hsrc n).w

/-! ### The level zero -/

omit [IsNoetherianRing Λ] in
/-- Two elements with the same residue differ by an element of `𝔪 = 𝔪 ^ (0 + 1)`. -/
theorem mem_maximalIdeal_pow_one_of_residue_eq (a b : Λ) (h : residue Λ a = residue Λ b) :
    a - b ∈ maximalIdeal Λ ^ (0 + 1) := by
  rw [zero_add, pow_one, ← residue_eq_zero_iff, map_sub, h, sub_self]

omit [Flat fX] in
/-- The closed point of the `0`-th truncation is an isomorphism `Spec κ ≅ Spec (Λ / 𝔪)`. -/
theorem isIso_levelPoint_zero : IsIso (levelPoint hc 0) := by
  have hb' : (toResidue hc 0).hom.toRingHom =
      Deformation.Artin.residueMap (AdicTruncation.obj (selfObj Λ hc) 0) := by
    ext a
    have h := (toResidue hc 0).residue_comm a
    rwa [residueFieldBase_residueEquiv_residue] at h
  have hres : ∀ a : Λ, (toResidue hc 0).hom
      (Ideal.Quotient.mk (AdicTruncation.ideal (selfObj Λ hc) 0) a) = residue Λ a := fun a =>
    (congrArg (fun φ => φ (Ideal.Quotient.mk (AdicTruncation.ideal (selfObj Λ hc) 0) a)) hb').trans
      (AdicTruncation.residueEquiv_residue_mk (selfObj Λ hc) 0 a)
  have hb : Function.Bijective (toResidue hc 0).hom := by
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hab : residue Λ a = residue Λ b := (hres a).symm.trans (hxy.trans (hres b))
      exact Ideal.Quotient.eq.2 (mem_maximalIdeal_pow_one_of_residue_eq a b hab)
    · obtain ⟨r, rfl⟩ := residue_surjective z
      exact ⟨Ideal.Quotient.mk _ r, hres r⟩
  have := ArtinianLocalAlgCat.isIso_of_bijective_hom (toResidue hc 0) hb
  exact inferInstanceAs (IsIso (baseSpecMap (toResidue hc 0)))

/-! ### Flatness from the truncations -/

omit [Flat fX] in
/-- **A proper scheme over a Noetherian local ring is flat if all its truncations are**
([Stacks, Tag 0D4G]): it is flat at the points over the closed point, the flat locus is open,
and a closed subset of `Y` missing the closed fibre has closed image missing the closed point,
hence is empty. -/
theorem flat_of_flat_adicBaseChange {Y : Scheme.{u}} (fY : Y ⟶ Spec (.of Λ)) [IsProper fY]
    (hflat : ∀ n, Flat (pullback.snd fY (adicThickeningι Λ (maximalIdeal Λ) n))) : Flat fY := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian fY
  have hclosed : ∀ y : Y, fY y = IsLocalRing.closedPoint Λ → (fY.stalkMap y).hom.Flat :=
    fun y hy => flat_stalkMap_of_flat_pullbacks_spec_quotient_pow (maximalIdeal Λ) fY hflat y
      (by rw [hy]; exact le_rfl)
  set W := {y : Y | (fY.stalkMap y).hom.Flat}
  have hW : IsOpen W := isOpen_setOf_isFlatAt_of_isLocallyNoetherian fY
  have himg : IsClosed (fY.base '' Wᶜ) := fY.isClosedMap _ hW.isClosed_compl
  have hempty : fY.base '' Wᶜ = ∅ := by
    by_contra hne
    obtain ⟨_, ⟨y, hy, rfl⟩⟩ := Set.nonempty_iff_ne_empty.2 hne
    have hcp : IsLocalRing.closedPoint Λ ∈ fY.base '' Wᶜ :=
      himg.closure_subset_iff.2 (Set.singleton_subset_iff.2 ⟨y, hy, rfl⟩)
        (IsLocalRing.specializes_closedPoint (fY y)).mem_closure
    obtain ⟨z, hz, hzc⟩ := hcp
    exact hz (hclosed z hzc)
  refine Flat.of_stalkMap fY fun y => ?_
  by_contra hy
  exact hempty.subset ⟨y, hy, rfl⟩

/-! ### The algebraization -/

include hc hh₀ in
/-- **Deforming a contraction over a complete local ring.** Let `Λ` be a complete Noetherian local
ring with residue field `κ`, `X` proper and flat over `Spec Λ`, and `h₀ : Xₛ ⟶ Y₀` a morphism over
`κ` to a proper scheme of dimension at most one with `𝒪_{Y₀} ≅ h₀,*𝒪_{Xₛ}` and
`R¹h₀,*𝒪_{Xₛ} = 0`. Then there are a projective, flat `Y ⟶ Spec Λ`, a morphism `h : X ⟶ Y` over
`Spec Λ`, and an isomorphism of `Y₀` with the special fibre of `Y` carrying `h₀` to the special
fibre of `h`. -/
theorem exists_contraction_of_isAdicComplete [IsProper fX] [IsProper gY₀]
    (h0 : IsIso (C := Y₀.Modules) (Scheme.Modules.unitToPushforwardUnit h₀))
    (hR : IsZero (((Scheme.Modules.pushforward h₀).rightDerived 1).obj
      (SheafOfModules.unit
        (pullback fX (ContractionUniquenessComplete.closedPoint Λ)).ringCatSheaf)))
    (hdimY : topologicalKrullDim Y₀ ≤ ((1 : ℕ) : WithBot ℕ∞)) :
    ∃ (Y : Scheme.{u}) (fY : Y ⟶ Spec (.of Λ)) (h : X ⟶ Y) (hh : h ≫ fY = fX),
      IsProjective fY ∧ IsProper fY ∧ Flat fY ∧
      ∃ ι : Y₀ ≅ pullback fY (ContractionUniquenessComplete.closedPoint Λ),
        ι.hom ≫ pullback.snd _ _ = gY₀ ∧
        h₀ ≫ ι.hom = fibreHom (ContractionUniquenessComplete.closedPoint Λ) fX fY h hh := by
  obtain ⟨V, pV, i, g, iY, hflat, hcart, hgp, hgc, htgt, hspec⟩ :=
    exists_formalDeformation hc fX gY₀ h₀ hh₀ h0 hR
  have := isIso_levelPoint_zero hc
  have : IsIso (iY 0) := (htgt 0).isIso_fst_of_isIso
  have : IsProper (pV 0) := by
    rw [show pV 0 = inv (iY 0) ≫ gY₀ ≫ levelPoint hc 0 by rw [IsIso.eq_inv_comp, (htgt 0).w]]
    infer_instance
  have hdimV : topologicalKrullDim (V 0 : Type u) ≤ 1 :=
    (Topology.IsInducing.topologicalKrullDim_le
      (Scheme.Hom.homeomorph (inv (iY 0))).isInducing).trans (by exact_mod_cast hdimY)
  have : IsAdicComplete (maximalIdeal Λ) Λ := hc
  obtain ⟨Y, fY, hproj, k, hk, hkpb⟩ :=
    Stacks.FormalCurve.exists_isProjectiveMorphism_of_topologicalKrullDim_le_one Λ
      (maximalIdeal Λ) pV i hcart inferInstance hdimV
  have hfYproj := hproj.isProjective
  have : IsProper fY := hfYproj.isProper
  -- the morphisms of the truncations
  let ε : ∀ n, V n ≅ adicBaseChange Λ (maximalIdeal Λ) fY n := fun n => (hkpb n).isoPullback
  have hεf : ∀ n, (ε n).hom ≫ pullback.fst fY (adicThickeningι Λ (maximalIdeal Λ) n) = k n :=
    fun n => IsPullback.isoPullback_hom_fst _
  have hεs : ∀ n, (ε n).hom ≫ pullback.snd fY (adicThickeningι Λ (maximalIdeal Λ) n) = pV n :=
    fun n => IsPullback.isoPullback_hom_snd _
  let g' : ∀ n, adicBaseChange Λ (maximalIdeal Λ) fX n ⟶ adicBaseChange Λ (maximalIdeal Λ) fY n :=
    fun n => g n ≫ (ε n).hom
  have g_over : ∀ n, g' n ≫ pullback.snd fY (adicThickeningι Λ (maximalIdeal Λ) n) =
      pullback.snd fX (adicThickeningι Λ (maximalIdeal Λ) n) := fun n => by
    rw [Category.assoc, hεs, hgp]
  have g_compat : ∀ n, adicBaseChangeSucc Λ (maximalIdeal Λ) fX n ≫ g' (n + 1) =
      g' n ≫ adicBaseChangeSucc Λ (maximalIdeal Λ) fY n := fun n => by
    apply pullback.hom_ext
    · simp only [g', Category.assoc, hεf]
      rw [reassoc_of% (hgc n), hk, adicBaseChangeSucc_fst, hεf]
    · have e : ∀ {Z : Scheme.{u}} (f : Z ⟶ Spec (.of Λ)),
          adicBaseChangeSucc Λ (maximalIdeal Λ) f n ≫
            pullback.snd f (adicThickeningι Λ (maximalIdeal Λ) (n + 1)) =
          pullback.snd f (adicThickeningι Λ (maximalIdeal Λ) n) ≫
            adicThickeningSucc Λ (maximalIdeal Λ) n := fun f => pullback.lift_snd _ _ _
      simp only [g', Category.assoc, hεs]
      rw [hgp, e fX, e fY, reassoc_of% (hεs n), reassoc_of% (hgp n)]
  obtain ⟨⟨h, hh⟩, hhn, -⟩ := existsUnique_algebraization_adicBaseChangeMap_holds Λ
    (maximalIdeal Λ) hc fX fY g' g_over g_compat
  -- flatness
  have hflY : Flat fY := flat_of_flat_adicBaseChange fY fun n => by
    rw [show pullback.snd fY (adicThickeningι Λ (maximalIdeal Λ) n) = (ε n).inv ≫ pV n by
      rw [Iso.eq_inv_comp, hεs]]
    have := hflat n
    infer_instance
  -- the special fibre
  have P : IsPullback (iY 0 ≫ k 0) gY₀ fY (ContractionUniquenessComplete.closedPoint Λ) := by
    have h₁ := (htgt 0).paste_horiz (hkpb 0)
    rwa [levelPoint_ι] at h₁
  refine ⟨Y, fY, h, hh, hfYproj, inferInstance, hflY, P.isoPullback, P.isoPullback_hom_snd, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, P.isoPullback_hom_fst, fibreHom_fst, reassoc_of% (hspec 0)]
    have h₂ := congrArg (· ≫ pullback.fst fY (adicThickeningι Λ (maximalIdeal Λ) 0)) (hhn 0)
    simp only [g', Category.assoc, hεf, adicBaseChangeMap_fst] at h₂
    rw [← h₂, specialToLevel_fst_assoc]
  · rw [Category.assoc, P.isoPullback_hom_snd, fibreHom_snd, hh₀]

end ContractionDeformation

end AlgebraicGeometry.C1590Private

end
