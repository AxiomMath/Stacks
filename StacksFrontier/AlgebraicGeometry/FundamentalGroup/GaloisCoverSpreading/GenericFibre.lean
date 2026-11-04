module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.GaloisCoverNoetherianBase
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverLimits.LimitDescent
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GenericResidueFieldOfSpec
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.StalkAffineNhdsLimit.Preimage

/-!
# Spreading out a Galois cover of the generic fibre

Let `S` be an integral scheme with generic point `η` and `f : X ⟶ S` a quasi-compact and
quasi-separated morphism. A finite étale Galois cover of the generic fibre `X_η` with finite group
`G` is the restriction of a finite étale Galois cover of `f⁻¹(U)` with group `G`, equivariantly,
for some open neighbourhood `U` of `η`. This is the first step of the maximal-open argument in the
proof of [Stacks, Tag 0EYJ], which the source takes for granted.

## Main results

* `AlgebraicGeometry.Abhyankar.exists_galoisExtendsOver_of_flat`: the spreading out, for `f`
  quasi-compact, quasi-separated, flat and locally of finite presentation.
* `AlgebraicGeometry.Abhyankar.exists_galoisExtendsOver`: the form used in the proof of
  [Stacks, Tag 0EYJ].

## Implementation notes

The generic fibre `X_η` is the fibre over the local scheme `Spec 𝒪_{S,η}` (whose closed point is
`η`), so it is the limit of the preimages `f⁻¹(W)` of the affine open neighbourhoods `W` of `η`
(`AlgebraicGeometry.isLimitPreimageSpecStalkCone`). The projections `X_η ⟶ f⁻¹(W)` are not
surjective, so the Galois cover descends through
`AlgebraicGeometry.GaloisCoverLimits.exists_torsor_model`, which needs no surjectivity. The
descended cover is connected because it is flat and locally of finite presentation over `S` with
connected generic fibre.

## References

* [Stacks Project, Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

namespace GaloisCoverLimits

/-- A scheme flat and locally of finite presentation over an integral scheme, whose generic
fibre is connected, is connected: the generic fibre is dense, the morphism being open. -/
theorem connectedSpace_of_connectedSpace_genericFiber {S Y : Scheme.{u}} [IsIntegral S]
    (f : Y ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [ConnectedSpace (f.fiber (genericPoint S))] : ConnectedSpace Y := by
  have hη : Dense ({genericPoint S} : Set S) := by
    rw [dense_iff_closure_eq, (genericPoint_spec S).def]
  have hrange : DenseRange (f.fiberι (genericPoint S)) := by
    rw [denseRange_iff_closure_range, f.range_fiberι]
    exact (hη.preimage f.isOpenMap).closure_eq
  have : Nonempty Y := ⟨f.fiberι (genericPoint S) (Classical.choice inferInstance)⟩
  have hpre : PreconnectedSpace Y :=
    hrange.preconnectedSpace (f.fiberι (genericPoint S)).continuous
  exact { toPreconnectedSpace := hpre, toNonempty := inferInstance }

end GaloisCoverLimits

/-- A square whose right edge factors through a monomorphism is cartesian as soon as the square
obtained by moving the monomorphism to the top edge is. -/
theorem isPullback_of_isPullback_comp_mono {C : Type*} [Category* C] {P U X Y S : C}
    {a : P ⟶ U} {b : P ⟶ Y} {m : U ⟶ X} {f : X ⟶ S} {c : Y ⟶ S} [Mono m]
    (H : IsPullback (a ≫ m) b f c) : IsPullback a b (m ≫ f) c := by
  refine IsPullback.of_isLimit' ⟨by rw [← Category.assoc]; exact H.w⟩
    (PullbackCone.IsLimit.mk _ (fun s ↦ H.lift (s.fst ≫ m) s.snd (by
      rw [Category.assoc]; exact s.condition)) (fun s ↦ ?_) (fun s ↦ H.lift_snd _ _ _)
      (fun s l h₁ h₂ ↦ ?_))
  · rw [← cancel_mono m]
    simp
  · apply H.hom_ext <;> simp [reassoc_of% h₁, h₂]

namespace Abhyankar

variable {S X : Scheme.{u}} (f : X ⟶ S) [IsIntegral S]

/-- The generic fibre of `f` is the generic fibre of its restriction to `f⁻¹(U)`. -/
theorem isPullback_genericFiberToPreimage (U : S.Opens) (hη : genericPoint S ∈ U) :
    IsPullback (genericFiberToPreimage f U hη) (f.fiberToSpecResidueField (genericPoint S))
      ((f ⁻¹ᵁ U).ι ≫ f) (S.fromSpecResidueField (genericPoint S)) :=
  isPullback_of_isPullback_comp_mono (by
    rw [genericFiberToPreimage_ι]
    exact IsPullback.of_hasPullback f (S.fromSpecResidueField (genericPoint S)))

/-- A finite étale cover of `f⁻¹(U)`, for `f` flat and locally of finite presentation, is
connected as soon as its restriction to the generic fibre is. -/
theorem connectedSpace_of_isPullback_genericFiberToPreimage [Flat f]
    [LocallyOfFinitePresentation f] (U : S.Opens) (hη : genericPoint S ∈ U)
    (V : FiniteEtaleOver (f ⁻¹ᵁ U).toScheme) {W : Scheme.{u}} (q : W ⟶ f.fiber (genericPoint S))
    (P : W ⟶ V.left) (hP : IsPullback P q V.hom (genericFiberToPreimage f U hη))
    [ConnectedSpace W] : ConnectedSpace V.left := by
  have : Etale V.hom := V.prop.2
  have : ConnectedSpace ((V.hom ≫ (f ⁻¹ᵁ U).ι ≫ f).fiber (genericPoint S)) :=
    (hP.paste_vert (isPullback_genericFiberToPreimage f U hη)).isoPullback.hom.homeomorph
      |>.connectedSpace_iff.mp inferInstance
  exact GaloisCoverLimits.connectedSpace_of_connectedSpace_genericFiber (V.hom ≫ (f ⁻¹ᵁ U).ι ≫ f)

/-- The generic fibre `X_η`, with its maps into the preimages `f⁻¹(W)` of the affine open
neighbourhoods `W` of `η`. -/
def genericFiberCone : Cone (preimageAffineOpenNhdsDiagram f (genericPoint S)) where
  pt := f.fiber (genericPoint S)
  π :=
  { app := fun W ↦ genericFiberToPreimage f W.opens W.mem_opens
    naturality := fun W W' g ↦ by
      change 𝟙 _ ≫ genericFiberToPreimage f W'.opens W'.mem_opens =
        genericFiberToPreimage f W.opens W.mem_opens ≫
          X.homOfLE (Scheme.Hom.preimage_mono f (AffineOpenNhds.opens_le g))
      rw [← cancel_mono (f ⁻¹ᵁ W'.opens).ι]
      simp only [Category.assoc, Scheme.homOfLE_ι, genericFiberToPreimage_ι, Category.id_comp] }

/-- The cone point of `genericFiberCone f` is the generic fibre of `f`. -/
@[simp]
theorem genericFiberCone_pt : (genericFiberCone f).pt = f.fiber (genericPoint S) :=
  rfl

/-- The leg of `genericFiberCone f` at an affine open neighbourhood `W` of `η` is the map
`X_η ⟶ f⁻¹(W)`. -/
@[simp]
theorem genericFiberCone_π_app (W : AffineOpenNhds S (genericPoint S)) :
    (genericFiberCone f).π.app W = genericFiberToPreimage f W.opens W.mem_opens :=
  rfl

/-- **The generic fibre is the limit of the preimages of the affine open neighbourhoods of the
generic point**: it is the fibre over the local scheme `Spec 𝒪_{S,η}`, whose closed point is
`η`. -/
def isLimitGenericFiberCone : IsLimit (genericFiberCone f) := by
  haveI : IsIso (S.residue (genericPoint S)) := isIso_residue_genericPoint S
  have hι₀ : IsIso (pullback.map f (S.fromSpecResidueField (genericPoint S)) f
      (S.fromSpecStalk (genericPoint S)) (𝟙 X) (Spec.map (S.residue (genericPoint S))) (𝟙 S)
      (by rw [Category.id_comp, Category.comp_id])
      (by rw [Category.comp_id, Scheme.fromSpecResidueField])) := inferInstance
  have hι₀fst : pullback.map f (S.fromSpecResidueField (genericPoint S)) f
      (S.fromSpecStalk (genericPoint S)) (𝟙 X) (Spec.map (S.residue (genericPoint S))) (𝟙 S)
      (by rw [Category.id_comp, Category.comp_id])
      (by rw [Category.comp_id, Scheme.fromSpecResidueField]) ≫
        pullback.fst f (S.fromSpecStalk (genericPoint S)) =
      pullback.fst f (S.fromSpecResidueField (genericPoint S)) := by
    rw [pullback.lift_fst, Category.comp_id]
  generalize pullback.map f (S.fromSpecResidueField (genericPoint S)) f
      (S.fromSpecStalk (genericPoint S)) (𝟙 X) (Spec.map (S.residue (genericPoint S))) (𝟙 S)
      (by rw [Category.id_comp, Category.comp_id])
      (by rw [Category.comp_id, Scheme.fromSpecResidueField]) = ι₀ at hι₀ hι₀fst
  haveI : IsIso (X := f.fiber (genericPoint S)) (Y := (preimageSpecStalkCone f (genericPoint S)).pt)
      ι₀ := hι₀
  refine (IsLimit.extendIso (s := preimageSpecStalkCone f (genericPoint S))
    (X := f.fiber (genericPoint S)) ι₀ (isLimitPreimageSpecStalkCone f (genericPoint S))).ofIsoLimit
    (Cones.ext (Iso.refl _) fun W ↦ ?_)
  refine Eq.trans ?_ (Category.id_comp _).symm
  exact (cancel_mono (f ⁻¹ᵁ W.opens).ι).mp <| ((Category.assoc ι₀ _ _).trans
    ((congrArg (ι₀ ≫ ·) (preimageSpecStalkLeg_ι f (genericPoint S) W)).trans hι₀fst)).trans
    (genericFiberToPreimage_ι f W.opens W.mem_opens).symm

/-- **The generic Galois cover spreads out.** Let `S` be an integral scheme with generic point
`η` and `f : X ⟶ S` quasi-compact, quasi-separated, flat and locally of finite presentation. A
finite étale Galois cover of the generic fibre `X_η` with group `G` is, equivariantly, the
restriction of a finite étale Galois cover of `f⁻¹(U)` with group `G`, for some open
neighbourhood `U` of `η`. -/
theorem exists_galoisExtendsOver_of_flat [QuasiCompact f] [QuasiSeparated f] [Flat f]
    [LocallyOfFinitePresentation f] (G : Type v) [Group G] [Finite G]
    (Z : FiniteEtaleGaloisCover (f.fiber (genericPoint S)) G) :
    ∃ U : S.Opens, GaloisExtendsOver f Z U := by
  obtain ⟨W, V, act, P, hP, hact, hiso⟩ := @GaloisCoverLimits.exists_torsor_model _ _
    (preimageAffineOpenNhdsDiagram f (genericPoint S)) (genericFiberCone f) _ _ _ _
    (isLimitGenericFiberCone f) G _ _ Z.obj Z.action Z.comparisonIsIso
  have : ConnectedSpace ((𝟭 Scheme).obj Z.obj.left) := Z.connected
  have hconn : ConnectedSpace V.left :=
    connectedSpace_of_isPullback_genericFiberToPreimage f W.opens W.mem_opens V Z.obj.hom P hP
  let Y : FiniteEtaleGaloisCover (f ⁻¹ᵁ W.opens).toScheme G :=
    { obj := V, connected := hconn, action := act, comparisonIsIso := hiso }
  obtain ⟨e, he⟩ := GaloisCoverLimits.exists_equivariant_iso_of_isPullback
    (genericFiberToPreimage f W.opens W.mem_opens) V Z.obj P hP (fun g ↦ (act g).hom)
    (fun g ↦ (Z.action g).hom) hact
  exact ⟨W.opens, W.mem_opens, Y, e, he⟩

/-- **The generic Galois cover extends over an open neighbourhood of `η`**, the first step of
the maximal-open argument in the proof of [Stacks, Tag 0EYJ]. Let `S` be an integral normal
Noetherian scheme with generic point `η`, `f : X ⟶ S` a quasi-compact smooth morphism with
geometrically connected fibres and a section `σ`, and `Z ⟶ X_η` a finite étale Galois cover with
group `G` of order invertible on `S` with a `κ(η)`-point over `σ(η)`. Then `Z` is, equivariantly,
the restriction of a finite étale Galois cover of `f⁻¹(U)` with group `G` for some open `U ∋ η`.

Only quasi-compactness, flatness and local finite presentation of `f` are used.

SOURCE GAP: the proof of Tag 0EYJ starts from "a maximal open `U` over which `Z` extends" and so
takes this step for granted. Spreading out needs `f` quasi-compact, and a smooth morphism with
geometrically connected fibres need not be: `S ×_k L`, for `L` the affine line with infinitely
many origins, is a counterexample to quasi-compactness. Charts of `X_η` then spread out over
opens of `S` with no common open neighbourhood of `η` in general. Here the step is proved for
quasi-compact `f`, and Tag 0EYJ for general `f` is reduced to the quasi-compact case. -/
theorem exists_galoisExtendsOver {S X : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsIntegral S]
    [IsNormal S] [QuasiCompact f] [Smooth f] [GeometricallyConnected f]
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (G : Type v) [Group G] [Finite G]
    (_ : ∀ s : S, IsUnit (Nat.card G : S.residueField s))
    (Z : FiniteEtaleGaloisCover (f.fiber (genericPoint S)) G)
    (z : Spec (S.residueField (genericPoint S)) ⟶ Z.obj.left)
    (_ : z ≫ Z.obj.hom = genericFiberSection f σ hσ) :
    ∃ U : S.Opens, GaloisExtendsOver f Z U := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  exact exists_galoisExtendsOver_of_flat f G Z

end Abhyankar

end AlgebraicGeometry
