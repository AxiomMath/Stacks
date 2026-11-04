module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FibreSupportDimension
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformFlatnessShortExact
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformFlatnessTransport

/-!
# Flattening neighbourhoods

The induction of [Stacks, Tag 0815] is run point by point on the source: around each `x : X` one
produces a quasi-compact étale neighbourhood `V ⟶ S` of the base, an étale neighbourhood
`U ⟶ X` of `x`, a morphism `U ⟶ V` over `S`, and a centre on `V` which is of finite
presentation, disjoint from the preimage of the open `U ⊆ S` over which flatness is already
known, and which flattens the strict transform of the pullback of `F` to `U`. These data are
packaged as `AlgebraicGeometry.FlatteningNeighborhood`, so that the étale-local-to-global step
of [Stacks, Tag 0814] consumes a single object rather than a nest of existentials.

## Main definitions

* `AlgebraicGeometry.FlatteningNeighborhood`: the data of a flattening neighbourhood at a point.

## Main results

* `AlgebraicGeometry.nonempty_flatteningNeighborhood_of_notMem_supp`: a flattening neighbourhood
  exists at a point outside the support of `F`.
* `AlgebraicGeometry.nonempty_flatteningNeighborhood_of_elementaryDevissage`: a flattening
  neighbourhood exists given an elementary dévissage and a flattening centre for it.
* `AlgebraicGeometry.nonempty_flatteningNeighborhood_of_oneStepDevissage`: a flattening
  neighbourhood exists given a one-step dévissage and a flattening centre for it.

## Implementation notes

The strict transform used is `Stacks.StrictTransform.sheaf` at `b = AlgebraicGeometry.blowUpToBase`
and `E = AlgebraicGeometry.exceptionalIdeal`, the setting in which [Stacks, Tag 080F] and
[Stacks, Tag 080I] are stated.

Finite presentation of the centre is `AlgebraicGeometry.FinitePresentation` of its closed
immersion, the predicate of [Stacks, Tag 01TP], as in `Stacks.Blowup.IsAdmissibleBlowup`.

## References

* [Stacks Project, Tag 0814](https://stacks.math.columbia.edu/tag/0814)
* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A **flattening neighbourhood** of `f : X ⟶ S`, a module `F` on `X` and an open `U ⊆ S` at a
point `x : X`: a quasi-compact étale neighbourhood `base ⟶ S`, an étale neighbourhood
`source ⟶ X` of `x`, a morphism `source ⟶ base` over `S`, and a centre on `base` which is of
finite presentation, supported away from the preimage of `U`, and whose blowup flattens the
strict transform of the pullback of `F` to `source`.

This is one point's worth of the local input to the étale-local flattening statement
[Stacks, Tag 0814]. -/
structure FlatteningNeighborhood {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    [F.IsQuasicoherent] (U : S.Opens) (x : X) where
  /-- The étale neighbourhood of the base. -/
  base : Scheme.{u}
  /-- The étale neighbourhood of the source. -/
  source : Scheme.{u}
  /-- The structure morphism of the étale neighbourhood of the base. -/
  toBase : base ⟶ S
  /-- The structure morphism of the étale neighbourhood of the source. -/
  toSource : source ⟶ X
  /-- The morphism of neighbourhoods over `S`, the local replacement of `f`. -/
  map : source ⟶ base
  /-- The distinguished point of the neighbourhood of the source. -/
  point : source
  /-- The distinguished point maps to `x`. -/
  point_eq : toSource point = x
  /-- The neighbourhood of the base is étale over `S`. -/
  etale_base : Etale toBase
  /-- The neighbourhood of the base is quasi-compact over `S`. -/
  quasiCompact_base : QuasiCompact toBase
  /-- The neighbourhood of the source is étale over `X`. -/
  etale_source : Etale toSource
  /-- The morphism `map` lies over `f`. -/
  commutes : toSource ≫ f = map ≫ toBase
  /-- The centre to be blown up on the neighbourhood of the base. -/
  center : base.IdealSheafData
  /-- The centre is of finite presentation and its support is disjoint from the preimage of `U`. -/
  admissible : FinitePresentation center.subschemeι ∧
    Disjoint (toBase ⁻¹ᵁ U : Set base) (center.support : Set base)
  /-- The strict transform of the pullback of `F` to `source` under the blowup of `center` is
  flat over the blowup of `base`. -/
  flat :
    IsFlatOver (pullback.snd map (blowUpToBase center)).toLRSHom.toShHom
      (Stacks.StrictTransform.sheaf map (blowUpToBase center) (exceptionalIdeal center)
        ((Scheme.Modules.pullback toSource).obj F))

/-! ### Away from the support -/

/-- **A flattening neighbourhood exists at a point outside the support.** No blowup is needed:
the complement of the support of `F` is an open neighbourhood of `x` on which the pullback of `F`
is already flat over `S` ([Stacks, Tag 056J] computes its support), so the empty centre does the
job by `AlgebraicGeometry.isFlatOver_strictTransformSheaf_of_isFlatOver`. -/
theorem nonempty_flatteningNeighborhood_of_notMem_supp {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (U : S.Opens) (x : X)
    (hx : x ∉ SheafOfModules.supp F) :
    Nonempty (FlatteningNeighborhood f F U x) := by
  let W : X.Opens :=
    ⟨(SheafOfModules.supp F)ᶜ, (SheafOfModules.isClosed_supp F).isOpen_compl⟩
  let G := (Scheme.Modules.pullback W.ι).obj F
  have : G.IsQuasicoherent :=
    @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
      W.ι.toLRSHom.toShHom F ‹F.IsQuasicoherent›
  have hG : IsFlatOver (W.ι ≫ f).toLRSHom.toShHom G := fun y ↦
    isFlatOverAt_of_notMem_supp _ _ _ (by rw [Stacks.Modules.supp_pullback]; exact y.2)
  exact ⟨{
    base := S
    source := W.toScheme
    toBase := 𝟙 S
    toSource := W.ι
    map := W.ι ≫ f
    point := ⟨x, hx⟩
    point_eq := rfl
    etale_base := inferInstance
    quasiCompact_base := inferInstance
    etale_source := inferInstance
    commutes := by simp
    center := ⊤
    admissible := ⟨⟨inferInstance, inferInstance, inferInstance⟩, by simp⟩
    flat := isFlatOver_strictTransformSheaf_of_isFlatOver (W.ι ≫ f) ⊤ G hG }⟩

/-! ### From a dévissage -/

/-- If `i : Z ⟶ X` and `π : Z ⟶ Y` are affine and the strict transform of `π_* G` is flat over the
blowup of the base, then so is the strict transform of any module isomorphic to `i_* G`. -/
private theorem isFlatOver_strictTransformSheaf_of_pushforward_iso {Z X Y S : Scheme.{u}}
    (i : Z ⟶ X) (π : Z ⟶ Y) (h : X ⟶ S) (g : Y ⟶ S) [IsAffineHom i] [IsAffineHom π]
    (hcomm : i ≫ h = π ≫ g) (I : S.IdealSheafData) (G : Z.Modules) [G.IsQuasicoherent]
    {F : X.Modules} (e : (Scheme.Modules.pushforward i).obj G ≅ F)
    (hM : IsFlatOver (pullback.snd g (blowUpToBase I)).toLRSHom.toShHom
      (Stacks.StrictTransform.sheaf g (blowUpToBase I) (exceptionalIdeal I)
        ((Scheme.Modules.pushforward π).obj G))) :
    IsFlatOver (pullback.snd h (blowUpToBase I)).toLRSHom.toShHom
      (Stacks.StrictTransform.sheaf h (blowUpToBase I) (exceptionalIdeal I) F) := by
  refine isFlatOver_strictTransformSheaf_of_iso h I e
    ((isFlatOver_strictTransformSheaf_iff_pushforward i h I G).mp ?_)
  rw [hcomm]
  exact (isFlatOver_strictTransformSheaf_iff_pushforward π g I G).mpr hM

/-- **A flattening neighbourhood from an elementary dévissage.** An elementary dévissage of `F`
at `x` supplies the two étale neighbourhoods and the morphism between them; a centre on the
neighbourhood of the base which flattens the strict transform of the module pushed to the smooth
scheme `Y` then flattens the strict transform of the pullback of `F`, because flatness of a
strict transform is unchanged by direct image along an affine morphism
(`AlgebraicGeometry.isFlatOver_strictTransformSheaf_iff_pushforward`, applied to the finite
morphism `Z ⟶ Y` and to the closed immersion `Z ⟶ U`) and by an isomorphism of the module
(`AlgebraicGeometry.isFlatOver_strictTransformSheaf_of_iso`, applied to the dévissage's
identification of the direct image with the pullback of `F`). -/
theorem nonempty_flatteningNeighborhood_of_elementaryDevissage {X S : Scheme.{u}}
    [QuasiSeparatedSpace S] (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent] (U : S.Opens)
    (x : X)
    (hx : f.asFiber x ∈
      SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
    (D : ElementaryDevissage f F x hx)
    (hflat : ∃ I : D.V.scheme.IdealSheafData,
      (FinitePresentation I.subschemeι ∧
        Disjoint (D.V.toBase ⁻¹ᵁ U : Set D.V.scheme) (I.support : Set D.V.scheme)) ∧
      IsFlatOver (pullback.snd D.h (blowUpToBase I)).toLRSHom.toShHom
        (Stacks.StrictTransform.sheaf D.h (blowUpToBase I) (exceptionalIdeal I)
          ((Scheme.Modules.pushforward D.π).obj D.G))) :
    Nonempty (FlatteningNeighborhood f F U x) := by
  have := D.quasicoherent_G
  have := D.finite_π
  have := D.closedImmersion
  have := D.affine_V
  obtain ⟨I, hI, hM⟩ := hflat
  exact ⟨{
    base := D.V.scheme
    source := D.U.scheme
    toBase := D.V.toBase
    toSource := D.U.toBase
    map := D.toBase
    point := D.U.point
    point_eq := D.U.map_point
    etale_base := inferInstance
    quasiCompact_base := inferInstance
    etale_source := inferInstance
    commutes := D.commutes_base
    center := I
    admissible := hI
    flat := isFlatOver_strictTransformSheaf_of_pushforward_iso D.i D.π D.toBase D.h
      D.commutes_closed I D.G D.sheafIso hM }⟩

/-- **A flattening neighbourhood from a one-step dévissage.** The same argument as
`AlgebraicGeometry.nonempty_flatteningNeighborhood_of_elementaryDevissage`, run on a one-step
dévissage of the pullback of `F` to a given étale neighbourhood of `x` over a given étale
neighbourhood of `f x`: the dévissage supplies the closed subscheme finite over the smooth
scheme, and its identification of the pullback of `F` with the direct image transports flatness
of the strict transform back. -/
theorem nonempty_flatteningNeighborhood_of_oneStepDevissage {X S : Scheme.{u}}
    [QuasiSeparatedSpace S] (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent] (U : S.Opens)
    (x : X) (A : EtaleNeighborhood X x) (B : EtaleNeighborhood S (f x))
    (h : A.scheme ⟶ B.scheme) (hcomm : A.toBase ≫ f = h ≫ B.toBase)
    (hft : LocallyOfFiniteType h)
    (hQqc : ((Scheme.Modules.pullback A.toBase).obj F).IsQuasicoherent)
    (hQft : ((Scheme.Modules.pullback A.toBase).obj F).IsFiniteType)
    (D : letI : LocallyOfFiniteType h := hft
      letI : ((Scheme.Modules.pullback A.toBase).obj F).IsQuasicoherent := hQqc
      letI : ((Scheme.Modules.pullback A.toBase).obj F).IsFiniteType := hQft
      OneStepDevissage h ((Scheme.Modules.pullback A.toBase).obj F) B.point)
    (hflat : ∃ I : B.scheme.IdealSheafData,
      (FinitePresentation I.subschemeι ∧
        Disjoint (B.toBase ⁻¹ᵁ U : Set B.scheme) (I.support : Set B.scheme)) ∧
      IsFlatOver (pullback.snd D.g (blowUpToBase I)).toLRSHom.toShHom
        (Stacks.StrictTransform.sheaf D.g (blowUpToBase I) (exceptionalIdeal I)
          ((Scheme.Modules.pushforward D.π).obj D.G))) :
    Nonempty (FlatteningNeighborhood f F U x) := by
  have : LocallyOfFiniteType h := hft
  have : ((Scheme.Modules.pullback A.toBase).obj F).IsQuasicoherent := hQqc
  have : ((Scheme.Modules.pullback A.toBase).obj F).IsFiniteType := hQft
  have : D.G.IsQuasicoherent := D.quasi_coherent_G
  have : IsFinite D.π := D.finite
  have : IsClosedImmersion D.i := D.closed_immersion
  have : IsAffine B.scheme := D.affine_S
  obtain ⟨I, hI, hM⟩ := hflat
  exact ⟨{
    base := B.scheme
    source := A.scheme
    toBase := B.toBase
    toSource := A.toBase
    map := h
    point := A.point
    point_eq := A.map_point
    etale_base := inferInstance
    quasiCompact_base := inferInstance
    etale_source := inferInstance
    commutes := hcomm
    center := I
    admissible := hI
    flat := isFlatOver_strictTransformSheaf_of_pushforward_iso D.i D.π h D.g
      D.over_base I D.G D.module_iso.symm hM }⟩

end AlgebraicGeometry

end
