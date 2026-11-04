module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.Etale.LiftAcrossClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Etale.NeighborhoodStalkFiber
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteOverSmoothAffine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FiniteTypeModuleLocalStructure
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# Elementary dévissage of a finite-type quasi-coherent module

Let `f : X ⟶ S` be locally of finite type, let `F` be a finite-type quasi-coherent
`𝒪_X`-module, and let `x` be a point of `X` lying in the support of the restriction of `F` to
the fibre of `f` through `x`. Then, after elementary étale neighbourhoods `U` of `(X, x)` and
`V` of `(S, f x)`, the pullback of `F` to `U` is the direct image of a finite-type
quasi-coherent module from a finitely presented closed subscheme `Z ⊆ U`, and `Z` is finite
over a scheme `Y` smooth over `V` of relative dimension the local dimension of the support,
with geometrically integral fibres. All four of `U`, `V`, `Z`, `Y` are affine. That is
Stacks 057S.

## Main definitions

* `AlgebraicGeometry.ElementaryDevissage`: the whole diagram, its module and all its
  properties, packaged so that later statements can refer to one chosen construction.

## Main results

* `AlgebraicGeometry.exists_elementaryDevissage` is Stacks 057S.
* `AlgebraicGeometry.ElementaryDevissage.preimage_i_singleton` and
  `AlgebraicGeometry.ElementaryDevissage.preimage_π_singleton` record that the closed immersion
  and the finite morphism of a dévissage both have singleton fibre over the distinguished point,
  which is what the transfer lemmas of Stacks 057T and Stacks 057U are applied through.

## Implementation notes

The proof follows the source in three steps.

The first step is the case where the support of the fibre module is the whole fibre. Then
`AlgebraicGeometry.exists_finite_over_smooth_affine` (Stacks 057L) already gives everything,
with `Z = U` and `i = 𝟙`.

The second step is the affine case. Stacks 057Q
(`AlgebraicGeometry.exists_finitePresentation_closedSubscheme_fiber_eq_supp`) produces a
finitely presented closed immersion `i : Z ⟶ X` and a module `G` on `Z` with `i_* G ≅ F` whose
fibre is the support; applying Stacks 057L to `Z ⟶ S` and `G` gives the dévissage of `G`, whose
source étale neighbourhood lives over `Z` rather than over `X`. Stacks 057R
(`Stacks.Etale.exists_etale_lift_of_isClosedImmersion`) lifts it across the closed immersion
`Z ×_S V ⟶ X ×_S V`, which is where the affineness hypotheses of 057L are used.

The third step reduces the general case to the affine one by restricting to affine opens
`U ⊆ f⁻¹(V)` and `V ⊆ S` around `x` and `f x`, and then composing the resulting étale
neighbourhoods with the two open immersions. That the local dimension of the support is
unchanged by this restriction is
`AlgebraicGeometry.ElementaryDevissage.topologicalKrullDimAt_supp_resLE`, which identifies the
fibre of the restricted morphism with an open subspace of the original fibre.

The dimension bookkeeping in the affine step is the comparison between the local dimension of
the support of the fibre module, taken at the point of the fibre of `f`, and the local
dimension of the fibre of `i ≫ f`: the two are identified by
`AlgebraicGeometry.ElementaryDevissage.topologicalKrullDimAt_fiber_eq_supp`, using that the
image of the fibre of `i ≫ f` is the image of the support.

## References

* [Stacks Project, Tag 057S](https://stacks.math.columbia.edu/tag/057S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.AffineBaseChangeIso Stacks.AlgebraicGeometry.AffinePushforward

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 057S.** An *elementary dévissage* of a finite-type quasi-coherent
module `F` along `f : X ⟶ S` at a point `x` of the support of its fibre: elementary étale
neighbourhoods `U` of `(X, x)` and `V` of `(S, f x)`, a finitely presented closed immersion
`i : Z ⟶ U` with a module `G` whose direct image is the pullback of `F`, and a factorisation of
`Z ⟶ V` as a finite morphism to a smooth `V`-scheme `Y` with geometrically integral fibres.

The data are recorded as a structure rather than existentially quantified so that later
statements can refer to one chosen construction. -/
structure ElementaryDevissage {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    (hx : f.asFiber x ∈
      SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)) where
  /-- The relative dimension of the smooth morphism. -/
  n : ℕ
  /-- It is the local dimension of the support of the fibre module at `x`. -/
  dimension : topologicalKrullDimAt
    (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
      ⟨f.asFiber x, hx⟩ = n
  /-- The elementary étale neighbourhood of the source. -/
  U : EtaleNeighborhood X x
  /-- The elementary étale neighbourhood of the base. -/
  V : EtaleNeighborhood S (f x)
  elementary_U : U.IsElementary
  elementary_V : V.IsElementary
  /-- The closed subscheme of the source neighbourhood carrying the module. -/
  Z : Scheme.{u}
  /-- The smooth scheme over the base neighbourhood. -/
  Y : Scheme.{u}
  /-- The structure morphism of the source neighbourhood over the base neighbourhood. -/
  toBase : U.scheme ⟶ V.scheme
  /-- The closed immersion. -/
  i : Z ⟶ U.scheme
  /-- The finite morphism. -/
  π : Z ⟶ Y
  /-- The smooth morphism. -/
  h : Y ⟶ V.scheme
  /-- The distinguished point of the closed subscheme. -/
  z : Z
  /-- The module on the closed subscheme. -/
  G : Z.Modules
  commutes_base : U.toBase ≫ f = toBase ≫ V.toBase
  commutes_closed : i ≫ toBase = π ≫ h
  point_closed : i z = U.point
  point_base : h (π z) = V.point
  affine_U : IsAffine U.scheme
  affine_V : IsAffine V.scheme
  affine_Z : IsAffine Z
  affine_Y : IsAffine Y
  closedImmersion : IsClosedImmersion i
  finitePresentation : FinitePresentation i
  /-- The direct image of the module is the pullback of `F`. -/
  sheafIso : (Scheme.Modules.pushforward i).obj G ≅
    (Scheme.Modules.pullback U.toBase).obj F
  finiteType_G : G.IsFiniteType
  quasicoherent_G : G.IsQuasicoherent
  finite_π : IsFinite π
  singleton_fiber : ∀ z' : Z, π z' = π z ↔ z' = z
  /-- The residue field of `Y` at `π z` is purely transcendental over the residue field of the
  base neighbourhood at its point. -/
  pureTranscendental :
    letI : Algebra (V.scheme.residueField V.point) (Y.residueField (π z)) :=
      ((V.scheme.residueFieldCongr point_base).inv ≫ h.residueFieldMap (π z)).hom.toAlgebra
    PurelyTranscendental (V.scheme.residueField V.point) (Y.residueField (π z))
  /-- The morphism `h : Y ⟶ V` is smooth of relative dimension `n`. -/
  smooth : SmoothOfRelativeDimension n h
  /-- Every fibre of `h : Y ⟶ V` is geometrically integral. -/
  integral_fibers : ∀ s' : V.scheme, GeometricallyIntegral (h.fiberToSpecResidueField s')

namespace ElementaryDevissage

/-- A point of the support of the fibre module which is in the image of a closed subscheme whose
fibre has exactly that image lifts to a point of the closed subscheme. -/
private theorem exists_point_of_mem_supp {X S Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X)
    (F : X.Modules) (x : X)
    (hRange : Set.range (fun z : (i ≫ f).fiber (f x) => i ((i ≫ f).fiberι (f x) z)) =
      f.fiberι (f x) '' SheafOfModules.supp
        ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
    (hSupport : f.asFiber x ∈ SheafOfModules.supp
      ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)) :
    ∃ z : Z, i z = x ∧ (i ≫ f) z = f x := by
  have hxImage := Set.mem_image_of_mem (f.fiberι (f x)) hSupport
  rw [← hRange] at hxImage
  obtain ⟨w, hw⟩ := hxImage
  have hix : i ((i ≫ f).fiberι (f x) w) = x := by
    simpa only [Scheme.Hom.fiberι_asFiber] using hw
  exact ⟨(i ≫ f).fiberι (f x) w, hix, congrArg f hix⟩

/-- The restriction of a morphism locally of finite type to a pair of opens is locally of finite
type. -/
private lemma locallyOfFiniteType_resLE {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    (U : X.Opens) (hUV : U ≤ f ⁻¹ᵁ V) [LocallyOfFiniteType f] :
    LocallyOfFiniteType (f.resLE V U hUV) := by
  delta Scheme.Hom.resLE
  infer_instance

/-- The inclusions of open subschemes commute with a restricted morphism on points. -/
private lemma ι_resLE_apply {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) (U : X.Opens)
    (hUV : U ≤ f ⁻¹ᵁ V) (y : U.toScheme) : V.ι (f.resLE V U hUV y) = f (U.ι y) := by
  have := congrArg (fun q : U.toScheme ⟶ S => q y) (Scheme.Hom.resLE_comp_ι f (e := hUV))
  simpa only [Scheme.Hom.comp_apply] using this

/-- The pullback of a finite-type quasi-coherent module is finite-type and quasi-coherent. -/
private theorem pullback_isFiniteType_and_isQuasicoherent {X Y : Scheme.{u}} (g : X ⟶ Y)
    (F : Y.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    ((Scheme.Modules.pullback g).obj F).IsFiniteType ∧
      ((Scheme.Modules.pullback g).obj F).IsQuasicoherent :=
  ⟨SheafOfModules.pullback_isFiniteType g.toLRSHom.toShHom F,
    @SheafOfModules.modulePullback_isQuasicoherent _ _ g.toLRSHom.toShHom F
      ‹F.IsQuasicoherent›⟩

/-- The base change of a morphism of finite presentation is of finite presentation. -/
private theorem finitePresentation_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback fst snd f g)
    (hf : FinitePresentation f) : FinitePresentation snd :=
  ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback sq hf.1,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq hf.2.1,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq hf.2.2⟩

/-- Restricting to affine opens around a point and its image does not change the local
dimension of the support of the fibre module: the fibre of the restricted morphism is an open
subspace of the original fibre, and the supports correspond. -/
private theorem topologicalKrullDimAt_supp_resLE {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    [F.IsFiniteType] (x : X) (U : X.Opens) (V : S.Opens) (hxU : x ∈ U) (hUV : U ≤ f ⁻¹ᵁ V)
    (hx : f.asFiber x ∈ SheafOfModules.supp
      ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)) :
    let f' := f.resLE V U hUV
    let x' : U.toScheme := ⟨x, hxU⟩
    let F' := (Scheme.Modules.pullback U.ι).obj F
    let T' := SheafOfModules.supp
      ((Scheme.Modules.pullback (f'.fiberι (f' x'))).obj F')
    ∃ hx' : f'.asFiber x' ∈ T',
      topologicalKrullDimAt T' ⟨f'.asFiber x', hx'⟩ =
        topologicalKrullDimAt
          (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
          ⟨f.asFiber x, hx⟩ := by
  let jX : U.toScheme ⟶ X := U.ι
  let jS : V.toScheme ⟶ S := V.ι
  let f' : U.toScheme ⟶ V.toScheme := f.resLE V U hUV
  let x' : U.toScheme := ⟨x, hxU⟩
  let T := SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)
  let F' := (Scheme.Modules.pullback jX).obj F
  have : F'.IsFiniteType := SheafOfModules.pullback_isFiniteType jX.toLRSHom.toShHom F
  let T' := SheafOfModules.supp ((Scheme.Modules.pullback (f'.fiberι (f' x'))).obj F')
  have hfac : f' ≫ jS = jX ≫ f := Scheme.Hom.resLE_comp_ι f (e := hUV)
  have hs : jS (f' x') = f x := ι_resLE_apply f V U hUV x'
  let jSpecMap : S.residueField (f x) ⟶ V.toScheme.residueField (f' x') :=
    (S.residueFieldCongr hs).inv ≫ jS.residueFieldMap (f' x')
  have hjSpecMap : V.toScheme.fromSpecResidueField (f' x') ≫ jS =
      Spec.map jSpecMap ≫ S.fromSpecResidueField (f x) := by
    have hres : Spec.map ((S.residueFieldCongr hs).inv) ≫ S.fromSpecResidueField (f x) =
        S.fromSpecResidueField (jS (f' x')) := by
      rw [Scheme.residueFieldCongr_inv]
      exact Scheme.residueFieldCongr_fromSpecResidueField hs.symm
    calc
      V.toScheme.fromSpecResidueField (f' x') ≫ jS =
          Spec.map (jS.residueFieldMap (f' x')) ≫ S.fromSpecResidueField (jS (f' x')) :=
        (jS.SpecMap_residueFieldMap_fromSpecResidueField (f' x')).symm
      _ = Spec.map (jS.residueFieldMap (f' x')) ≫
            (Spec.map ((S.residueFieldCongr hs).inv) ≫ S.fromSpecResidueField (f x)) := by
        rw [hres]
      _ = (Spec.map (jS.residueFieldMap (f' x')) ≫
            Spec.map ((S.residueFieldCongr hs).inv)) ≫ S.fromSpecResidueField (f x) := by
        simp [Category.assoc]
      _ = Spec.map ((S.residueFieldCongr hs).inv ≫ jS.residueFieldMap (f' x')) ≫
            S.fromSpecResidueField (f x) := by rw [← Spec.map_comp]
      _ = Spec.map jSpecMap ≫ S.fromSpecResidueField (f x) := rfl
  let jFib : f'.fiber (f' x') ⟶ f.fiber (f x) :=
    pullback.map f' (V.toScheme.fromSpecResidueField (f' x')) f (S.fromSpecResidueField (f x))
      jX (Spec.map jSpecMap) jS hfac hjSpecMap
  have hjFib : jFib ≫ f.fiberι (f x) = f'.fiberι (f' x') ≫ jX := by
    show pullback.lift
        (pullback.fst f' (V.toScheme.fromSpecResidueField (f' x')) ≫ jX)
        (pullback.snd f' (V.toScheme.fromSpecResidueField (f' x')) ≫ Spec.map jSpecMap) _ ≫
      pullback.fst f (S.fromSpecResidueField (f x)) = _
    exact pullback.lift_fst _ _ _
  let A : Set U.toScheme := f' ⁻¹' {f' x'}
  let B : Set X := f ⁻¹' {f x}
  let eLocal : f'.fiber (f' x') ≃ₜ A := f'.fiberHomeo (f' x')
  let eGlobal : f.fiber (f x) ≃ₜ B := f.fiberHomeo (f x)
  have hAB : jX.base ⁻¹' B = A := by
    ext y
    show f (jX y) = f x ↔ f' y = f' x'
    have hfacAt : jS (f' y) = f (jX y) := ι_resLE_apply f V U hUV y
    constructor
    · intro hy
      apply jS.isEmbedding.injective
      calc
        jS (f' y) = f (jX y) := hfacAt
        _ = f x := hy
        _ = jS (f' x') := hs.symm
    · intro hy
      calc
        f (jX y) = jS (f' y) := hfacAt.symm
        _ = jS (f' x') := congrArg jS hy
        _ = f x := hs
  let qA : A ≃ₜ (jX.base ⁻¹' B) := Homeomorph.setCongr hAB.symm
  let k : A → B := fun a => B.restrictPreimage jX.base (qA a)
  have hk : Topology.IsOpenEmbedding k :=
    (B.restrictPreimage_isOpenEmbedding jX.isOpenEmbedding).comp qA.isOpenEmbedding
  have hmap : (fun y : f'.fiber (f' x') => jFib y) = fun y => eGlobal.symm (k (eLocal y)) := by
    funext y
    apply eGlobal.injective
    rw [eGlobal.apply_symm_apply]
    apply Subtype.ext
    show f.fiberι (f x) (jFib y) = jX (f'.fiberι (f' x') y)
    have hh := congrArg (fun q : f'.fiber (f' x') ⟶ X => q y) hjFib
    simpa only [Scheme.Hom.comp_apply] using hh
  have hjFibEmbedding : Topology.IsOpenEmbedding (fun y : f'.fiber (f' x') => jFib y) := by
    rw [hmap]
    exact eGlobal.symm.isOpenEmbedding.comp (hk.comp eLocal.isOpenEmbedding)
  have hpt : jFib (f'.asFiber x') = f.asFiber x := by
    apply (f.fiberι (f x)).isEmbedding.injective
    have hh := congrArg (fun q : f'.fiber (f' x') ⟶ X => q (f'.asFiber x')) hjFib
    change f.fiberι (f x) (jFib (f'.asFiber x')) =
      jX (f'.fiberι (f' x') (f'.asFiber x')) at hh
    rw [Scheme.Hom.fiberι_asFiber] at hh
    have hh' : f.fiberι (f x) (jFib (f'.asFiber x')) = x := by simpa [x', jX] using hh
    simpa [Scheme.Hom.fiberι_asFiber] using hh'
  have hT : T' = jFib ⁻¹' T := by
    show SheafOfModules.supp ((Scheme.Modules.pullback (f'.fiberι (f' x'))).obj F') =
      jFib ⁻¹' SheafOfModules.supp
        ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)
    rw [Stacks.Modules.supp_pullback (f'.fiberι (f' x')) F',
      Stacks.Modules.supp_pullback jX F, Stacks.Modules.supp_pullback (f.fiberι (f x)) F]
    ext y
    simp only [Set.mem_preimage]
    have hh := congrArg (fun q : f'.fiber (f' x') ⟶ X => q y) hjFib
    change f.fiberι (f x) (jFib y) = jX (f'.fiberι (f' x') y) at hh
    exact Iff.of_eq (congrArg (fun p : X => p ∈ SheafOfModules.supp F) hh).symm
  have hmem : f'.asFiber x' ∈ T' := by
    rw [hT]
    simpa [hpt] using hx
  refine ⟨hmem, ?_⟩
  show topologicalKrullDimAt T' ⟨f'.asFiber x', hmem⟩ =
    topologicalKrullDimAt T ⟨f.asFiber x, hx⟩
  have hmem' : f'.asFiber x' ∈ jFib ⁻¹' T := by
    show jFib (f'.asFiber x') ∈ T
    rw [hpt]
    exact hx
  calc
    topologicalKrullDimAt T' ⟨f'.asFiber x', hmem⟩ =
        topologicalKrullDimAt (jFib ⁻¹' T) ⟨f'.asFiber x', hmem'⟩ :=
      topologicalKrullDimAt_eq_of_homeomorph (Homeomorph.setCongr hT) _
    _ = topologicalKrullDimAt T ⟨jFib (f'.asFiber x'), hmem'⟩ :=
      ((hjFibEmbedding.restrictPreimage T).topologicalKrullDimAt_eq
        ⟨f'.asFiber x', hmem'⟩).symm
    _ = topologicalKrullDimAt T ⟨f.asFiber x, hx⟩ :=
      congrArg (topologicalKrullDimAt T) (Subtype.ext hpt)

/-- If the image of the fibre of `i ≫ f` through a closed immersion `i` is the image of a subset
`T` of the fibre of `f`, then the local dimension of `T` at a point of `T` is the local
dimension of the fibre of `i ≫ f` at a preimage of that point. -/
theorem topologicalKrullDimAt_fiber_eq_supp {X S Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X)
    [IsClosedImmersion i] (x : X) (T : Set (f.fiber (f x)))
    (hRange : Set.range (fun z : (i ≫ f).fiber (f x) => i ((i ≫ f).fiberι (f x) z)) =
      f.fiberι (f x) '' T)
    (hx : f.asFiber x ∈ T) (z : Z) (hiz : i z = x) :
    topologicalKrullDimAt T ⟨f.asFiber x, hx⟩ =
      topologicalKrullDimAt ((i ≫ f).fiber (f x))
        (((i ≫ f).fiberHomeo (f x)).symm ⟨z, by simp [hiz]⟩) := by
  let g := i ≫ f
  let A : Set Z := g ⁻¹' {f x}
  let B : Set X := f ⁻¹' {f x}
  let k : A → B := B.restrictPreimage i.base
  have hk : Topology.IsEmbedding k := i.isClosedEmbedding.isEmbedding.restrictPreimage B
  let T' : Set B := f.fiberHomeo (f x) '' T
  have hkRange : Set.range k = T' := by
    apply Set.ext
    intro y
    constructor
    · rintro ⟨a, rfl⟩
      have hm : i a.1 ∈ Set.range (fun w : g.fiber (f x) => i (g.fiberι (f x) w)) :=
        ⟨(g.fiberHomeo (f x)).symm a, by simp [Scheme.Hom.fiberι_fiberHomeo_symm]⟩
      obtain ⟨t, ht, hty⟩ := (Set.mem_image _ _ _).mp (hRange ▸ hm)
      refine ⟨t, ht, ?_⟩
      apply Subtype.ext
      show f.fiberι (f x) t = i a.1
      exact hty
    · rintro ⟨t, ht, rfl⟩
      have hm : f.fiberι (f x) t ∈
          Set.range (fun w : g.fiber (f x) => i (g.fiberι (f x) w)) := by
        rw [hRange]
        exact Set.mem_image_of_mem _ ht
      obtain ⟨w, hw⟩ := hm
      exact ⟨g.fiberHomeo (f x) w, Subtype.ext hw⟩
  let eSupport : T ≃ₜ T' := (f.fiberHomeo (f x)).subtype (by
    intro t
    constructor
    · intro ht
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t', ht', h⟩
      exact (f.fiberHomeo (f x)).injective h ▸ ht')
  let eClosed : A ≃ₜ T' := hk.toHomeomorph.trans (Homeomorph.setCongr hkRange)
  let H : g.fiber (f x) ≃ₜ T := (g.fiberHomeo (f x)).trans (eClosed.trans eSupport.symm)
  have hgz : g z = f x := by simp [g, hiz]
  let zf : g.fiber (f x) := (g.fiberHomeo (f x)).symm ⟨z, by simpa [A] using hgz⟩
  have hH : H zf = ⟨f.asFiber x, hx⟩ := by
    let a : A := ⟨z, by simpa [A] using hgz⟩
    have hzA : g.fiberHomeo (f x) zf = a := (g.fiberHomeo (f x)).apply_symm_apply a
    have hkz : k a = f.fiberHomeo (f x) (f.asFiber x) := by
      apply Subtype.ext
      show i z = f.fiberι (f x) (f.asFiber x)
      rw [Scheme.Hom.fiberι_asFiber]
      exact hiz
    have he : Homeomorph.setCongr hkRange (hk.toHomeomorph a) = eSupport ⟨f.asFiber x, hx⟩ :=
      Subtype.ext hkz
    calc
      H zf = eSupport.symm (eClosed a) := by simp [H, hzA, Homeomorph.trans_apply]
      _ = ⟨f.asFiber x, hx⟩ := by
        rw [show eClosed a = Homeomorph.setCongr hkRange (hk.toHomeomorph a) from rfl, he]
        exact eSupport.symm_apply_apply ⟨f.asFiber x, hx⟩
  rw [← hH]
  exact (topologicalKrullDimAt_eq_of_homeomorph H zf).symm

/-- Pure transcendence of the residue field extension at a point transfers along an equality of
points. -/
private theorem purelyTranscendental_residueField_congr {V Y : Scheme.{u}} (h : Y ⟶ V) (v : V)
    (z y : Y) (hz : h z = v) (hy : h y = v) (hzy : y = z) :
    letI : Algebra (V.residueField v) (Y.residueField z) :=
      ((V.residueFieldCongr hz).inv ≫ h.residueFieldMap z).hom.toAlgebra
    PurelyTranscendental (V.residueField v) (Y.residueField z) →
    letI : Algebra (V.residueField v) (Y.residueField y) :=
      ((V.residueFieldCongr hy).inv ≫ h.residueFieldMap y).hom.toAlgebra
    PurelyTranscendental (V.residueField v) (Y.residueField y) := by
  intro hpure
  cases hzy
  exact hpure

/-- The case of Stacks 057S where the support of the fibre module is the whole fibre: the
closed immersion is the identity and Stacks 057L gives the rest. -/
private theorem exists_of_supp_eq_univ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (x : X)
    (hx : f.asFiber x ∈
      SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
    (hSupp : SheafOfModules.supp
      ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) = Set.univ) :
    Nonempty (ElementaryDevissage f F x hx) := by
  obtain ⟨n, hn, U, V, Y, h, π, hUE, hVE, hcomm, hsmooth, hintegral,
      hfinite, hsingle, hpure, hfp, hVaff, hYaff, hUaff⟩ :=
    exists_finite_over_smooth_affine f x
  let G := (Scheme.Modules.pullback U.toBase).obj F
  obtain ⟨hGft, hGqc⟩ := pullback_isFiniteType_and_isQuasicoherent U.toBase F
  let e : SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) ≃ₜ
      f.fiber (f x) := (Homeomorph.setCongr hSupp).trans (Homeomorph.Set.univ _)
  have hpoint : e ⟨f.asFiber x, hx⟩ = f.asFiber x := by
    simp only [e, Homeomorph.trans_apply, Homeomorph.Set.univ_apply]
    rfl
  have hdim : topologicalKrullDimAt
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
      ⟨f.asFiber x, hx⟩ = n := by
    rw [topologicalKrullDimAt_eq_of_homeomorph e, hpoint]
    exact hn
  obtain ⟨heq, hpure⟩ := hpure
  exact ⟨{ n := n
           dimension := hdim
           U := U
           V := V
           elementary_U := hUE
           elementary_V := hVE
           Z := U.scheme
           Y := Y
           toBase := π ≫ h
           i := 𝟙 U.scheme
           π := π
           h := h
           z := U.point
           G := G
           commutes_base := by simpa using hcomm
           commutes_closed := by simp
           point_closed := by simp
           point_base := heq
           affine_U := hUaff
           affine_V := hVaff
           affine_Z := hUaff
           affine_Y := hYaff
           closedImmersion := inferInstance
           finitePresentation := ⟨inferInstance, inferInstance, inferInstance⟩
           sheafIso := (Scheme.Modules.pushforwardId U.scheme).app G
           finiteType_G := hGft
           quasicoherent_G := hGqc
           finite_π := hfinite
           singleton_fiber := hsingle
           pureTranscendental := hpure
           smooth := hsmooth
           integral_fibers := hintegral }⟩

/-- Stacks 057S for a morphism of affine schemes. -/
private theorem exists_of_isAffine {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine X] [IsAffine S]
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (x : X)
    (hx : f.asFiber x ∈
      SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)) :
    Nonempty (ElementaryDevissage f F x hx) := by
  classical
  obtain ⟨Z, i, G, eQ, hi, hfp, hGqc, hGft, hRange⟩ :=
    exists_finitePresentation_closedSubscheme_fiber_eq_supp f F (f x)
  have : G.IsFiniteType := hGft
  have : G.IsQuasicoherent := hGqc
  have : IsClosedImmersion i := hi
  have : IsAffineHom i := inferInstance
  have : IsAffine Z := isAffine_of_isAffineHom i
  let g : Z ⟶ S := i ≫ f
  have : LocallyOfFiniteType g := inferInstance
  obtain ⟨z, hiz, hgz⟩ := exists_point_of_mem_supp f i F x hRange hx
  subst x
  obtain ⟨n, hn, UZ, V, Y, h, π, hUE, hVE, hcomm, hsmooth, hintegral,
      hfinite, hsingle, hpure, hfpπ, hVaff, hYaff, hUZaff⟩ :=
    exists_finite_over_smooth_affine g z
  have hdim := topologicalKrullDimAt_fiber_eq_supp f i (i z)
    (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f (i z)))).obj F))
    hRange hx z rfl
  have hdim' : topologicalKrullDimAt
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f (i z)))).obj F))
        ⟨f.asFiber (i z), hx⟩ = n := by
    rw [hdim]
    have hbase : g z = f (i z) := rfl
    let eSet : (g ⁻¹' {g z}) ≃ₜ (g ⁻¹' {f (i z)}) := Homeomorph.setCongr (by ext y; simp [hbase])
    let H : g.fiber (g z) ≃ₜ g.fiber (f (i z)) :=
      (g.fiberHomeo (g z)).trans (eSet.trans (g.fiberHomeo (f (i z))).symm)
    have hcoe : (↑(g.fiberHomeo (g z) (g.asFiber z)) : Z) = z := by
      have h₁ := Scheme.Hom.fiberι_fiberHomeo_symm g (g z)
        (g.fiberHomeo (g z) (g.asFiber z))
      rw [Homeomorph.symm_apply_apply] at h₁
      rw [← h₁, Scheme.Hom.fiberι_asFiber]
    have hpt : H (g.asFiber z) = (g.fiberHomeo (f (i z))).symm ⟨z, by simp [hbase]⟩ := by
      rw [Homeomorph.eq_symm_apply]
      simp only [H, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
      exact Subtype.ext hcoe
    calc
      topologicalKrullDimAt (g.fiber (f (i z)))
          ((g.fiberHomeo (f (i z))).symm ⟨z, by simp [hbase]⟩) =
          topologicalKrullDimAt (g.fiber (g z)) (g.asFiber z) := by
            rw [← hpt]
            exact (topologicalKrullDimAt_eq_of_homeomorph H (g.asFiber z)).symm
      _ = n := by simpa [g] using hn
  obtain ⟨heq, hpure⟩ := hpure
  let Vfinal : EtaleNeighborhood S (f (i z)) :=
    { scheme := V.scheme
      point := V.point
      toBase := V.toBase
      etale_toBase := V.etale_toBase
      map_point := V.map_point.trans hgz }
  have hVfinalElem : Vfinal.IsElementary := by
    rw [EtaleNeighborhood.isElementary_iff]
    exact (EtaleNeighborhood.isElementary_iff V).mp hVE
  -- the closed immersion base changed to `V`, and its étale lift
  let X₁ := pullback f V.toBase
  let x₁ : X₁ ⟶ X := pullback.fst f V.toBase
  let v₁ : X₁ ⟶ V.scheme := pullback.snd f V.toBase
  let Z₁ := pullback i x₁
  let z₁ : Z₁ ⟶ Z := pullback.fst i x₁
  let i₁ : Z₁ ⟶ X₁ := pullback.snd i x₁
  have x₁sq : IsPullback z₁ i₁ i x₁ := IsPullback.of_hasPullback i x₁
  let uX : UZ.scheme ⟶ X₁ := pullback.lift (UZ.toBase ≫ i) (π ≫ h) (by
    dsimp [g] at hcomm
    simpa [x₁, v₁, Category.assoc] using hcomm)
  have hCompat : UZ.toBase ≫ i = uX ≫ x₁ := (pullback.lift_fst (UZ.toBase ≫ i) (π ≫ h) _).symm
  let uZ₁ : UZ.scheme ⟶ Z₁ := pullback.lift UZ.toBase uX hCompat
  have huZ₁ : uZ₁ ≫ z₁ = UZ.toBase := pullback.lift_fst UZ.toBase uX hCompat
  have huZ₁Etale : Etale uZ₁ := by
    have : Etale (uZ₁ ≫ z₁) := by simpa [huZ₁] using UZ.etale_toBase
    exact Etale.of_comp uZ₁ z₁
  have hX₁aff : IsAffine X₁ := inferInstance
  have hZ₁aff : IsAffine Z₁ := inferInstance
  have hi₁ : IsClosedImmersion i₁ := inferInstance
  obtain ⟨W, w, hWaff, hwEtale, eR, heR⟩ :=
    Stacks.Etale.exists_etale_lift_of_isClosedImmersion i₁ uZ₁
  let wX : W ⟶ X := w ≫ x₁
  let wV : W ⟶ V.scheme := w ≫ v₁
  let Z₂ := pullback i₁ w
  let z₂ : Z₂ ⟶ Z₁ := pullback.fst i₁ w
  let i₂ : Z₂ ⟶ W := pullback.snd i₁ w
  have wsq : IsPullback z₂ i₂ i₁ w := IsPullback.of_hasPullback i₁ w
  let e₂ : UZ.scheme ≅ Z₂ := eR
  let z₂pt : Z₂ := e₂.hom UZ.point
  -- the module on the twice base-changed closed subscheme
  let G₁ : Z₁.Modules := (Scheme.Modules.pullback z₁).obj G
  obtain ⟨hG₁ft, hG₁qc⟩ := pullback_isFiniteType_and_isQuasicoherent z₁ G
  let GFinal : Z₂.Modules := (Scheme.Modules.pullback z₂).obj G₁
  obtain ⟨hGFinalft, hGFinalqc⟩ := pullback_isFiniteType_and_isQuasicoherent z₂ G₁
  let πFinal : Z₂ ⟶ Y := e₂.inv ≫ π
  let pointFinal : W := i₂ z₂pt
  have hRpoint : z₂ z₂pt = uZ₁ UZ.point := by
    have := congrArg (fun q : UZ.scheme ⟶ Z₁ => q UZ.point) heR
    simpa [e₂, z₂pt, z₂] using this
  have hzpoint : z₁ (z₂ z₂pt) = z := by
    calc
      z₁ (z₂ z₂pt) = z₁ (uZ₁ UZ.point) := by rw [hRpoint]
      _ = UZ.toBase UZ.point := congrArg (fun q : UZ.scheme ⟶ Z => q UZ.point) huZ₁
      _ = z := UZ.map_point
  have hWpull : i₂ ≫ w = z₂ ≫ i₁ := wsq.w.symm
  have hZpull : i₁ ≫ x₁ = z₁ ≫ i := x₁sq.w.symm
  have hpointFinal : wX pointFinal = i z := by
    calc
      wX pointFinal = (i₂ ≫ w ≫ x₁) z₂pt := by simp [wX, pointFinal]
      _ = (z₂ ≫ i₁ ≫ x₁) z₂pt := by
        refine congrArg (fun q : Z₂ ⟶ X => q z₂pt) ?_
        calc
          i₂ ≫ w ≫ x₁ = (i₂ ≫ w) ≫ x₁ := by simp [Category.assoc]
          _ = (z₂ ≫ i₁) ≫ x₁ := by rw [hWpull]
          _ = z₂ ≫ i₁ ≫ x₁ := by simp [Category.assoc]
      _ = (z₂ ≫ z₁ ≫ i) z₂pt := by
        refine congrArg (fun q : Z₂ ⟶ X => q z₂pt) ?_
        calc
          z₂ ≫ i₁ ≫ x₁ = z₂ ≫ (i₁ ≫ x₁) := rfl
          _ = z₂ ≫ (z₁ ≫ i) := by rw [hZpull]
          _ = z₂ ≫ z₁ ≫ i := rfl
      _ = i z := by simpa [Category.assoc] using congrArg (fun q => i q) hzpoint
  have hwFinalEtale : Etale wX := inferInstance
  let Ufinal : EtaleNeighborhood X (i z) :=
    { scheme := W
      point := pointFinal
      toBase := wX
      etale_toBase := hwFinalEtale
      map_point := hpointFinal }
  have hfp₂ : FinitePresentation i₂ :=
    finitePresentation_of_isPullback wsq (finitePresentation_of_isPullback x₁sq hfp)
  have hIaffHom : IsAffineHom i := inferInstance
  have hi₁aff : IsAffineHom i₁ := inferInstance
  have hPushIso : (Scheme.Modules.pushforward i₂).obj GFinal ≅
      (Scheme.Modules.pullback wX).obj F := by
    have hbc₁ := isIso_baseChangeNatTrans_of_isAffineHom x₁sq G
    have hbc₂ := isIso_baseChangeNatTrans_of_isAffineHom wsq G₁
    let eBC₁ : (Scheme.Modules.pullback x₁).obj ((Scheme.Modules.pushforward i).obj G) ≅
        (Scheme.Modules.pushforward i₁).obj G₁ :=
      asIso ((baseChangeNatTrans x₁sq.w).app G)
    let eBC₂ : (Scheme.Modules.pullback w).obj ((Scheme.Modules.pushforward i₁).obj G₁) ≅
        (Scheme.Modules.pushforward i₂).obj GFinal :=
      asIso ((baseChangeNatTrans wsq.w).app G₁)
    calc
      (Scheme.Modules.pushforward i₂).obj GFinal ≅
          (Scheme.Modules.pullback w).obj
            ((Scheme.Modules.pushforward i₁).obj G₁) := eBC₂.symm
      _ ≅ (Scheme.Modules.pullback w).obj
            ((Scheme.Modules.pullback x₁).obj ((Scheme.Modules.pushforward i).obj G)) :=
        (Scheme.Modules.pullback w).mapIso eBC₁.symm
      _ ≅ (Scheme.Modules.pullback w).obj ((Scheme.Modules.pullback x₁).obj F) :=
        (Scheme.Modules.pullback w).mapIso ((Scheme.Modules.pullback x₁).mapIso eQ)
      _ ≅ (Scheme.Modules.pullback wX).obj F := by
        simpa [wX] using (Scheme.Modules.pullbackComp w x₁).app F
  have hToBase : wX ≫ f = wV ≫ V.toBase := by
    calc
      wX ≫ f = w ≫ x₁ ≫ f := by simp [wX, Category.assoc]
      _ = w ≫ v₁ ≫ V.toBase := by
        rw [show x₁ ≫ f = v₁ ≫ V.toBase from pullback.condition]
      _ = wV ≫ V.toBase := by simp [wV, Category.assoc]
  have hinvR : e₂.inv ≫ uZ₁ = z₂ := by rw [← heR]; simp [e₂, z₂]
  have hToClosed : i₂ ≫ wV = πFinal ≫ h := by
    have hULift : uZ₁ ≫ i₁ = uX := pullback.lift_snd UZ.toBase uX hCompat
    have hUXV : uX ≫ v₁ = π ≫ h := pullback.lift_snd (UZ.toBase ≫ i) (π ≫ h) _
    have hClosedBase : uZ₁ ≫ i₁ ≫ v₁ = π ≫ h := by
      rw [← Category.assoc, hULift, hUXV]
    calc
      i₂ ≫ wV = z₂ ≫ i₁ ≫ v₁ := by
        calc
          i₂ ≫ wV = (i₂ ≫ w) ≫ v₁ := by simp [wV, Category.assoc]
          _ = (z₂ ≫ i₁) ≫ v₁ := by rw [hWpull]
          _ = z₂ ≫ i₁ ≫ v₁ := by simp [Category.assoc]
      _ = (e₂.inv ≫ uZ₁) ≫ (i₁ ≫ v₁) := by rw [hinvR]
      _ = e₂.inv ≫ (uZ₁ ≫ i₁ ≫ v₁) := Category.assoc _ _ _
      _ = e₂.inv ≫ (π ≫ h) := by rw [hClosedBase]
      _ = πFinal ≫ h := (Category.assoc _ _ _).symm
  have hfiniteFinal : IsFinite πFinal := by
    have : IsFinite e₂.inv := inferInstance
    exact inferInstance
  have hsingleFinal : ∀ z' : Z₂, πFinal z' = πFinal z₂pt ↔ z' = z₂pt := by
    intro z'
    constructor
    · intro hπ
      have hπ' : π (e₂.inv z') = π UZ.point := by simpa [πFinal, z₂pt] using hπ
      have hz : e₂.inv z' = UZ.point := (hsingle (e₂.inv z')).mp hπ'
      simpa using congrArg e₂.hom hz
    · intro hz
      subst z'
      rfl
  have hπpoint : πFinal z₂pt = π UZ.point := by simp [πFinal, z₂pt, e₂]
  have heqFinal : h (πFinal z₂pt) = Vfinal.point := by
    rw [hπpoint]
    simpa [Vfinal] using heq
  let : Algebra (V.scheme.residueField V.point) (Y.residueField (πFinal z₂pt)) :=
    ((V.scheme.residueFieldCongr heqFinal).inv ≫
      h.residueFieldMap (πFinal z₂pt)).hom.toAlgebra
  have hpureFinal : PurelyTranscendental (V.scheme.residueField V.point)
      (Y.residueField (πFinal z₂pt)) :=
    purelyTranscendental_residueField_congr h V.point (π UZ.point) (πFinal z₂pt) heq
      heqFinal hπpoint hpure
  -- the new source neighbourhood is elementary
  have hClosedComp : e₂.hom ≫ i₂ ≫ wX = UZ.toBase ≫ i := by
    calc
      e₂.hom ≫ i₂ ≫ wX = e₂.hom ≫ (i₂ ≫ w) ≫ x₁ := by simp [wX, Category.assoc]
      _ = e₂.hom ≫ (z₂ ≫ i₁) ≫ x₁ := by rw [hWpull]
      _ = (e₂.hom ≫ z₂) ≫ i₁ ≫ x₁ := by simp [Category.assoc]
      _ = uZ₁ ≫ i₁ ≫ x₁ := by rw [show e₂.hom ≫ z₂ = uZ₁ from heR]
      _ = uX ≫ x₁ := by
        have hULift : uZ₁ ≫ i₁ = uX := pullback.lift_snd UZ.toBase uX hCompat
        calc
          uZ₁ ≫ i₁ ≫ x₁ = (uZ₁ ≫ i₁) ≫ x₁ := by simp [Category.assoc]
          _ = uX ≫ x₁ := by rw [hULift]
      _ = UZ.toBase ≫ i := hCompat.symm
  have : IsClosedImmersion i₂ := inferInstance
  have hUE' : IsIso (UZ.toBase.residueFieldMap UZ.point) :=
    (EtaleNeighborhood.isElementary_iff UZ).mp hUE
  have hClosedCompIso : IsIso ((e₂.hom ≫ i₂ ≫ wX).residueFieldMap UZ.point) := by
    rw [hClosedComp, Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso'
      (i.isIso_residueFieldMap_of_surjectiveOnStalks (UZ.toBase UZ.point)) hUE'
  have hUfinalRes : IsIso (wX.residueFieldMap pointFinal) := by
    have hMap : (e₂.hom ≫ i₂ ≫ wX).residueFieldMap UZ.point =
        wX.residueFieldMap pointFinal ≫
          (i₂.residueFieldMap z₂pt ≫ e₂.hom.residueFieldMap UZ.point) := by
      simp [Scheme.residueFieldMap_comp, pointFinal, z₂pt, e₂, Category.assoc]
    have hFactor : IsIso (wX.residueFieldMap pointFinal ≫
        (i₂.residueFieldMap z₂pt ≫ e₂.hom.residueFieldMap UZ.point)) := by
      rw [← hMap]
      exact hClosedCompIso
    have : IsIso (i₂.residueFieldMap z₂pt) :=
      i₂.isIso_residueFieldMap_of_surjectiveOnStalks z₂pt
    have : IsIso (e₂.hom.residueFieldMap UZ.point) := inferInstance
    have : IsIso (i₂.residueFieldMap z₂pt ≫ e₂.hom.residueFieldMap UZ.point) := inferInstance
    have : IsIso (wX.residueFieldMap pointFinal ≫
        (i₂.residueFieldMap z₂pt ≫ e₂.hom.residueFieldMap UZ.point)) := hFactor
    exact IsIso.of_isIso_comp_right (wX.residueFieldMap pointFinal)
      (i₂.residueFieldMap z₂pt ≫ e₂.hom.residueFieldMap UZ.point)
  exact ⟨{ n := n
           dimension := hdim'
           U := Ufinal
           V := Vfinal
           elementary_U := by
             rw [EtaleNeighborhood.isElementary_iff]
             exact hUfinalRes
           elementary_V := hVfinalElem
           Z := Z₂
           Y := Y
           toBase := wV
           i := i₂
           π := πFinal
           h := h
           z := z₂pt
           G := GFinal
           commutes_base := hToBase
           commutes_closed := hToClosed
           point_closed := rfl
           point_base := by simpa [πFinal, z₂pt, e₂, Vfinal] using heq
           affine_U := hWaff
           affine_V := hVaff
           affine_Z := inferInstance
           affine_Y := hYaff
           closedImmersion := inferInstance
           finitePresentation := hfp₂
           sheafIso := hPushIso
           finiteType_G := hGFinalft
           quasicoherent_G := hGFinalqc
           finite_π := hfiniteFinal
           singleton_fiber := hsingleFinal
           pureTranscendental := hpureFinal
           smooth := hsmooth
           integral_fibers := hintegral }⟩

/-- An étale neighbourhood of a point of an open subscheme is an étale neighbourhood of that
point of the ambient scheme. -/
private def overOpen {T : Scheme.{u}} (O : T.Opens) (t : T) (ht : t ∈ O)
    (N : EtaleNeighborhood O.toScheme ⟨t, ht⟩) : EtaleNeighborhood T t where
  scheme := N.scheme
  point := N.point
  toBase := N.toBase ≫ O.ι
  etale_toBase := @Etale.etale_comp _ _ N.toBase _ O.ι N.etale_toBase inferInstance
  map_point := by
    change O.ι (N.toBase N.point) = t
    rw [N.map_point]
    rfl

/-- An étale neighbourhood of a point may be regarded as a neighbourhood of any point equal
to it. -/
private def changeBasePoint {T : Scheme.{u}} {s t : T} (N : EtaleNeighborhood T s) (hst : s = t) :
    EtaleNeighborhood T t where
  scheme := N.scheme
  point := N.point
  toBase := N.toBase
  etale_toBase := N.etale_toBase
  map_point := N.map_point.trans hst

/-- Changing the base point of an étale neighbourhood along an equality preserves
elementariness. -/
private theorem changeBasePoint_isElementary {T : Scheme.{u}} {s t : T}
    (N : EtaleNeighborhood T s) (hst : s = t) (hN : N.IsElementary) :
    (changeBasePoint N hst).IsElementary := by
  cases hst
  exact hN

/-- An elementary étale neighbourhood of a point of an open subscheme is an elementary étale
neighbourhood of that point of the ambient scheme: an open immersion is an isomorphism on
residue fields. -/
private theorem overOpen_isElementary {T : Scheme.{u}} (O : T.Opens) (t : T) (ht : t ∈ O)
    (N : EtaleNeighborhood O.toScheme ⟨t, ht⟩) (hN : N.IsElementary) :
    (overOpen O t ht N).IsElementary := by
  have hBase : IsIso (N.toBase.residueFieldMap N.point) :=
    (EtaleNeighborhood.isElementary_iff N).mp hN
  have hOpen : IsIso (O.ι.residueFieldMap (N.toBase N.point)) := inferInstance
  rw [EtaleNeighborhood.isElementary_iff]
  show IsIso ((N.toBase ≫ O.ι).residueFieldMap N.point)
  rw [Scheme.residueFieldMap_comp]
  exact IsIso.comp_isIso' hOpen hBase

/-- The fibre of the closed immersion of an elementary dévissage over the distinguished point of
the source neighbourhood is the distinguished point of the closed subscheme. -/
theorem preimage_i_singleton {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {x : X}
    {hx : f.asFiber x ∈
      SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)}
    (D : ElementaryDevissage f F x hx) :
    D.i ⁻¹' {D.U.point} = {D.z} := by
  have : IsClosedImmersion D.i := D.closedImmersion
  ext z'
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  refine ⟨fun hz' ↦ D.i.isClosedEmbedding.injective (hz'.trans D.point_closed.symm), ?_⟩
  rintro rfl
  exact D.point_closed

/-- The fibre of the finite morphism of an elementary dévissage over the image of the
distinguished point is that point. -/
theorem preimage_π_singleton {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {x : X}
    {hx : f.asFiber x ∈
      SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)}
    (D : ElementaryDevissage f F x hx) :
    D.π ⁻¹' {D.π D.z} = {D.z} := by
  ext z'
  simpa only [Set.mem_preimage, Set.mem_singleton_iff] using D.singleton_fiber z'

end ElementaryDevissage

open ElementaryDevissage in
/-- **Stacks Project, Tag 057S.** A finite-type quasi-coherent module admits an elementary
dévissage at any point of the support of its fibre. -/
@[stacks 057S]
theorem exists_elementaryDevissage {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (x : X)
    (hx : f.asFiber x ∈
      SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)) :
    Nonempty (ElementaryDevissage f F x hx) := by
  classical
  obtain ⟨_, ⟨V₀, hV, rfl⟩, hsV, _⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U₀, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ f ⁻¹ᵁ V₀ from hsV) (f ⁻¹ᵁ V₀).2
  let Uₐ : X.affineOpens := ⟨U₀, hU⟩
  let Vₐ : S.affineOpens := ⟨V₀, hV⟩
  let f' : Uₐ.1.toScheme ⟶ Vₐ.1.toScheme := f.resLE Vₐ.1 Uₐ.1 hUV
  let x' : Uₐ.1.toScheme := ⟨x, hxU⟩
  let F' : Uₐ.1.toScheme.Modules := (Scheme.Modules.pullback Uₐ.1.ι).obj F
  obtain ⟨hx', hdim⟩ := topologicalKrullDimAt_supp_resLE f F x Uₐ.1 Vₐ.1 hxU hUV hx
  have : IsAffine Uₐ.1.toScheme := Uₐ.2
  have : IsAffine Vₐ.1.toScheme := Vₐ.2
  have : LocallyOfFiniteType f' := locallyOfFiniteType_resLE f Vₐ.1 Uₐ.1 hUV
  obtain ⟨_, _⟩ := pullback_isFiniteType_and_isQuasicoherent Uₐ.1.ι F
  obtain ⟨d⟩ := exists_of_isAffine f' F' x' hx'
  let Uglobal := overOpen Uₐ.1 x hxU d.U
  have hfx : f' x' = (⟨f x, hsV⟩ : Vₐ.1.toScheme) := by
    apply Vₐ.1.ι.isEmbedding.injective
    exact ι_resLE_apply f Vₐ.1 Uₐ.1 hUV x'
  let Vlocal := changeBasePoint d.V hfx
  have hVlocalElem : Vlocal.IsElementary :=
    changeBasePoint_isElementary d.V hfx d.elementary_V
  let Vglobal := overOpen Vₐ.1 (f x) hsV Vlocal
  have hdimension : topologicalKrullDimAt
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
      ⟨f.asFiber x, hx⟩ = d.n := by
    rw [← hdim]
    exact d.dimension
  have hbase : Uglobal.toBase ≫ f = d.toBase ≫ Vglobal.toBase := by
    show (d.U.toBase ≫ Uₐ.1.ι) ≫ f = d.toBase ≫ (Vlocal.toBase ≫ Vₐ.1.ι)
    calc
      (d.U.toBase ≫ Uₐ.1.ι) ≫ f = d.U.toBase ≫ (Uₐ.1.ι ≫ f) := Category.assoc _ _ _
      _ = d.U.toBase ≫ (f' ≫ Vₐ.1.ι) := by rw [← Scheme.Hom.resLE_comp_ι f (e := hUV)]
      _ = (d.U.toBase ≫ f') ≫ Vₐ.1.ι := (Category.assoc _ _ _).symm
      _ = (d.toBase ≫ d.V.toBase) ≫ Vₐ.1.ι := by rw [d.commutes_base]
      _ = d.toBase ≫ (Vlocal.toBase ≫ Vₐ.1.ι) := Category.assoc _ _ _
  have hsheaf : (Scheme.Modules.pushforward d.i).obj d.G ≅
      (Scheme.Modules.pullback Uglobal.toBase).obj F := by
    show _ ≅ (Scheme.Modules.pullback (d.U.toBase ≫ Uₐ.1.ι)).obj F
    simpa [F'] using d.sheafIso ≪≫ (Scheme.Modules.pullbackComp d.U.toBase Uₐ.1.ι).app F
  exact ⟨{ n := d.n
           dimension := hdimension
           U := Uglobal
           V := Vglobal
           elementary_U := overOpen_isElementary Uₐ.1 x hxU d.U d.elementary_U
           elementary_V := overOpen_isElementary Vₐ.1 (f x) hsV Vlocal hVlocalElem
           Z := d.Z
           Y := d.Y
           toBase := d.toBase
           i := d.i
           π := d.π
           h := d.h
           z := d.z
           G := d.G
           commutes_base := hbase
           commutes_closed := d.commutes_closed
           point_closed := d.point_closed
           point_base := d.point_base
           affine_U := d.affine_U
           affine_V := d.affine_V
           affine_Z := d.affine_Z
           affine_Y := d.affine_Y
           closedImmersion := d.closedImmersion
           finitePresentation := d.finitePresentation
           sheafIso := hsheaf
           finiteType_G := d.finiteType_G
           quasicoherent_G := d.quasicoherent_G
           finite_π := d.finite_π
           singleton_fiber := d.singleton_fiber
           pureTranscendental := d.pureTranscendental
           smooth := d.smooth
           integral_fibers := d.integral_fibers }⟩

end AlgebraicGeometry

end
