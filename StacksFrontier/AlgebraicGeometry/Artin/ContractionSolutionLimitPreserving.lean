module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionClosed
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionComparison
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LimitPreservingNoetherian
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LocallyNoetherianExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Transport
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget

/-!
# The completion of a locally Noetherian algebraic space along a closed subset is limit preserving

Let `S` be a locally Noetherian scheme and let `X` be an algebraic space locally of finite type
over `S`, and let `T ⊆ |X|` be closed. The completion `X_{/T}` of Stacks 0AMC is limit
preserving in the sense of Stacks 049J: it turns a cofiltered limit `V = lim V i` of affine
objects of the big fppf site of `S` into a filtered colimit of sets.

## Main results

* `AlgebraicGeometry.Scheme.isCompact_of_preimage_eq_preimage`: a subset of a quasi-compact
  scheme whose preimage along an open surjection is the preimage of an open of a locally
  Noetherian scheme is quasi-compact.
* `AlgebraicGeometry.Space.isCompact_preimage_pointsMap`: for an algebraic space `X` locally of
  finite type over a locally Noetherian base, the preimage of an open set of points of `X` in a
  quasi-compact object of the site is quasi-compact.
* `AlgebraicGeometry.Space.exists_map_mem_openSubspaceOfPoints_of_isLimit`: the condition of
  having point-set image in a closed `T ⊆ |X|` descends from a cofiltered limit of affines to a
  finite stage.
* `AlgebraicGeometry.Space.limitPreserving_openSubspaceOfPoints`,
  `AlgebraicGeometry.Space.limitPreserving_completionSubfunctor` and
  `AlgebraicGeometry.Space.limitPreserving_completionSheaf`: the subfunctor of sections with
  point-set image in `T` and the completion `X_{/T}` are limit preserving.
* `AlgebraicGeometry.Space.isSheaf_completionSubfunctor`: the subfunctor of sections of an fppf
  sheaf with point-set image in a set of points is an fppf sheaf.
* `AlgebraicGeometry.Artin.ContractionSituation.completionSheafIsoW`: in the situation of
  Stacks 0GHC, the restriction of `X_{/T}` to locally Noetherian schemes over `S` is isomorphic
  to that of `W`.
* `AlgebraicGeometry.Artin.ContractionSituation.limitPreserving_W`: `W` is limit preserving.
* `AlgebraicGeometry.Artin.ContractionSituation.existsUnique_completionSheafIso_W` and
  `AlgebraicGeometry.Artin.ContractionSituation.completionSheafIsoWExt`: the isomorphism
  `X_{/T} ≅ W` of fppf sheaves on the whole site extending
  `AlgebraicGeometry.Artin.ContractionSituation.completionSheafIsoW`.

## References

* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Tag 05N0](https://stacks.math.columbia.edu/tag/05N0)
* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
* [Stacks Project, Tag 0GE3](https://stacks.math.columbia.edu/tag/0GE3)
* [Stacks Project, Tag 0GHC](https://stacks.math.columbia.edu/tag/0GHC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v v' w w' z z'

namespace AlgebraicGeometry

/-- Let `q : P ⟶ V` be a morphism of schemes with open and surjective underlying map onto a
quasi-compact scheme, and let `p : P ⟶ U` be a morphism to a locally Noetherian scheme. A subset
`K ⊆ V` whose preimage along `q` is the preimage along `p` of an open `O ⊆ U` is quasi-compact. -/
theorem Scheme.isCompact_of_preimage_eq_preimage {P V U : Scheme.{u}} (q : P ⟶ V) (p : P ⟶ U)
    [CompactSpace V] [IsLocallyNoetherian U] (hopen : IsOpenMap q.base)
    (hsurj : Function.Surjective q.base) {K : Set V} {O : Set U} (hO : IsOpen O)
    (h : q.base ⁻¹' K = p.base ⁻¹' O) : IsCompact K := by
  obtain ⟨W, hWc, hWim⟩ := exists_isCompact_opens_image_eq_univ q hopen hsurj
  have : CompactSpace W := isCompact_iff_compactSpace.mp hWc
  let O' : U.Opens := ⟨O, hO⟩
  let p' : (W : Scheme.{u}) ⟶ U := W.ι ≫ p
  have : QuasiCompact (p' ⁻¹ᵁ O').ι :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (isPullback_morphismRestrict p' O')
      (inferInstanceAs (QuasiCompact O'.ι))
  have hc : IsCompact (Set.range (p' ⁻¹ᵁ O').ι.base) := by
    have := QuasiCompact.compactSpace_of_compactSpace (p' ⁻¹ᵁ O').ι
    exact isCompact_range (p' ⁻¹ᵁ O').ι.continuous
  have hK : K = q.base '' (W.ι.base '' Set.range (p' ⁻¹ᵁ O').ι.base) := by
    rw [Scheme.Opens.range_ι]
    ext k
    constructor
    · intro hk
      obtain ⟨w, hw, rfl⟩ : k ∈ q.base '' (W : Set P) := hWim ▸ Set.mem_univ k
      refine ⟨W.ι.base ⟨w, hw⟩, ⟨⟨w, hw⟩, ?_, rfl⟩, rfl⟩
      change p.base w ∈ O
      rwa [← Set.mem_preimage, ← h]
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      change p.base (W.ι.base w) ∈ O at hw
      rwa [← Set.mem_preimage, ← h] at hw
  rw [hK]
  exact (hc.image W.ι.continuous).image q.continuous

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `X` be an algebraic space locally of finite type over a locally Noetherian scheme `S`, and
let `a : V ⟶ X` be a morphism from a quasi-compact object of the site. The preimage of an open
set of points of `X` along `a` is quasi-compact. -/
theorem isCompact_preimage_pointsMap [IsLocallyNoetherian S] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hft : IsLocallyOfFiniteType B S hS (terminal.from X))
    (V : BigFppfOver B S hS) [CompactSpace ((BigFppfOver.toScheme B S hS).obj V)]
    (a : yoneda.obj V ⟶ X) {O : Set (points B S hS X)} (hO : IsOpen O) :
    IsCompact (pointsMap B S hS (yoneda.obj V) a ⁻¹' O) := by
  obtain ⟨U, e, hsurj, het⟩ := hX.exists_atlas
  have hUN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) :=
    isLocallyNoetherian_of_presheafEtale B S hS hft U e het
  let hr := het.rep
  have sq := hr.isPullback a
  have hqet : Etale ((BigFppfOver.toScheme B S hS).map (hr.snd a)) :=
    het.2 a (hr.fst a) (hr.snd a) sq
  have hqsurj : Surjective ((BigFppfOver.toScheme B S hS).map (hr.snd a)) :=
    hsurj.2 a (hr.fst a) (hr.snd a) sq
  let p := yoneda.preimage (hr.fst a)
  let φV := schemePointsHomeomorph B S hS V
  let φU := schemePointsHomeomorph B S hS U
  let K : Set ((BigFppfOver.toScheme B S hS).obj V) :=
    φV.symm ⁻¹' (pointsMap B S hS (yoneda.obj V) a ⁻¹' O)
  have hK : IsCompact K := by
    refine Scheme.isCompact_of_preimage_eq_preimage
      ((BigFppfOver.toScheme B S hS).map (hr.snd a)) ((BigFppfOver.toScheme B S hS).map p)
      (Scheme.Hom.isOpenMap _) hqsurj.surj
      (O := φU.symm ⁻¹' (pointsMap B S hS (yoneda.obj U) e ⁻¹' O))
      ((hO.preimage (continuous_pointsMap B S hS e)).preimage φU.symm.continuous) ?_
    ext z
    simp only [Set.mem_preimage, K, φV, φU, p]
    rw [← schemePointsHomeomorph_symm_naturality, ← schemePointsHomeomorph_symm_naturality,
      ← pointsMap_comp_apply, ← pointsMap_comp_apply, Functor.map_preimage, ← sq.w]
  have hKe : pointsMap B S hS (yoneda.obj V) a ⁻¹' O = φV ⁻¹' K := by
    ext w
    simp [K]
  rw [hKe]
  exact φV.isCompact_preimage.mpr hK

/-- Restricting a section `x` of `X` over `Y` along `g : Z ⟶ Y` gives a section with point-set
image in a set `T ⊆ |X|` exactly when every scheme point of `Z` is carried by `g` to a point of
`Y` whose image in `|X|` lies in `T`. -/
theorem map_mem_openSubspaceOfPoints_iff {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (points B S hS X)) {Z Y : BigFppfOver B S hS} (g : Z ⟶ Y) (x : X.obj (op Y)) :
    X.map g.op x ∈ (openSubspaceOfPoints B S hS X T).obj (op Z) ↔
      ∀ z : (BigFppfOver.toScheme B S hS).obj Z,
        pointsMap B S hS (yoneda.obj Y) (yonedaEquiv.symm x)
          ((schemePointsHomeomorph B S hS Y).symm ((BigFppfOver.toScheme B S hS).map g z)) ∈ T := by
  rw [mem_openSubspaceOfPoints_iff, Set.range_subset_iff, yonedaEquiv_symm_map,
    Quiver.Hom.unop_op]
  refine (schemePointsHomeomorph B S hS Z).symm.surjective.forall.trans ?_
  simp only [pointsMap_comp_apply, schemePointsHomeomorph_symm_naturality]

/-- Let `X` be an algebraic space locally of finite type over a locally Noetherian scheme `S`, let
`T ⊆ |X|` be closed, and let `V = lim V i` be a cofiltered limit of affine objects of the site. If
a section of `X` over some `V i` has, restricted to `V`, point-set image in `T`, then so does its
restriction to some later stage `V j`. -/
theorem exists_map_mem_openSubspaceOfPoints_of_isLimit [IsLocallyNoetherian S]
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hft : IsLocallyOfFiniteType B S hS (terminal.from X)) {T : Set (points B S hS X)}
    (hT : IsClosed T) {I : Type u} [Category.{u} I] [IsCofiltered I]
    {D : I ⥤ BigFppfOver B S hS} {c : Cone D}
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hD : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i))) (i : I)
    (x : X.obj (op (D.obj i)))
    (hx : X.map (c.π.app i).op x ∈ (openSubspaceOfPoints B S hS X T).obj (op c.pt)) :
    ∃ (j : I) (f : j ⟶ i),
      X.map (D.map f).op x ∈ (openSubspaceOfPoints B S hS X T).obj (op (D.obj j)) := by
  let a := yonedaEquiv.symm x
  let φ := schemePointsHomeomorph B S hS (D.obj i)
  let K : Set ((BigFppfOver.toScheme B S hS).obj (D.obj i)) :=
    φ.symm ⁻¹' (pointsMap B S hS (yoneda.obj (D.obj i)) a ⁻¹' Tᶜ)
  have hKo : IsOpen K :=
    (hT.isOpen_compl.preimage (continuous_pointsMap B S hS a)).preimage φ.symm.continuous
  have hKc : IsCompact K :=
    φ.symm.isCompact_preimage.mpr
      (isCompact_preimage_pointsMap B S hS hX hft (D.obj i) a hT.isOpen_compl)
  let U₀ : ((D ⋙ BigFppfOver.toScheme B S hS).obj i).Opens := ⟨K, hKo⟩
  have : ∀ i, IsAffine ((D ⋙ BigFppfOver.toScheme B S hS).obj i) := hD
  have key : ∀ {Z : BigFppfOver B S hS} (g : Z ⟶ D.obj i),
      X.map g.op x ∈ (openSubspaceOfPoints B S hS X T).obj (op Z) ↔
        (BigFppfOver.toScheme B S hS).map g ⁻¹ᵁ U₀ ≤ ⊥ := by
    intro Z g
    rw [map_mem_openSubspaceOfPoints_iff]
    exact ⟨fun h z hz => (hz (h z)).elim, fun h z => Classical.byContradiction fun hz =>
      h (show z ∈ (BigFppfOver.toScheme B S hS).map g ⁻¹ᵁ U₀ from hz)⟩
  obtain ⟨j, f, hf⟩ := exists_map_preimage_le_map_preimage (D ⋙ BigFppfOver.toScheme B S hS)
    ((BigFppfOver.toScheme B S hS).mapCone c) hc (i := i) (U := U₀) (V := ⊥) hKc
    (by simpa using (key (c.π.app i)).mp hx)
  exact ⟨j, f, (key (D.map f)).mpr (by simpa using hf)⟩

/-- For `X` an algebraic space locally of finite type over a locally Noetherian scheme `S` and
`T ⊆ |X|` closed, the subfunctor of sections of `X` with point-set image in `T` is limit
preserving. -/
theorem limitPreserving_openSubspaceOfPoints [IsLocallyNoetherian S]
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hft : IsLocallyOfFiniteType B S hS (terminal.from X)) {T : Set (points B S hS X)}
    (hT : IsClosed T) :
    LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS)
      (openSubspaceOfPoints B S hS X T).toFunctor := by
  intro I _ _ D c hc hD hC
  obtain ⟨hXc⟩ := limitPreserving_of_isLocallyOfFiniteType B S hS hX hft I D c hc hD hC
  refine nonempty_isColimit_mapCocone_of_exists_of_eventually_eq _ D c ?_ ?_
  · intro s
    obtain ⟨i, y, hy⟩ := exists_eq_map_of_isColimit_mapCocone X D c hXc s.1
    obtain ⟨j, f, hf⟩ := exists_map_mem_openSubspaceOfPoints_of_isLimit B S hS hX hft hT hc hD i y
      (by rw [hy]; exact s.2)
    refine ⟨j, ⟨X.map (D.map f).op y, hf⟩, Subtype.ext ?_⟩
    change X.map (c.π.app j).op (X.map (D.map f).op y) = s.1
    rw [← Functor.map_comp_apply, ← op_comp, c.w f, hy]
  · intro i x y hxy
    obtain ⟨j, f, hf⟩ := eventually_eq_of_isColimit_mapCocone X D c hXc i x.1 y.1
      (congrArg Subtype.val hxy)
    exact ⟨j, f, Subtype.ext hf⟩

/-- Limit preservation passes to the universe lift of a presheaf of sets. -/
theorem limitPreserving_comp_uliftFunctor {C : Type z} [Category.{z'} C]
    {toScheme : C ⥤ Scheme.{u}} {F : Cᵒᵖ ⥤ Type v}
    (hF : LimitPreserving.{u, v, w, w', z, z'} toScheme F) :
    LimitPreserving.{u, max v v', w, w', z, z'} toScheme (F ⋙ uliftFunctor.{v'}) := by
  intro I _ _ D c hc hD hC
  obtain ⟨h⟩ := hF I D c hc hD hC
  exact ⟨isColimitOfPreserves uliftFunctor.{v'} h⟩

/-- The subfunctor of the universe lift of `X` whose sections have point-set image in `T` is the
universe lift of the subfunctor of `X` cut out by `T`. -/
noncomputable def completionSubfunctorIso (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (T : Set (points B S hS X)) :
    (completionSubfunctor B S hS X T).toFunctor ≅
      (openSubspaceOfPoints B S hS X T).toFunctor ⋙ uliftFunctor.{u + 1} :=
  NatIso.ofComponents (fun U => Equiv.toIso
    { toFun := fun s => ULift.up ⟨s.1.down, (hasImageIn_iff_range_subset B S hS T _ _).1 s.2⟩
      invFun := fun s => ⟨ULift.up s.down.1, (hasImageIn_iff_range_subset B S hS T _ _).2 s.down.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }) (by intros; ext; rfl)

/-- The sections of an fppf sheaf with point-set image in a set of points form an fppf sheaf. -/
theorem isSheaf_completionSubfunctor {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) (T : Set (points B S hS X)) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (completionSubfunctor B S hS X T).toFunctor := by
  rw [Presheaf.isSheaf_of_iso_iff (completionSubfunctorIso B S hS X T), isSheaf_iff_isSheaf_of_type,
    Presieve.isSheaf_comp_uliftFunctor_iff, ← isSheaf_iff_isSheaf_of_type]
  exact isSheaf_openSubspaceOfPoints B S hS hX T

/-- The completion `X_{/T}` of an fppf sheaf `X` along a set of points `T` is
isomorphic to the subfunctor of sections with point-set image in `T`. -/
noncomputable def completionSheafIsoSubfunctor {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) (T : Set (points B S hS X)) :
    (completionSheaf B S hS X T).obj ≅ (completionSubfunctor B S hS X T).toFunctor :=
  ((BigFppfOver.topology B S hS).isoSheafify (isSheaf_completionSubfunctor B S hS hX T)).symm

/-- The subfunctor of sections of `X` with point-set image in a closed subset `T ⊆ |X|` is limit
preserving, for `X` an algebraic space locally of finite type over a locally Noetherian scheme. -/
theorem limitPreserving_completionSubfunctor [IsLocallyNoetherian S]
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hft : IsLocallyOfFiniteType B S hS (terminal.from X)) {T : Set (points B S hS X)}
    (hT : IsClosed T) :
    LimitPreserving.{u, u + 1, u, u, u + 1, u} (BigFppfOver.toScheme B S hS)
      (completionSubfunctor B S hS X T).toFunctor :=
  limitPreserving_of_natIso (completionSubfunctorIso B S hS X T).symm
    (limitPreserving_comp_uliftFunctor
      (limitPreserving_openSubspaceOfPoints B S hS hX hft hT))

/-- Let `S` be locally Noetherian, let `X` be an algebraic space locally of finite type over `S`
and let `T ⊆ |X|` be closed. The completion `X_{/T}` is limit preserving. -/
theorem limitPreserving_completionSheaf [IsLocallyNoetherian S]
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hft : IsLocallyOfFiniteType B S hS (terminal.from X)) {T : Set (points B S hS X)}
    (hT : IsClosed T) :
    LimitPreserving.{u, u + 1, u, u, u + 1, u} (BigFppfOver.toScheme B S hS)
      (completionSheaf B S hS X T).obj :=
  limitPreserving_of_natIso (completionSheafIsoSubfunctor B S hS hX.isSheaf T).symm
    (limitPreserving_completionSubfunctor B S hS hX hft hT)

end Space

namespace Artin.ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSituation B S hS) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (α : contractionFunctor c ≅ morOnLocallyNoetherian B S hS X)

/-- For an fppf sheaf `X` carrying a functorial bijection `F(V) = Mor_S(V, X)`, the restrictions of
the completion `X_{/T}` along the subset `T ⊆ |X|` of the solution and of `W` to the locally
Noetherian schemes over `S` are isomorphic. -/
noncomputable def completionSheafIsoW
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) :
    (ObjectProperty.ι (fun T : BigFppfOver B S hS =>
        IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))).op ⋙
        (Space.completionSheaf B S hS X (contractedLocus c α)).obj ≅
      (ObjectProperty.ι (fun T : BigFppfOver B S hS =>
        IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))).op ⋙ c.W.obj :=
  have := isIso_completionToW c α
  Functor.isoWhiskerLeft _ (Space.completionSheafIsoSubfunctor B S hS hX (contractedLocus c α)) ≪≫
    asIso (completionToW c α)

/-- The isomorphism `AlgebraicGeometry.Artin.ContractionSituation.completionSheafIsoW` is the
comparison morphism `AlgebraicGeometry.Artin.ContractionSituation.completionToW` precomposed with
the identification of `X_{/T}` with the subfunctor of sections with point-set image in `T`. -/
theorem completionSheafIsoW_hom (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) :
    (completionSheafIsoW c α hX).hom =
      Functor.whiskerLeft _ (Space.completionSheafIsoSubfunctor B S hS hX
        (contractedLocus c α)).hom ≫ completionToW c α := rfl

/-- The formal algebraic space `W` of a contraction situation is limit preserving. -/
theorem limitPreserving_W :
    LimitPreserving.{u, u + 1, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) c.W.obj :=
  have := c.isLocallyNoetherian_base
  FormalSpace.limitPreserving_of_isLocallyNoetherian_of_isReduction B S hS
    c.isLocallyNoetherian_W c.isReduction_WredInclusion c.isLocallyOfFiniteType_Wred

/-- Let `X` be an algebraic space locally of finite type over `S` carrying a functorial bijection
`F(V) = Mor_S(V, X)` on locally Noetherian schemes. There is a unique isomorphism of fppf sheaves
`X_{/T} ≅ W` whose restriction to the locally Noetherian schemes over `S` is
`AlgebraicGeometry.Artin.ContractionSituation.completionSheafIsoW`. -/
theorem existsUnique_completionSheafIso_W (hX : IsAlgebraicSpace B S hS X)
    (hft : Space.IsLocallyOfFiniteType B S hS (terminal.from X)) :
    ∃! a : Space.completionSheaf B S hS X (contractedLocus c α) ≅ c.W,
      Functor.isoWhiskerLeft (ObjectProperty.ι (fun T : BigFppfOver B S hS =>
          IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))).op
        ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mapIso a) =
        completionSheafIsoW c α hX.isSheaf := by
  have := c.isLocallyNoetherian_base
  obtain ⟨e, he, hu⟩ := ExtendingFunctors.existsUnique_iso_isoWhiskerLeft_eq_bigFppfOver B hS
    (Space.completionSheaf B S hS X (contractedLocus c α)).property
    (Space.limitPreserving_completionSheaf B S hS hX hft (isClosed_contractedLocus c α hX hft))
    c.W.property (limitPreserving_W c) (completionSheafIsoW c α hX.isSheaf)
  let ff := fullyFaithfulSheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))
  let e' : (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).obj
      (Space.completionSheaf B S hS X (contractedLocus c α)) ≅
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).obj c.W := e
  have h₁ : (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mapIso
      (ff.preimageIso e') = e := Iso.ext (by simp [ff, e'])
  refine ⟨ff.preimageIso e', by beta_reduce; rw [h₁]; exact he,
    fun a ha ↦ Iso.ext (ff.map_injective ?_)⟩
  simpa [ff, e'] using congrArg Iso.hom (hu _ ha)

/-- The isomorphism `X_{/T} ≅ W` of fppf sheaves on the big fppf site of `S` whose restriction
to locally Noetherian schemes is
`AlgebraicGeometry.Artin.ContractionSituation.completionSheafIsoW`. -/
noncomputable def completionSheafIsoWExt (hX : IsAlgebraicSpace B S hS X)
    (hft : Space.IsLocallyOfFiniteType B S hS (terminal.from X)) :
    Space.completionSheaf B S hS X (contractedLocus c α) ≅ c.W :=
  (existsUnique_completionSheafIso_W c α hX hft).exists.choose

/-- The isomorphism `AlgebraicGeometry.Artin.ContractionSituation.completionSheafIsoWExt`
restricts on locally Noetherian schemes to
`AlgebraicGeometry.Artin.ContractionSituation.completionSheafIsoW`. -/
theorem isoWhiskerLeft_completionSheafIsoWExt (hX : IsAlgebraicSpace B S hS X)
    (hft : Space.IsLocallyOfFiniteType B S hS (terminal.from X)) :
    Functor.isoWhiskerLeft (ObjectProperty.ι (fun T : BigFppfOver B S hS =>
        IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))).op
      ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mapIso
        (completionSheafIsoWExt c α hX hft)) =
      completionSheafIsoW c α hX.isSheaf :=
  (existsUnique_completionSheafIso_W c α hX hft).exists.choose_spec

end Artin.ContractionSituation

end AlgebraicGeometry

end
