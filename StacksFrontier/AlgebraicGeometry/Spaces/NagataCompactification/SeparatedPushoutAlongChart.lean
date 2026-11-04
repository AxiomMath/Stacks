module

public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryDistinguishedSquareGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SeparatedElementarySquarePushout
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.OffDiagonalChart
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange

/-!
# The separated pushout of the repaired gluing step of Stacks 0F4B

Let `Y` be an algebraic space, `U` and `N` algebraic spaces separated over `Y`, `j : U₁ ⟶ N` an
open immersion and `f : U₁ ⟶ U` a separated étale morphism over `Y`. Stacks 0DVJ glues `U` and `N`
along `U₁` to an algebraic space `W = U ⊔_{U₁} N`, in which `U` is open and `N ⟶ W` is étale and
an isomorphism over the complement of `U`. The square is cartesian, so the corrected form of
Stacks 0F45 applies: `W` is separated over `Y` as soon as

* the graph `U₁ ⟶ U ×_Y N` is a closed morphism, and
* for every closed set `K` of points of `U₁ ×_U U₁` off the diagonal, the image of `K` in
  `N ×_Y N` is closed.

For the chart `N` of `AlgebraicGeometry.Space.exists_isProper_offDiagonal_chart`, an open
subspace of a modification `X'` of the compactification of `U₁`, both conditions hold: the first
because the graph `V ⟶ U ×_Y X'` of the proper `ψ : V ⟶ U` is proper and `N` meets `V` only in
`U₁`, the second because `N ×_Y N` is the open part of `X' ×_Y X'` with both coordinates in `N`.
This gives the space `W₁` of the repaired proof of Stacks 0F4B.

## Main results

* `AlgebraicGeometry.Space.exists_isSeparated_isPushout_of_isClosedMap_offDiagonal`: the
  separated pushout.
* `AlgebraicGeometry.Space.isClosedMorphism_pullbackLift_openSubspaceOfPoints` and
  `AlgebraicGeometry.Space.isClosed_image_pullbackMap_openSubspaceOfPoints`: the two conditions
  for an open subspace given by a set of points.
* `AlgebraicGeometry.Space.exists_isSeparated_pushout_offDiagonal_chart`: the separated space
  `W₁ = U ⊔_{U₁} N`.
* `AlgebraicGeometry.Space.exists_isSeparated_pushout_of_isOpenImmersion`: the separated space
  `W₂`, glued along an open immersion.

## References

* [Stacks Project, Tag 0DVJ](https://stacks.math.columbia.edu/tag/0DVJ)
* [Stacks Project, Tag 0F45](https://stacks.math.columbia.edu/tag/0F45)
* [Stacks Project, Tag 0F4B](https://stacks.math.columbia.edu/tag/0F4B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Topology

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

/-- **Gluing along an étale map and an open immersion gives a separated space** (Stacks 0DVJ and
the corrected Stacks 0F45). Let `U` and `N` be separated over `Y`, `j : U₁ ⟶ N` an open immersion
and `f : U₁ ⟶ U` a separated étale morphism with `f ≫ q_U = j ≫ q_N`. If the graph
`U₁ ⟶ U ×_Y N` is closed and the image in `N ×_Y N` of every closed set of points of `U₁ ×_U U₁`
off the diagonal is closed, then the pushout `W = U ⊔_{U₁} N` of Stacks 0DVJ is separated over
`Y`. The square `U₁ ⟶ N ⟶ W ⟵ U ⟵ U₁` is an elementary distinguished square, a pushout of
algebraic spaces and a pullback. -/
theorem exists_isSeparated_isPushout_of_isClosedMap_offDiagonal {Y U N : AlgebraicSpaces B S hS}
    {U₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU₁ : IsAlgebraicSpace B S hS U₁) {j : U₁ ⟶ N.obj}
    (hj : IsOpenImmersion B S hS j) {f : U₁ ⟶ U.obj} (hf : IsEtale B S hS f)
    (hfsep : IsSeparated B S hS f) {qU : U.obj ⟶ Y.obj} {qN : N.obj ⟶ Y.obj}
    (hqU : IsSeparated B S hS qU) (hqN : IsSeparated B S hS qN) (hcomm : f ≫ qU = j ≫ qN)
    (hUV : IsClosedMorphism B S hS (pullback.lift f j hcomm : U₁ ⟶ pullback qU qN))
    (hO : ∀ K : Set (points B S hS (pullback f f)), IsClosed K →
      Disjoint K (Set.range (pointsMap B S hS U₁ (pullback.diagonal f))) →
      IsClosed (pointsMap B S hS _ (pullback.map f f qN qN j j qU hcomm hcomm) '' K)) :
    ∃ (W : AlgebraicSpaces B S hS) (Uw : Subfunctor W.obj) (e : U.obj ≅ Uw.toFunctor)
      (fW : N ⟶ W) (g : W.obj ⟶ Y.obj),
      IsElementaryDistinguishedSquare B S hS W.property Uw fW.hom ∧
      IsPullback j f fW.hom (e.hom ≫ Uw.ι) ∧
      IsPushout (ObjectProperty.homMk j : (⟨U₁, hU₁⟩ : AlgebraicSpaces B S hS) ⟶ N)
        (ObjectProperty.homMk f : (⟨U₁, hU₁⟩ : AlgebraicSpaces B S hS) ⟶ U) fW
        (ObjectProperty.homMk (e.hom ≫ Uw.ι) : U ⟶ W) ∧
      e.hom ≫ Uw.ι ≫ g = qU ∧ fW.hom ≫ g = qN ∧ IsSeparated B S hS g := by
  have : Mono j := mono_of_presheaf_isOpenImmersion hj
  let t := asIso (Subfunctor.toRange j)
  have ht : t.hom ≫ (Subfunctor.range j).ι = j := Subfunctor.toRange_ι j
  have hV' : IsOpenSubspace B S hS (Subfunctor.range j) :=
    isOpenSubspace_subfunctorRange B S hS hU₁ hj
  obtain ⟨W, Uw, e, fW, hsq, hP⟩ := exists_pushout_isElementaryDistinguishedSquare B S hS U N
    (Subfunctor.range j) hV' (t.inv ≫ f) (isEtale_comp B S hS (isEtale_of_isIso B S hS _) hf)
    (isSeparated_comp B S hS _ _ (isSeparated_of_isIso B S hS _) hfsep)
  have hpb₀ := isPullback_of_isPushout_of_isEtale_of_isSeparated B S hS (Subfunctor.range j) hV'
    (t.inv ≫ f) (isEtale_comp B S hS (isEtale_of_isIso B S hS _) hf)
    (isSeparated_comp B S hS _ _ (isSeparated_of_isIso B S hS _) hfsep) hP
  have hpb : IsPullback j f fW.hom (e.hom ≫ Uw.ι) :=
    hpb₀.of_iso t.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [← ht]) (by simp) (by simp) (by simp)
  -- the isomorphism of the two copies of `U₁` as algebraic spaces
  let T : (⟨U₁, hU₁⟩ : AlgebraicSpaces B S hS) ≅ ⟨(Subfunctor.range j).toFunctor, hV'.1⟩ :=
    { hom := ObjectProperty.homMk t.hom
      inv := ObjectProperty.homMk t.inv
      hom_inv_id := by ext1; exact t.hom_inv_id
      inv_hom_id := by ext1; exact t.inv_hom_id }
  have hP' : IsPushout (ObjectProperty.homMk j : (⟨U₁, hU₁⟩ : AlgebraicSpaces B S hS) ⟶ N)
      (ObjectProperty.homMk f : (⟨U₁, hU₁⟩ : AlgebraicSpaces B S hS) ⟶ U) fW
      (ObjectProperty.homMk (e.hom ≫ Uw.ι) : U ⟶ W) :=
    hP.of_iso T.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by ext1; simp [T, ← ht]) (by ext1; simp [T]) (by simp) (by simp)
  let gW : W ⟶ Y := hP'.desc (ObjectProperty.homMk qN) (ObjectProperty.homMk qU)
    (by ext1; exact hcomm.symm)
  have hgN : fW.hom ≫ gW.hom = qN := congrArg InducedCategory.Hom.hom
    (hP'.inl_desc (ObjectProperty.homMk qN) (ObjectProperty.homMk qU) (by ext1; exact hcomm.symm))
  have hgU : e.hom ≫ Uw.ι ≫ gW.hom = qU := by
    simpa only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      Category.assoc] using congrArg InducedCategory.Hom.hom
        (hP'.inr_desc (ObjectProperty.homMk qN) (ObjectProperty.homMk qU)
          (by ext1; exact hcomm.symm))
  exact ⟨W, Uw, e, fW, gW.hom, hsq, hpb, hP', hgU, hgN,
    isSeparated_of_isPullback_of_isClosedMap_offDiagonal Y.2 W.2 N.2 hU₁ U.2 hsq hpb hf gW.hom
      hgU hgN hqU hqN hcomm hUV hO⟩

/-! ### The two conditions on an open subspace of points -/

section Bridge

variable {X Y V U U₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Nset : Set (points B S hS X)}

/-- An open immersion induces an open embedding on points. -/
private theorem isOpenEmbedding_pointsMap_of_openImmersion {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} (hf : IsOpenImmersion B S hS f) : IsOpenEmbedding (pointsMap B S hS F f) :=
  have : Mono f := mono_of_presheaf_isOpenImmersion hf
  .of_continuous_injective_isOpenMap (continuous_pointsMap B S hS _)
    (pointsMap_injective_of_mono B S hS _) (isOpenMap_pointsMap_of_isOpenImmersion B S hS _ hf)

/-- An open immersion into `X` whose points lie in `Nset` factors through the open immersion
`openSubspaceOfPoints X Nset`. -/
private theorem exists_openImmersion_lift_openSubspaceOfPoints {e : U₁ ⟶ X}
    (he : IsOpenImmersion B S hS e) (hN : Set.range (pointsMap B S hS U₁ e) ⊆ Nset) :
    ∃ jN : U₁ ⟶ (openSubspaceOfPoints B S hS X Nset).toFunctor,
      jN ≫ (openSubspaceOfPoints B S hS X Nset).ι = e ∧ IsOpenImmersion B S hS jN := by
  have hle : Subfunctor.range e ≤ openSubspaceOfPoints B S hS X Nset :=
    (range_le_openSubspaceOfPoints_range_pointsMap e).trans (openSubspaceOfPoints_mono B S hS hN)
  refine ⟨Subfunctor.lift e hle, Subfunctor.lift_ι _ _, ?_⟩
  exact isOpenImmersion_of_comp_mono B S hS _ (openSubspaceOfPoints B S hS X Nset).ι
    (by rwa [Subfunctor.lift_ι])

/-- **The graph `U₁ ⟶ U ×_Y N` is closed.** Let `ψ : V ⟶ U` be proper, `ι : V ⟶ X` an open
immersion over `Y` with `π : X ⟶ Y` separated, and `j : U₁ ⟶ V` an open immersion. Let `N` be the
open subspace on a set of points of `X` which meets `V` only in `U₁`, and `j_N : U₁ ⟶ N` the
factorization of `j ≫ ι`. Then `(j ≫ ψ, j_N) : U₁ ⟶ U ×_Y N` is a closed morphism: the graph
`V ⟶ U ×_Y X` is proper, and the points of its image over `N` come from `U₁`. -/
theorem isClosedMorphism_pullbackLift_openSubspaceOfPoints (hV : IsAlgebraicSpace B S hS V)
    (hU : IsAlgebraicSpace B S hS U) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) {ψ : V ⟶ U} {ι : V ⟶ X} {q : U ⟶ Y} {π : X ⟶ Y}
    (hψ : IsProper B S hS ψ) (hπ : IsSeparated B S hS π) (hι : IsOpenImmersion B S hS ι)
    (h : ψ ≫ q = ι ≫ π) {j : U₁ ⟶ V} (hj : IsOpenImmersion B S hS j) (hNo : IsOpen Nset)
    (hN : Nset ∩ Set.range (pointsMap B S hS V ι) ⊆ Set.range (pointsMap B S hS U₁ (j ≫ ι)))
    {jN : U₁ ⟶ (openSubspaceOfPoints B S hS X Nset).toFunctor}
    (hjN : jN ≫ (openSubspaceOfPoints B S hS X Nset).ι = j ≫ ι)
    (hcomm : (j ≫ ψ) ≫ q = jN ≫ (openSubspaceOfPoints B S hS X Nset).ι ≫ π) :
    IsClosedMorphism B S hS (pullback.lift (j ≫ ψ) jN hcomm :
      U₁ ⟶ pullback q ((openSubspaceOfPoints B S hS X Nset).ι ≫ π)) := by
  have : Mono ι := mono_of_presheaf_isOpenImmersion hι
  have : Mono j := mono_of_presheaf_isOpenImmersion hj
  have hΓ := isProper_pullbackLift_of_isProper B S hS hV hU hX hY hψ hπ h
  have hP : IsAlgebraicSpace B S hS (pullback q π) := isAlgebraicSpace_pullback B S hS q π hU hX hY
  have hΓcl : IsClosedMap (pointsMap B S hS V (pullback.lift ψ ι h)) :=
    isClosedMap_pointsMap_of_pullback_fst_id B S hS _ (hΓ.2.2 _ hP (𝟙 _))
  let ιN := pullback.map q ((openSubspaceOfPoints B S hS X Nset).ι ≫ π) q π (𝟙 U)
    (openSubspaceOfPoints B S hS X Nset).ι (𝟙 Y) (by simp) (by simp)
  have hιN : IsOpenImmersion B S hS ιN := isOpenImmersion_snd_of_isPullback
    (isPullback_pullbackMap_snd (openSubspaceOfPoints B S hS X Nset).ι π q).flip
    (isOpenSubspace_openSubspaceOfPoints B S hS hX Nset hNo).2
  have : Mono ιN := mono_of_presheaf_isOpenImmersion hιN
  have hιNemb := isOpenEmbedding_pointsMap_of_openImmersion hιN
  have hjemb := isOpenEmbedding_pointsMap_of_openImmersion hj
  have hfac : pullback.lift (j ≫ ψ) jN hcomm ≫ ιN = j ≫ pullback.lift ψ ι h := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.assoc, pullback.lift_fst,
        pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, hjN,
        Category.assoc, pullback.lift_snd]
  intro C hC
  rw [hιNemb.isInducing.isClosed_iff]
  refine ⟨pointsMap B S hS _ (pullback.lift ψ ι h) '' closure (pointsMap B S hS _ j '' C),
    hΓcl _ isClosed_closure, ?_⟩
  ext z
  constructor
  · rintro ⟨v, hv, hvz⟩
    have hsnd : pointsMap B S hS _ (pullback.snd q π) (pointsMap B S hS _ ιN z) ∈ Nset := by
      rw [← pointsMap_comp_apply, show ιN ≫ pullback.snd q π =
          pullback.snd q ((openSubspaceOfPoints B S hS X Nset).ι ≫ π) ≫
          (openSubspaceOfPoints B S hS X Nset).ι from pullback.lift_snd _ _ _,
        pointsMap_comp_apply]
      exact (range_pointsMap_ι_openSubspaceOfPoints B S hS Nset).subset ⟨_, rfl⟩
    rw [← hvz, ← pointsMap_comp_apply, pullback.lift_snd] at hsnd
    obtain ⟨x, hx⟩ := hN ⟨hsnd, v, rfl⟩
    have hxv : pointsMap B S hS _ j x = v := pointsMap_injective_of_mono B S hS ι
      (by rw [← pointsMap_comp_apply, hx])
    have hxC : x ∈ C := by
      rw [← hC.closure_eq, hjemb.isInducing.closure_eq_preimage_closure_image, Set.mem_preimage,
        hxv]
      exact hv
    refine ⟨x, hxC, hιNemb.injective ?_⟩
    rw [← pointsMap_comp_apply, hfac, pointsMap_comp_apply, hxv, hvz]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨pointsMap B S hS _ j x, subset_closure ⟨x, hx, rfl⟩, ?_⟩
    rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, hfac]

/-- **Closed sets off the diagonal have closed image in `N ×_Y N`.** Let `N` be the open subspace
on an open set of points of `X`, and `j_N : U₁ ⟶ N` a factorization of `e : U₁ ⟶ X`. If the image
of a set `K` of points of `U₁ ×_U U₁` in `X ×_Y X` is closed among the points with both coordinates
in `N`, then its image in `N ×_Y N` is closed: `N ×_Y N ⟶ X ×_Y X` is an open immersion whose
points are those with both coordinates in `N`. -/
theorem isClosed_image_pullbackMap_openSubspaceOfPoints (hX : IsAlgebraicSpace B S hS X)
    (hNo : IsOpen Nset) {π : X ⟶ Y} {f : U₁ ⟶ U} {e : U₁ ⟶ X} {q : U ⟶ Y}
    {jN : U₁ ⟶ (openSubspaceOfPoints B S hS X Nset).toFunctor}
    (hjN : jN ≫ (openSubspaceOfPoints B S hS X Nset).ι = e)
    (hcomm : f ≫ q = jN ≫ (openSubspaceOfPoints B S hS X Nset).ι ≫ π)
    {K : Set (points B S hS (pullback f f))}
    (hK : ∀ ρ : pullback f f ⟶ pullback π π, ρ ≫ pullback.fst π π = pullback.fst f f ≫ e →
      ρ ≫ pullback.snd π π = pullback.snd f f ≫ e →
      closure (pointsMap B S hS _ ρ '' K) ∩
          (pointsMap B S hS _ (pullback.fst π π) ⁻¹' Nset ∩
            pointsMap B S hS _ (pullback.snd π π) ⁻¹' Nset) ⊆
        pointsMap B S hS _ ρ '' K) :
    IsClosed (pointsMap B S hS _ (pullback.map f f ((openSubspaceOfPoints B S hS X Nset).ι ≫ π)
      ((openSubspaceOfPoints B S hS X Nset).ι ≫ π) jN jN q hcomm hcomm) '' K) := by
  let ιNN := pullback.map ((openSubspaceOfPoints B S hS X Nset).ι ≫ π)
    ((openSubspaceOfPoints B S hS X Nset).ι ≫ π) π π (openSubspaceOfPoints B S hS X Nset).ι
    (openSubspaceOfPoints B S hS X Nset).ι (𝟙 Y) (by simp) (by simp)
  have hιNN : IsOpenImmersion B S hS ιNN :=
    isOpenImmersion_pullbackMap_of_isOpenImmersion _ π
      (isOpenSubspace_openSubspaceOfPoints B S hS hX Nset hNo).2
  have : Mono ιNN := mono_of_presheaf_isOpenImmersion hιNN
  have hemb := isOpenEmbedding_pointsMap_of_openImmersion hιNN
  let m := pullback.map f f ((openSubspaceOfPoints B S hS X Nset).ι ≫ π)
      ((openSubspaceOfPoints B S hS X Nset).ι ≫ π) jN jN q hcomm hcomm
  have h₁ : (m ≫ ιNN) ≫ pullback.fst π π = pullback.fst f f ≫ e := by
    simp [m, ιNN, ← hjN]
  have h₂ : (m ≫ ιNN) ≫ pullback.snd π π = pullback.snd f f ≫ e := by
    simp [m, ιNN, ← hjN]
  have hNpts : ∀ {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (g : P ⟶ (openSubspaceOfPoints B S hS X Nset).toFunctor) (z : points B S hS P),
      pointsMap B S hS P (g ≫ (openSubspaceOfPoints B S hS X Nset).ι) z ∈ Nset := by
    intro P g z
    rw [pointsMap_comp_apply]
    exact (range_pointsMap_ι_openSubspaceOfPoints B S hS Nset).subset ⟨_, rfl⟩
  rw [hemb.isInducing.isClosed_iff]
  refine ⟨closure (pointsMap B S hS _ (m ≫ ιNN) '' K), isClosed_closure, ?_⟩
  ext z
  constructor
  · intro hz
    have hmem := hK (m ≫ ιNN) h₁ h₂ ⟨hz, ?_, ?_⟩
    · obtain ⟨k, hk, hkz⟩ := hmem
      exact ⟨k, hk, hemb.injective (by rw [← pointsMap_comp_apply, hkz])⟩
    · rw [Set.mem_preimage, ← pointsMap_comp_apply,
        show ιNN ≫ pullback.fst π π = pullback.fst _ _ ≫ (openSubspaceOfPoints B S hS X Nset).ι
          from pullback.lift_fst _ _ _]
      exact hNpts _ z
    · rw [Set.mem_preimage, ← pointsMap_comp_apply,
        show ιNN ≫ pullback.snd π π = pullback.snd _ _ ≫ (openSubspaceOfPoints B S hS X Nset).ι
          from pullback.lift_snd _ _ _]
      exact hNpts _ z
  · rintro ⟨k, hk, rfl⟩
    exact subset_closure ⟨k, hk, by rw [pointsMap_comp_apply]⟩

end Bridge

/-! ### The space `W₁` -/

section Gluing

variable {X Y : AlgebraicSpaces B S hS} {π : X ⟶ Y} {V U U₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {ι : V ⟶ X.1} {ψ : V ⟶ U} {q : U ⟶ Y.1} {j : U₁ ⟶ V}

/-- **The separated space `W₁` of the repaired gluing step of Stacks 0F4B.** Let `π : X ⟶ Y` be
proper over a Noetherian `Y`, `ι : V ⟶ X` an open immersion, `ψ : V ⟶ U` proper with
`ψ ≫ q = ι ≫ π` and `q` separated, and `j : U₁ ⟶ V` an open immersion with `f = j ≫ ψ` separated,
étale, and an isomorphism over the reduced closed subspace on a closed set `Z ⊆ |U|`. Then there
are a proper `b : X' ⟶ X` with a lift `ι'` of `ι`, an open subspace `N` of `X'` containing `U₁`
and the closure of `f⁻¹ Z` and meeting `V` only in `U₁`, and the pushout `W = U ⊔_{U₁} N` of
Stacks 0DVJ, which is separated over `Y`. -/
theorem exists_isSeparated_pushout_offDiagonal_chart (hZ : B.Contains (⊤_ Scheme.{u}))
    (hπ : IsProper B S hS π.hom) (hYN : IsNoetherian B S hS hZ Y.1)
    (hV : IsAlgebraicSpace B S hS V) (hU : IsAlgebraicSpace B S hS U)
    (hU₁ : IsAlgebraicSpace B S hS U₁) (hψ : IsProper B S hS ψ) (hq : IsSeparated B S hS q)
    (hι : IsOpenImmersion B S hS ι) (hj : IsOpenImmersion B S hS j) (h : ψ ≫ q = ι ≫ π.hom)
    (hf : IsEtale B S hS (j ≫ ψ)) (hfsep : IsSeparated B S hS (j ≫ ψ))
    (Zs : Set (points B S hS U)) (hZs : IsClosed Zs)
    (hiso : IsIso ((reducedClosedSubspace B S hS U hU Zs hZs).fromPreimage (j ≫ ψ))) :
    ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X) (ι' : V ⟶ X'.1)
      (Nset : Set (points B S hS X'.1)) (_ : IsOpen Nset)
      (jN : U₁ ⟶ (openSubspaceOfPoints B S hS X'.1 Nset).toFunctor)
      (W : AlgebraicSpaces B S hS) (Uw : Subfunctor W.obj) (e : U ≅ Uw.toFunctor)
      (fW : (openSubspaceOfPoints B S hS X'.1 Nset).toFunctor ⟶ W.obj) (g : W.obj ⟶ Y.obj),
      IsProper B S hS b.hom ∧ ι' ≫ b.hom = ι ∧ IsOpenImmersion B S hS ι' ∧
      pointsMap B S hS _ b.hom ⁻¹' Set.range (pointsMap B S hS V ι) =
        Set.range (pointsMap B S hS V ι') ∧
      jN ≫ (openSubspaceOfPoints B S hS X'.1 Nset).ι = j ≫ ι' ∧
      Nset ∩ Set.range (pointsMap B S hS V ι') ⊆ Set.range (pointsMap B S hS U₁ (j ≫ ι')) ∧
      closure (pointsMap B S hS U₁ (j ≫ ι') '' (pointsMap B S hS U₁ (j ≫ ψ) ⁻¹' Zs)) ⊆ Nset ∧
      IsElementaryDistinguishedSquare B S hS W.property Uw fW ∧
      IsPullback jN (j ≫ ψ) fW (e.hom ≫ Uw.ι) ∧
      e.hom ≫ Uw.ι ≫ g = q ∧
      fW ≫ g = (openSubspaceOfPoints B S hS X'.1 Nset).ι ≫ (b ≫ π).hom ∧
      IsSeparated B S hS g := by
  obtain ⟨X', b, ι', Nset, hb, hι', hι'o, hpre, hNo, hN₁, hN₂, hN₃, hN₄⟩ :=
    exists_isProper_offDiagonal_chart hZ hπ hYN hV hU hU₁ hψ hι hj h hf Zs hZs hiso
  have hπ' : IsProper B S hS (b ≫ π).hom := isProper_comp B S hS X'.2 X.2 Y.2 _ _ hb hπ
  have hNs := isOpenSubspace_openSubspaceOfPoints B S hS X'.2 Nset hNo
  obtain ⟨jN, hjN, hjNo⟩ := exists_openImmersion_lift_openSubspaceOfPoints
    (isOpenImmersion_comp B S hS _ _ hj hι'o) hN₁
  have h' : ψ ≫ q = ι' ≫ (b ≫ π).hom := by
    rw [h, ← hι', ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
  have hcomm : (j ≫ ψ) ≫ q = jN ≫ (openSubspaceOfPoints B S hS X'.1 Nset).ι ≫ (b ≫ π).hom := by
    rw [reassoc_of% hjN, Category.assoc, h']
  obtain ⟨W, Uw, e, fW, g, hsq, hpb, -, hgU, hgN, hg⟩ :=
    exists_isSeparated_isPushout_of_isClosedMap_offDiagonal (Y := Y) (U := ⟨U, hU⟩)
      (N := ⟨_, hNs.1⟩) hU₁ hjNo hf hfsep hq
      (isSeparated_comp B S hS _ _ (isSeparated_of_mono B S hS _ inferInstance) hπ'.1) hcomm
      (isClosedMorphism_pullbackLift_openSubspaceOfPoints hV hU X'.2 Y.2 hψ hπ'.1 hι'o h' hj hNo
        hN₂ hjN hcomm)
      (fun K hK hKΔ => isClosed_image_pullbackMap_openSubspaceOfPoints X'.2 hNo hjN hcomm
        (hN₄ (b ≫ π) rfl · · · K hK hKΔ))
  exact ⟨X', b, ι', Nset, hNo, jN, W, Uw, e, fW.hom, g, hb, hι', hι'o, hpre, hjN, hN₂, hN₃, hsq,
    hpb, hgU, hgN, hg⟩

/-- **The separated space `W₂` of the repaired gluing step of Stacks 0F4B.** Let `π : X ⟶ Y` be
separated, `ι : V ⟶ X` an open immersion, `ψ : V ⟶ U` proper with `ψ ≫ q = ι ≫ π` and `q`
separated, and `j : U₁ ⟶ V` an open immersion with `j ≫ ψ` an open immersion (the open `U₂ ⊆ U` of
the source, extended to `V = V₂` by Stacks 0F4A). Let `N` be the open subspace of `X` off the
closure of `V ∖ U₁`. Then the pushout `W = U ⊔_{U₁} N` of Stacks 0DVJ is separated over `Y`: the
graph `U₁ ⟶ U ×_Y N` is closed because `N` meets `V` only in `U₁`, and `U₁ ×_U U₁` is its
diagonal. -/
theorem exists_isSeparated_pushout_of_isOpenImmersion (hπ : IsSeparated B S hS π.hom)
    (hV : IsAlgebraicSpace B S hS V) (hU : IsAlgebraicSpace B S hS U)
    (hU₁ : IsAlgebraicSpace B S hS U₁) (hψ : IsProper B S hS ψ) (hq : IsSeparated B S hS q)
    (hι : IsOpenImmersion B S hS ι) (hj : IsOpenImmersion B S hS j) (h : ψ ≫ q = ι ≫ π.hom)
    (hf : IsOpenImmersion B S hS (j ≫ ψ)) :
    ∃ (jN : U₁ ⟶ (openSubspaceOfPoints B S hS X.1
        (closure (pointsMap B S hS V ι '' (Set.range (pointsMap B S hS U₁ j))ᶜ))ᶜ).toFunctor)
      (W : AlgebraicSpaces B S hS) (Uw : Subfunctor W.obj) (e : U ≅ Uw.toFunctor)
      (fW : (openSubspaceOfPoints B S hS X.1
        (closure (pointsMap B S hS V ι '' (Set.range (pointsMap B S hS U₁ j))ᶜ))ᶜ).toFunctor ⟶
          W.obj) (g : W.obj ⟶ Y.obj),
      jN ≫ (openSubspaceOfPoints B S hS X.1
        (closure (pointsMap B S hS V ι '' (Set.range (pointsMap B S hS U₁ j))ᶜ))ᶜ).ι = j ≫ ι ∧
      IsElementaryDistinguishedSquare B S hS W.property Uw fW ∧
      IsPullback jN (j ≫ ψ) fW (e.hom ≫ Uw.ι) ∧
      e.hom ≫ Uw.ι ≫ g = q ∧
      fW ≫ g = (openSubspaceOfPoints B S hS X.1
        (closure (pointsMap B S hS V ι '' (Set.range (pointsMap B S hS U₁ j))ᶜ))ᶜ).ι ≫ π.hom ∧
      IsSeparated B S hS g := by
  have : Mono ι := mono_of_presheaf_isOpenImmersion hι
  have : Mono (j ≫ ψ) := mono_of_presheaf_isOpenImmersion hf
  set Nset := (closure (pointsMap B S hS V ι '' (Set.range (pointsMap B S hS U₁ j))ᶜ))ᶜ
  have hNo : IsOpen Nset := isClosed_closure.isOpen_compl
  have hNs := isOpenSubspace_openSubspaceOfPoints B S hS X.2 Nset hNo
  have hιinj := pointsMap_injective_of_mono B S hS ι
  have hN₂ : Nset ∩ Set.range (pointsMap B S hS V ι) ⊆ Set.range (pointsMap B S hS U₁ (j ≫ ι)) := by
    rintro _ ⟨hx, v, rfl⟩
    by_contra hv
    refine hx (subset_closure ⟨v, fun ⟨y, hy⟩ => hv ⟨y, ?_⟩, rfl⟩)
    rw [pointsMap_comp_apply, hy]
  have hN₁ : Set.range (pointsMap B S hS U₁ (j ≫ ι)) ⊆ Nset := by
    have hjopen : IsOpen (Set.range (pointsMap B S hS U₁ j)) :=
      (isOpenMap_pointsMap_of_isOpenImmersion B S hS _ hj).isOpen_range
    have hιemb := isOpenEmbedding_pointsMap_of_openImmersion hι
    rintro _ ⟨y, rfl⟩ hy
    obtain ⟨v, hv, hve⟩ := (hιemb.closure_image_inter_range hjopen.isClosed_compl).subset
      ⟨hy, pointsMap B S hS _ j y, by rw [pointsMap_comp_apply]⟩
    exact hv ⟨y, hιinj (by rw [hve, pointsMap_comp_apply])⟩
  obtain ⟨jN, hjN, hjNo⟩ := exists_openImmersion_lift_openSubspaceOfPoints
    (isOpenImmersion_comp B S hS _ _ hj hι) hN₁
  have hcomm : (j ≫ ψ) ≫ q = jN ≫ (openSubspaceOfPoints B S hS X.1 Nset).ι ≫ π.hom := by
    rw [reassoc_of% hjN, Category.assoc, h]
  have : IsIso (pullback.diagonal (j ≫ ψ)) := (pullback.isIso_diagonal_iff _).2 inferInstance
  obtain ⟨W, Uw, e, fW, g, hsq, hpb, -, hgU, hgN, hg⟩ :=
    exists_isSeparated_isPushout_of_isClosedMap_offDiagonal (Y := Y) (U := ⟨U, hU⟩)
      (N := ⟨_, hNs.1⟩) hU₁ hjNo (isEtale_of_isOpenImmersion B S hS hf)
      (isSeparated_of_mono B S hS _ inferInstance) hq
      (isSeparated_comp B S hS _ _ (isSeparated_of_mono B S hS _ inferInstance) hπ) hcomm
      (isClosedMorphism_pullbackLift_openSubspaceOfPoints hV hU X.2 Y.2 hψ hπ hι h hj hNo
        hN₂ hjN hcomm)
      (fun K _ hKΔ => by
        rw [show K = ∅ from Set.eq_empty_of_forall_notMem fun k hk => Set.disjoint_left.1 hKΔ hk
          ((pointsMap_surjective_of_isIso B S hS _) k), Set.image_empty]
        exact isClosed_empty)
  exact ⟨jN, W, Uw, e, fW.hom, g, hjN, hsq, hpb, hgU, hgN, hg⟩

end Gluing

end AlgebraicGeometry.Space

end
