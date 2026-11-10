module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ProperPartOverHenselianPair.Chow
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.SeparatedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Induction
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# Splitting off a proper part of an algebraic space over a henselian pair

Let `(A, I)` be a henselian pair and let `X` be an algebraic space separated and of finite type
over `A`.  An open and closed subspace of the closed fibre `X₀ = X ×_{Spec A} Spec (A/I)` which
is proper over `Spec (A/I)` is the closed fibre of an open and closed subspace of `X` which is
proper over `A`.  This is Stacks 0CWI, the algebraic-space form of the scheme statement
Stacks 0CT9.

## Main results

* `AlgebraicGeometry.Space.exists_isOpenSubspace_isClosedSubspace_isProper_of_henselianPair`:
  the extension, with the closed fibre of the subspace produced recorded as an isomorphism over
  the closed fibre of `X`.
* `AlgebraicGeometry.Space.isClopen_image_of_closed_fibres`: the image of an open and closed
  set under a closed surjection which is saturated over a subset `Z` of the base meeting every
  nonempty closed subset is open and closed.

## References

* [Stacks Project, Tag 0CWI](https://stacks.math.columbia.edu/tag/0CWI)
* [Stacks Project, Tag 0CT9](https://stacks.math.columbia.edu/tag/0CT9)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
* [Stacks Project, Tag 08AJ](https://stacks.math.columbia.edu/tag/08AJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### The topological descent step -/

/-- Let `p : E → X` be a continuous closed surjection, let `f : X → S`, and let `U ⊆ E` be open
and closed.  Assume that every nonempty closed subset of `S` meets `Z`, that the image in `S` of
every closed subset of `U` is closed, and that `U` is saturated along the fibres of `p` lying
over `Z`.  Then `p '' U` is open and closed and `U` is its full preimage. -/
theorem isClopen_image_of_closed_fibres
    {E X S : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [TopologicalSpace S] (p : E → X) (f : X → S)
    (hp : Function.Surjective p) (hpc : IsClosedMap p) (hcont : Continuous p)
    (U : Set E) (hU : IsClopen U) (Z : Set S)
    (hZ : ∀ K : Set S, IsClosed K → K.Nonempty → (K ∩ Z).Nonempty)
    (hproper : ∀ K : Set E, IsClosed K → K ⊆ U → IsClosed ((f ∘ p) '' K))
    (hfibre : ∀ a b : E, f (p a) ∈ Z → p a = p b → (a ∈ U ↔ b ∈ U)) :
    IsClopen (p '' U) ∧ p ⁻¹' (p '' U) = U := by
  have h₁ : IsClosed (p '' U) := hpc _ hU.1
  have h₂ : IsClosed (p '' Uᶜ) := hpc _ hU.2.isClosed_compl
  have hdisj : Disjoint (p '' U) (p '' Uᶜ) := by
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    let K := U ∩ p ⁻¹' (p '' Uᶜ)
    have hK : IsClosed K := hU.1.inter (h₂.preimage hcont)
    have hKne : K.Nonempty := by
      obtain ⟨a, ha, rfl⟩ := hx₁
      exact ⟨a, ha, hx₂⟩
    obtain ⟨s, ⟨a, ha, rfl⟩, hsZ⟩ :=
      hZ ((f ∘ p) '' K) (hproper K hK Set.inter_subset_left) (hKne.image _)
    obtain ⟨b, hb, hab⟩ := ha.2
    exact hb ((hfibre a b hsZ hab.symm).mp ha.1)
  have hcompl : (p '' U)ᶜ = p '' Uᶜ := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, rfl⟩ := hp x
      exact ⟨a, fun ha ↦ hx ⟨a, ha, rfl⟩, rfl⟩
    · intro hx hx'
      exact Set.disjoint_left.mp hdisj hx' hx
  refine ⟨⟨h₁, ?_⟩, ?_⟩
  · rw [← isClosed_compl_iff, hcompl]
    exact h₂
  · ext a
    constructor
    · intro ha
      by_contra hn
      exact Set.disjoint_left.mp hdisj ha ⟨a, hn, rfl⟩
    · intro ha
      exact ⟨a, ha, rfl⟩

/-! ### Properness of a base change, and properness read off the site -/

section Auxiliary

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Properness of morphisms of algebraic spaces over `S` is stable under base change, read on a
cartesian square of presheaves rather than on one in the category of algebraic spaces. -/
theorem isProper_of_isPullback_presheaf
    {P X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace B S hS P) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z)
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (sq : IsPullback a b f g) (hf : IsProper B S hS f) :
    IsProper B S hS b := by
  have sq' : IsPullback
      (ObjectProperty.homMk a : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
      (ObjectProperty.homMk b : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩)
      (ObjectProperty.homMk g : (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩) :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (IsAlgebraicSpace B S hS)) sq
  exact MorphismProperty.of_isPullback
    (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) ↦ IsProper B S hS k.hom) sq' hf

/-- The Yoneda image of a morphism of the site is proper exactly when that morphism is. -/
theorem isProper_yoneda_map_iff {U V : BigFppfOver B S hS} (f : U ⟶ V) :
    IsProper B S hS (yoneda.map f) ↔
      _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map f) :=
  (presheaf_isProper_iff B S hS (yoneda.map f) (isAlgebraicSpace_yoneda B S hS U)
        (isAlgebraicSpace_yoneda B S hS V)
        (Functor.relativelyRepresentable.map yoneda f)).trans
    (presheaf_yoneda_map_iff B S hS inferInstance f)

/-- The point set of one leg of a cartesian square is the preimage of the point set of the
opposite leg. -/
theorem preimage_range_pointsMap_of_isPullback
    {P X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (sq : IsPullback a b f g) :
    pointsMap B S hS Y g ⁻¹' Set.range (pointsMap B S hS X f) =
      Set.range (pointsMap B S hS P b) := by
  ext y
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨w, -, hw⟩ := exists_point_of_isPullback_presheaf B S hS sq x y hx
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    refine ⟨pointsMap B S hS P a w, ?_⟩
    change (pointsMap B S hS X f ∘ pointsMap B S hS P a) w =
      (pointsMap B S hS Y g ∘ pointsMap B S hS P b) w
    rw [← pointsMap_comp, ← pointsMap_comp, sq.w]

end Auxiliary

/-! ### Closed subsets of the base over a henselian pair -/

/-- For a henselian pair `(A, I)`, a nonempty closed subset of the point space of the presheaf
represented by `Spec A` meets the image of the points of `Spec (A/I)`. -/
theorem closed_meets_quotient_range
    (A : Type u) [CommRing A] (I : Ideal A) (hI : HenselianPair A I)
    (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of A))) (hT : B.Contains (Spec (.of (A ⧸ I))))
    (qSite : B.obj hT ⟶ B.obj hS)
    (hqSite : B.inclusion.map qSite =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    let T : BigFppfOver B (Spec (.of A)) hS := Over.mk qSite
    let base : BigFppfOver B (Spec (.of A)) hS := Over.mk (𝟙 (B.obj hS))
    let q : T ⟶ base := Over.homMk qSite (Category.comp_id _)
    letI := pointTopology B (Spec (.of A)) hS (yoneda.obj base)
    ∀ K : Set (points B (Spec (.of A)) hS (yoneda.obj base)),
      IsClosed K → K.Nonempty →
      (K ∩ Set.range (pointsMap B (Spec (.of A)) hS
        (yoneda.obj T) (yoneda.map q))).Nonempty := by
  intro T base q
  let := pointTopology B (Spec (.of A)) hS (yoneda.obj base)
  let := pointTopology B (Spec (.of A)) hS (yoneda.obj T)
  intro K hK hKne
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  let es := schemePointsHomeomorph B (Spec (.of A)) hS base
  have hmapq : (BigFppfOver.toScheme B (Spec (.of A)) hS).map q =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := hqSite
  have hsub : K ⊆ (∅ : Set (points B (Spec (.of A)) hS (yoneda.obj base))) := by
    refine subset_of_isClosed_of_forall_mem_zeroLocus I hI (fun x ↦ es x)
      es.isClosedMap hK isOpen_empty ?_
    intro x hx hxK
    have hxr : es x ∈ Set.range ((BigFppfOver.toScheme B (Spec (.of A)) hS).map q) := by
      rwa [hmapq, range_spec_map_quotient_mk I]
    obtain ⟨y, hy⟩ := hxr
    have hxmem : x ∈ Set.range (pointsMap B (Spec (.of A)) hS
        (yoneda.obj T) (yoneda.map q)) := by
      refine ⟨(schemePointsHomeomorph B (Spec (.of A)) hS T).symm y, ?_⟩
      rw [schemePointsHomeomorph_symm_naturality B (Spec (.of A)) hS q y, hy]
      exact es.symm_apply_apply x
    rw [← hempty]
    exact ⟨hxK, hxmem⟩
  exact hKne.ne_empty (Set.subset_empty_iff.mp hsub)

/-! ### Stacks 0CWI -/

/-- Let `(A, I)` be a henselian pair and let `X` be an algebraic space separated and of finite type
over `A`.  Let `Y` be an open and closed subspace of the closed fibre
`X₀ = X ×_{Spec A} Spec (A/I)` which is proper over `Spec (A/I)`.  Then there is an open and
closed subspace `W ⊆ X`, proper over `A`, with `W ×_{Spec A} Spec (A/I) = Y`, the equality of
closed fibres being an isomorphism `Y ≅ W ×_{Spec A} Spec (A/I)` compatible with the two
inclusions into `X₀`. -/
theorem exists_isOpenSubspace_isClosedSubspace_isProper_of_henselianPair
    (A : Type u) [CommRing A] (I : Ideal A) (hI : HenselianPair A I)
    (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of A))) (hT : B.Contains (Spec (.of (A ⧸ I))))
    (qSite : B.obj hT ⟶ B.obj hS)
    (hqSite : B.inclusion.map qSite =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    let S := Spec (CommRingCat.of A)
    let T : BigFppfOver B S hS := Over.mk qSite
    let base : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
    let q : yoneda.obj T ⟶ yoneda.obj base :=
      yoneda.map (Over.homMk qSite (Category.comp_id _) : T ⟶ base)
    ∀ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS X →
      ∀ (f : X ⟶ yoneda.obj base), IsSeparated B S hS f → IsFiniteType B S hS f →
      ∀ (Y : Subfunctor (pullback f q)), IsOpenSubspace B S hS Y → IsClosedSubspace B S hS Y →
      IsProper B S hS (Y.ι ≫ pullback.snd f q) →
      ∃ (W : Subfunctor X) (_ : IsOpenSubspace B S hS W)
        (_ : IsClosedSubspace B S hS W) (_ : IsProper B S hS (W.ι ≫ f)),
      let w₀ : pullback (W.ι ≫ f) q ⟶ pullback f q :=
          pullback.lift (pullback.fst (W.ι ≫ f) q ≫ W.ι)
            (pullback.snd (W.ι ≫ f) q) ((Category.assoc _ _ _).trans pullback.condition)
        ∃ e : Y.toFunctor ≅ pullback (W.ι ≫ f) q, e.hom ≫ w₀ = Y.ι := by
  intro S T base q X hX f hfSeparated hfFiniteType Y hYOpen hYClosed hYProper
  classical
  obtain ⟨T', φ, hφProper, hφSurjective, hQuasiProjective⟩ :=
    hasChowSchemeCover_of_isSeparated_isFiniteType B (CommRingCat.of A) hS X hX f
      hfSeparated hfFiniteType
  let Tscheme := (BigFppfOver.toScheme B S hS).obj T'
  let fT := B.inclusion.map T'.hom
  have hfTLocallyFiniteType : LocallyOfFiniteType fT :=
    _root_.AlgebraicGeometry.IsHQuasiProjective.locallyOfFiniteType hQuasiProjective
  have hfTQuasiCompact : QuasiCompact fT :=
    _root_.AlgebraicGeometry.IsHQuasiProjective.quasiCompact hQuasiProjective
  have hfTSeparated : _root_.AlgebraicGeometry.IsSeparated fT :=
    _root_.AlgebraicGeometry.IsHQuasiProjective.isSeparated hQuasiProjective
  let m : T' ⟶ base := Over.homMk T'.hom (by simp [base])
  let q' : T ⟶ base := Over.homMk qSite
  have hm : yoneda.map m = φ ≫ f :=
    (isTerminal_yoneda_obj_base B S hS).hom_ext _ _
  let U₀ := pullback m q'
  let a : yoneda.obj U₀ ⟶ yoneda.obj T' := yoneda.map (pullback.fst m q')
  let b : yoneda.obj U₀ ⟶ yoneda.obj T := yoneda.map (pullback.snd m q')
  have hab : a ≫ φ ≫ f = b ≫ q := by
    rw [← hm, ← yoneda.map_comp, ← yoneda.map_comp]
    exact congrArg yoneda.map pullback.condition
  have hlarge : IsPullback a b (φ ≫ f) q := by
    rw [← hm]
    exact (IsPullback.of_hasPullback m q').map yoneda
  let φ₀ : yoneda.obj U₀ ⟶ pullback f q :=
    pullback.lift (a ≫ φ) b (by simpa only [Category.assoc] using hab)
  have hφ₀ : IsPullback a φ₀ φ (pullback.fst f q) := by
    apply IsPullback.of_bot (v₂₁ := pullback.snd f q) (v₂₂ := f)
    · rw [show φ₀ ≫ pullback.snd f q = b from pullback.lift_snd _ _ _]
      exact hlarge
    · exact (pullback.lift_fst _ _ _).symm
    · exact IsPullback.of_hasPullback f q
  have hU₀ := isAlgebraicSpace_yoneda B S hS U₀
  have hUalg := isAlgebraicSpace_yoneda B S hS T'
  have hTalg := isAlgebraicSpace_yoneda B S hS T
  have hbase := isAlgebraicSpace_yoneda B S hS base
  have hX₀ := isAlgebraicSpace_pullback B S hS f q hX hTalg hbase
  have hφ₀Proper := isProper_of_isPullback_presheaf B S hS hU₀ hUalg hX₀ hX hφ₀ hφProper
  obtain ⟨V, j, β, hβ⟩ := hYOpen.2.rep φ₀
  have hjOpen : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map j) :=
    hYOpen.2.property φ₀ β j hβ
  have hjClosed : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map j) :=
    hYClosed.2.property φ₀ β j hβ
  have hV := isAlgebraicSpace_yoneda B S hS V
  have hβProper := isProper_of_isPullback_presheaf B S hS hV hU₀ hYOpen.1 hX₀
    hβ.flip hφ₀Proper
  have hjProper : _root_.AlgebraicGeometry.IsProper
      ((BigFppfOver.toScheme B S hS).map (j ≫ pullback.snd m q')) := by
    apply (isProper_yoneda_map_iff B S hS _).mp
    have heq : yoneda.map (j ≫ pullback.snd m q') =
        β ≫ (Y.ι ≫ pullback.snd f q) := by
      rw [Functor.map_comp]
      simpa only [Category.assoc, φ₀, pullback.lift_snd] using
        (hβ.w_assoc (pullback.snd f q)).symm
    rw [heq]
    exact isProper_comp B S hS hV hYOpen.1 hTalg β (Y.ι ≫ pullback.snd f q)
      hβProper hYProper
  let L := BigFppfOver.toScheme B S hS
  have : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      L).IsStableUnderBaseChange :=
    BigFppfOver.isStableUnderBaseChange_inverseImage B S hS _
  have : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) L).IsStableUnderBaseChange :=
    BigFppfOver.isStableUnderBaseChange_inverseImage B S hS _
  have hpbScheme : IsPullback (L.map (pullback.fst m q'))
      (L.map (pullback.snd m q')) fT
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
    have hp := (IsPullback.of_hasPullback m q').map L
    simpa only [L, BigFppfOver.toScheme, Functor.comp_map, Over.forget_map, m, q',
      Over.homMk_left, fT, hqSite] using hp
  let i := L.map j ≫ hpbScheme.isoPullback.hom
  have : _root_.AlgebraicGeometry.IsOpenImmersion i := by
    have := hjOpen
    dsimp only [i]
    infer_instance
  have : _root_.AlgebraicGeometry.IsClosedImmersion i := by
    have := hjClosed
    dsimp only [i]
    infer_instance
  have : _root_.AlgebraicGeometry.IsProper (i ≫ pullback.snd fT
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) := by
    simpa only [i, Category.assoc, hpbScheme.isoPullback_hom_snd,
      ← L.map_comp] using hjProper
  have := hfTLocallyFiniteType
  have := hfTQuasiCompact
  have := hfTSeparated
  obtain ⟨W', w, hwOpen, hwClosed, hwProper, e, he⟩ :=
    _root_.AlgebraicGeometry.exists_isClopen_isProper_of_henselianPair A I hI fT i
  have := hwOpen
  have := hwClosed
  have := hwProper
  have hW'size : B.Contains W' :=
    (Scheme.size_le_of_mono_quasiCompact w).trans_lt T'.left.property
  let Ws : BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (w ≫ fT) : B.obj hW'size ⟶ B.obj hS)
  let ws : Ws ⟶ T' := Over.homMk (ObjectProperty.homMk w)
  have hwsClosed : IsClosedImmersion B S hS (yoneda.map ws) :=
    MorphismProperty.relative_map (P := MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) L)
      hwClosed
  have hWs := isAlgebraicSpace_yoneda B S hS Ws
  have hwsProper : IsProper B S hS (yoneda.map ws ≫ φ ≫ f) := by
    rw [← hm, ← yoneda.map_comp]
    exact (isProper_yoneda_map_iff B S hS (ws ≫ m)).mpr hwProper
  let v : L.obj V ⟶ W' := e.hom ≫ pullback.fst (w ≫ fT)
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  have hvw : v ≫ w = L.map j ≫ L.map (pullback.fst m q') := by
    have h := congrArg (fun k ↦ k ≫ pullback.fst fT
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) he
    simpa only [i, v, Category.assoc, pullback.lift_fst,
      hpbScheme.isoPullback_hom_fst] using h
  have hvs : v ≫ w ≫ fT = B.inclusion.map V.hom := by
    rw [← Category.assoc, hvw, Category.assoc]
    change B.inclusion.map j.left ≫ B.inclusion.map (pullback.fst m q').left ≫
        B.inclusion.map T'.hom = _
    rw [← B.inclusion.map_comp, (pullback.fst m q').w,
      ← B.inclusion.map_comp, j.w]
  let vs : V ⟶ Ws := Over.homMk (ObjectProperty.homMk v) (B.inclusion.map_injective hvs)
  have hvws : vs ≫ ws = j ≫ pullback.fst m q' := L.map_injective hvw
  have hvsq : IsPullback vs (j ≫ pullback.snd m q') (ws ≫ m) q' := by
    apply IsPullback.of_map_of_faithful (F := L)
    have he₂ : e.hom ≫ pullback.snd (w ≫ fT)
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) =
        L.map (j ≫ pullback.snd m q') := by
      have h := congrArg (fun k ↦ k ≫ pullback.snd fT
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) he
      simpa only [i, Category.assoc, pullback.lift_snd,
        hpbScheme.isoPullback_hom_snd, L.map_comp] using h
    have hsq : IsPullback v (L.map (j ≫ pullback.snd m q')) (w ≫ fT)
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
      refine IsPullback.of_iso_pullback ⟨?_⟩ e rfl he₂
      change (e.hom ≫ pullback.fst (w ≫ fT)
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ≫ (w ≫ fT) = _
      rw [← he₂, Category.assoc, pullback.condition, Category.assoc]
    change IsPullback v (L.map (j ≫ pullback.snd m q'))
      (w ≫ fT) (B.inclusion.map qSite)
    rw [hqSite]
    exact hsq
  have hjsq : IsPullback vs j ws (pullback.fst m q') :=
    hvsq.of_bot hvws (IsPullback.of_hasPullback m q')
  let := pointTopology B S hS X
  let := pointTopology B S hS (yoneda.obj T')
  let := pointTopology B S hS (yoneda.obj Ws)
  let := pointTopology B S hS (yoneda.obj base)
  let p := pointsMap B S hS (yoneda.obj T') φ
  let g := pointsMap B S hS X f
  let r := pointsMap B S hS (yoneda.obj Ws) (yoneda.map ws)
  let U := Set.range r
  have hrClosed : IsClosedMap r :=
    isClosed_of_universallyClosed B S hS hUalg (yoneda.map ws)
      (isProper_of_isClosedImmersion B S hS hWs hUalg _ hwsClosed).2.2
  have hrOpen : IsOpenMap r := by
    refine isOpenMap_pointsMap_of_etale B S hS hUalg Ws (yoneda.map ws) ?_
    exact MorphismProperty.relative_map
      (P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) L)
      (f := ws) (show Etale w from inferInstance)
  have hU : IsClopen U :=
    ⟨by simpa [U] using hrClosed Set.univ isClosed_univ,
      by simpa [U] using hrOpen Set.univ isOpen_univ⟩
  have hp : Function.Surjective p := hφSurjective
  have hpClosed : IsClosedMap p :=
    isClosed_of_universallyClosed B S hS hX φ hφProper.2.2
  have hpContinuous : Continuous p := continuous_pointsMap B S hS φ
  have hrContinuous : Continuous r := continuous_pointsMap B S hS (yoneda.map ws)
  have hproper : ∀ K, IsClosed K → K ⊆ U → IsClosed ((g ∘ p) '' K) := by
    intro K hK hKU
    have h := isClosed_of_universallyClosed B S hS hbase
      (yoneda.map ws ≫ φ ≫ f) hwsProper.2.2 (r ⁻¹' K) (hK.preimage hrContinuous)
    have heq : r '' (r ⁻¹' K) = K := Set.image_preimage_eq_of_subset hKU
    rw [pointsMap_comp, pointsMap_comp] at h
    change IsClosed (((g ∘ p) ∘ r) '' (r ⁻¹' K)) at h
    rwa [Set.image_comp, heq] at h
  let Z := Set.range (pointsMap B S hS (yoneda.obj T) q)
  have hwpre := preimage_range_pointsMap_of_isPullback B S hS (hjsq.map yoneda)
  have hYpre := preimage_range_pointsMap_of_isPullback B S hS hβ
  have hcomp (z : points B S hS (yoneda.obj U₀)) :
      pointsMap B S hS (pullback f q) (pullback.fst f q)
          (pointsMap B S hS (yoneda.obj U₀) φ₀ z) =
        p (pointsMap B S hS (yoneda.obj U₀) a z) := by
    change (pointsMap B S hS (pullback f q) (pullback.fst f q) ∘
      pointsMap B S hS (yoneda.obj U₀) φ₀) z = (p ∘ pointsMap B S hS (yoneda.obj U₀) a) z
    rw [← pointsMap_comp, ← hφ₀.w, pointsMap_comp]
  have hmem (z : points B S hS (yoneda.obj U₀)) :
      pointsMap B S hS (yoneda.obj U₀) a z ∈ U ↔
        pointsMap B S hS (yoneda.obj U₀) φ₀ z ∈
          Set.range (pointsMap B S hS Y.toFunctor Y.ι) :=
    Set.ext_iff.mp (hwpre.trans hYpre.symm) z
  have hfibre : ∀ x y, g (p x) ∈ Z → p x = p y → (x ∈ U ↔ y ∈ U) := by
    intro x y hx hxy
    obtain ⟨t, ht⟩ := hx
    have hx' : pointsMap B S hS (yoneda.obj T') (φ ≫ f) x =
        pointsMap B S hS (yoneda.obj T) q t := by
      rw [pointsMap_comp]
      change g (p x) = _
      exact ht.symm
    have hy' : pointsMap B S hS (yoneda.obj T') (φ ≫ f) y =
        pointsMap B S hS (yoneda.obj T) q t := by
      rw [pointsMap_comp]
      change g (p y) = _
      rw [← hxy]
      exact ht.symm
    obtain ⟨x₀, hxx, -⟩ := exists_point_of_isPullback_presheaf B S hS hlarge x t hx'
    obtain ⟨y₀, hyy, -⟩ := exists_point_of_isPullback_presheaf B S hS hlarge y t hy'
    have : Mono qSite := by
      have : _root_.AlgebraicGeometry.IsClosedImmersion (B.inclusion.map qSite) := by
        rw [hqSite]
        exact _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
          Ideal.Quotient.mk_surjective
      exact Functor.mono_of_mono_map B.inclusion inferInstance
    have : Mono q' := by dsimp only [q']; infer_instance
    have : Mono q := by change Mono (yoneda.map q'); infer_instance
    have hequal : pointsMap B S hS (yoneda.obj U₀) φ₀ x₀ =
        pointsMap B S hS (yoneda.obj U₀) φ₀ y₀ := by
      apply pointsMap_injective_of_mono B S hS (pullback.fst f q)
      rw [hcomp, hcomp, hxx, hyy]
      exact hxy
    rw [← hxx, ← hyy, hmem, hmem, hequal]
  obtain ⟨hQ, hpreQ⟩ := isClopen_image_of_closed_fibres p g hp hpClosed hpContinuous
    U hU Z (closed_meets_quotient_range A I hI B hS hT qSite hqSite) hproper hfibre
  let Wopen := (openSubspacesOrderIso B S hS X hX).symm ⟨p '' U, hQ.2⟩
  let W := Wopen.1
  have hWOpen : IsOpenSubspace B S hS W := Wopen.2
  have hWrange : Set.range (pointsMap B S hS W.toFunctor W.ι) = p '' U := by
    rw [← openSubspacesOrderIso_apply B S hS X hX Wopen]
    exact congrArg (fun V : TopologicalSpace.Opens (points B S hS X) ↦ V.1)
      ((openSubspacesOrderIso B S hS X hX).apply_symm_apply _)
  have hWClosed : IsClosedSubspace B S hS W := by
    refine ⟨hWOpen.1, ?_⟩
    apply (isClosedImmersion_iff_isClosed_range_pointsMap B S hS hX W.ι
      (isImmersion_of_isOpenImmersion B S hS hWOpen.2)).mpr
    rw [hWrange]
    exact hQ.1
  let ψ := yoneda.map ws ≫ φ
  have hψrange : Set.range (pointsMap B S hS (yoneda.obj Ws) ψ) = p '' U := by
    change Set.range (pointsMap B S hS (yoneda.obj Ws) (yoneda.map ws ≫ φ)) = _
    rw [pointsMap_comp, Set.range_comp]
  obtain ⟨l, hl⟩ := (factorsThrough_openSubspace_iff_points B S hS hX hWs W hWOpen ψ).2
    (by rw [hψrange, hWrange])
  have hlSurj : IsSurjective B S hS l := by
    intro x
    have hx : pointsMap B S hS W.toFunctor W.ι x ∈
        Set.range (pointsMap B S hS (yoneda.obj Ws) ψ) := by
      rw [hψrange, ← hWrange]
      exact ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hx
    refine ⟨y, ?_⟩
    apply pointsMap_injective_of_mono B S hS W.ι
    change (pointsMap B S hS W.toFunctor W.ι ∘
      pointsMap B S hS (yoneda.obj Ws) l) y = _
    rwa [← pointsMap_comp, hl]
  have hWiProper := isProper_of_isClosedImmersion B S hS hWOpen.1 hX W.ι hWClosed.2
  have hWProper : IsProper B S hS (W.ι ≫ f) := by
    refine isProper_of_isSurjective_comp B S hS hWs hWOpen.1 hbase l (W.ι ≫ f)
      ?_ hlSurj ?_ ?_
    · rw [← Category.assoc, hl]
      exact hwsProper.2.2
    · exact isSeparated_comp B S hS W.ι f hWiProper.1 hfSeparated
    · exact isFiniteType_comp B S hS hWOpen.1 hX hbase W.ι f hWiProper.2.1 hfFiniteType
  let P := W.preimage (pullback.fst f q)
  have hPOpen := isOpenSubspace_preimage B S hS (pullback.fst f q) W hX hX₀ hWOpen
  have hPY : P = Y := by
    apply eq_of_range_pointsMap_ι_eq B S hS hPOpen hYOpen
    have hPrange := preimage_range_pointsMap_of_isPullback B S hS
      (Subfunctor.isPullback_preimage (pullback.fst f q) W)
    rw [← hPrange, hWrange]
    ext x
    obtain ⟨u, hu⟩ := hp (pointsMap B S hS (pullback f q) (pullback.fst f q) x)
    obtain ⟨z, hz, hzx⟩ := exists_point_of_isPullback_presheaf B S hS hφ₀ u x hu
    rw [← hzx]
    change pointsMap B S hS (pullback f q) (pullback.fst f q)
        (pointsMap B S hS (yoneda.obj U₀) φ₀ z) ∈ p '' U ↔ _
    rw [hcomp]
    exact (Set.ext_iff.mp hpreQ _).trans (hmem z)
  have hPsq := (Subfunctor.isPullback_preimage (pullback.fst f q) W).paste_vert
    (IsPullback.of_hasPullback f q)
  let e₀ : Y.toFunctor ≅ P.toFunctor := eqToIso (congrArg Subfunctor.toFunctor hPY.symm)
  have he₀ : e₀.hom ≫ P.ι = Y.ι := by
    subst hPY
    simp [e₀]
  refine ⟨W, hWOpen, hWClosed, hWProper, e₀.trans hPsq.isoPullback, ?_⟩
  apply pullback.hom_ext
  · simp only [Iso.trans_hom, Category.assoc, pullback.lift_fst,
      IsPullback.isoPullback_hom_fst_assoc]
    rw [Subfunctor.fromPreimage_ι, ← Category.assoc, he₀]
  · simp only [Iso.trans_hom, Category.assoc, pullback.lift_snd,
      IsPullback.isoPullback_hom_snd]
    rw [← Category.assoc, he₀]

end AlgebraicGeometry.Space

end
