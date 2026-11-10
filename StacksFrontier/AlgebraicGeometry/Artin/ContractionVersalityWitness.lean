module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionVersalityFormal
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionModificationMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtInfinitesimalLifting
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ModificationOutputQuasiCompact
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionLiftGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType

/-!
# The compatibility witness is smooth over `Z` when `x̂` is formally smooth

In the situation of Stacks 0GH8 let `ξ = (Z, u', x̂) ∈ F(V)` and let `V' ⟶ V`, `x̂'`, `x'` witness
the compatibility between `u'` and `x̂`. The second case of the proof of Stacks 0GIA observes that
`x̂' : V'_{/Z} ⟶ X'_{/T'}` is smooth as a base change of `x̂`, and that this makes `x' : V' ⟶ X'`
smooth at every point of `V'` over `Z` by More on Morphisms of Spaces, Lemma 0APN. This file
proves that, from the lifting property of `x̂` along nilpotent thickenings near a point of `Z`
(the form in which formal smoothness of `x̂` is used): a small extension problem for `x'` at a
point of `V'` over `Z` is, through the cartesian square `V'_{/Z} = V_{/Z} ×_W X'_{/T'}`, a lifting
problem for `x̂`.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.CompatibilityWitness.liftsAt_x'`: the lifting
  property of `x'` against small extensions at points of `V'` over `Z`.
* `AlgebraicGeometry.Artin.ContractionSituation.CompatibilityWitness.isSmoothAt_x'`: `x'` is
  smooth at those points (Stacks 0APN, (3) ⟹ (1)).

## References

* [Stacks Project, Tag 0APN](https://stacks.math.columbia.edu/tag/0APN)
* [Stacks Project, Tag 0GIA](https://stacks.math.columbia.edu/tag/0GIA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-! ### Thickenings presented through isomorphisms -/

section TestMaps

/-- The morphism of spectra induced by a surjection of Artinian local rings, read through
isomorphisms of schemes, has nilpotent kernel on global sections. -/
theorem isNilpotent_ker_appTop_of_iso_specMap {R' R : CommRingCat.{u}} [IsArtinianRing R']
    [IsLocalRing R'] [Nontrivial R] (f : R' ⟶ R)
    {X Y : Scheme.{u}} (e : X ≅ Spec R) (e' : Y ≅ Spec R') (m : X ⟶ Y)
    (hm : m = e.hom ≫ Spec.map f ≫ e'.inv) :
    IsNilpotent (RingHom.ker m.appTop.hom) := by
  have h₀ := isNilpotent_ker_appTop_of_eq_specMap f rfl rfl (Spec.map f)
    (by simp only [eqToHom_refl, Category.id_comp, Category.comp_id])
  obtain ⟨n, hn⟩ := h₀
  subst hm
  have : IsIso e.hom.appTop := by change IsIso (e.hom.app ⊤); infer_instance
  have : IsIso e'.inv.appTop := by change IsIso (e'.inv.app ⊤); infer_instance
  have hinj : Function.Injective e.hom.appTop.hom :=
    (ConcreteCategory.bijective_of_isIso e.hom.appTop).1
  have hker : RingHom.ker (e.hom ≫ Spec.map f ≫ e'.inv).appTop.hom =
      (RingHom.ker (Spec.map f).appTop.hom).comap e'.inv.appTop.hom := by
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      CommRingCat.hom_comp, RingHom.ker_comp_of_injective _ hinj, RingHom.comap_ker]
  refine ⟨n, eq_bot_iff.mpr ?_⟩
  rw [hker]
  have hbot : RingHom.ker e'.inv.appTop.hom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp
      (ConcreteCategory.bijective_of_isIso e'.inv.appTop).1
  refine (Ideal.le_comap_pow _ n).trans ?_
  rw [hn, Ideal.zero_eq_bot, ← RingHom.ker_eq_comap_bot, hbot]

end TestMaps

namespace Artin.ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The section of the completion of a sheaf given by a section with image in `T` determines that
section. -/
theorem presheafSection_injective {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) {T : Set (Space.points B S hS F)}
    {U : BigFppfOver B S hS} {x y : F.obj (op U)} (hx : Space.HasImageIn B S hS F T U x)
    (hy : Space.HasImageIn B S hS F T U y)
    (h : FormalSpace.presheafSection B S hS x hx = FormalSpace.presheafSection B S hS y hy) :
    x = y := by
  let e := Space.completionSheafIsoSubfunctor B S hS hF T
  have hx' : e.hom.app (op U) (FormalSpace.presheafSection B S hS x hx) = ⟨ULift.up x, hx⟩ :=
    congrArg (fun ψ => ψ.app (op U) ⟨ULift.up x, hx⟩) e.inv_hom_id
  have hy' : e.hom.app (op U) (FormalSpace.presheafSection B S hS y hy) = ⟨ULift.up y, hy⟩ :=
    congrArg (fun ψ => ψ.app (op U) ⟨ULift.up y, hy⟩) e.inv_hom_id
  have := congrArg (e.hom.app (op U)) h
  rw [hx', hy'] at this
  exact congrArg (fun s => s.1.down) this

/-- A section over an object of the site with a single point has point-set image in `T` as soon
as the image of that point lies in `T`. -/
theorem hasImageIn_of_subsingleton {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B S hS} [Subsingleton ((BigFppfOver.toScheme B S hS).obj U)]
    (T : Set (Space.points B S hS F)) (x : F.obj (op U)) (q : Space.points B S hS (yoneda.obj U))
    (hq : Space.pointsMap B S hS (yoneda.obj U) (yonedaEquiv.symm x) q ∈ T) :
    Space.HasImageIn B S hS F T U x := by
  rw [Space.hasImageIn_iff_range_subset]
  rintro _ ⟨q', rfl⟩
  have : q' = q := (Space.pointsEquivScheme B S hS U).injective (Subsingleton.elim _ _)
  rw [this]
  exact hq

variable (c : ContractionSituation B S hS)

/-- The morphism `x̂'` of a compatibility witness, read on the section of `V'_{/Z}` given by a
section `α` of `V'`: it is the section of `X'_{/T'}` given by `x'(α)`. -/
theorem CompatibilityWitness.xhat'_presheafSection {V : BigFppfOver B S hS}
    {Z : Set (Space.points B S hS (yoneda.obj V))}
    {u' : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ c.U'.toFunctor}
    {xhat : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ c.W}
    (w : CompatibilityWitness c V Z u' xhat) {U : BigFppfOver B S hS} (α : w.V'.obj (op U))
    (hα : Space.HasImageIn B S hS w.V' (Space.pointsMap B S hS w.V' w.p ⁻¹' Z) U α)
    (hα' : Space.HasImageIn B S hS c.X' c.T' U (w.x'.app (op U) α)) :
    w.xhat'.hom.app (op U) (FormalSpace.presheafSection B S hS α hα) =
      FormalSpace.presheafSection B S hS (w.x'.app (op U) α) hα' := by
  apply FormalSpace.injective_completionSheafInclusion_app B S hS
  rw [completionSheafInclusion_app_eq_of_comp_eq w.x' w.xhat' w.completion_x' α hα,
    FormalSpace.inclusion_presheafSection]

/-- **The witness `x'` lifts against small extensions at points of `V'` over `Z`.** Let
`V' ⟶ V`, `x̂'`, `x'` witness the compatibility of `ξ = (Z, u', x̂)`, and suppose `x̂` lifts along
nilpotent thickenings of sections landing in a set `O`. Then at every point `y ∈ |V'|` lying over
a point of `Z ∩ O`, every lifting problem for `x'` along a small extension has a solution. The
problem is pushed to `V` and to `W` along `p` and `g`, solved there by the lifting property of
`x̂`, and pulled back through the cartesian square `V'_{/Z} = V_{/Z} ×_W X'_{/T'}`. -/
theorem CompatibilityWitness.liftsAt_x' {V : BigFppfOver B S hS} {t : Triple c V}
    (w : CompatibilityWitness c V t.Z t.u t.xhat) (O : Set ((BigFppfOver.toScheme B S hS).obj V))
    (hlift : ∀ (T₀ T₁ : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T₁)]
      (i : T₀ ⟶ T₁),
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) →
      IsNilpotent (RingHom.ker ((BigFppfOver.toScheme B S hS).map i).appTop.hom) →
      ∀ (φ : T₀ ⟶ V) (hφ : Space.HasImageIn B S hS (yoneda.obj V) t.Z T₀ φ),
        Set.range ((BigFppfOver.toScheme B S hS).map φ) ⊆ O →
        ∀ wW : c.W.obj.obj (op T₁),
          c.W.obj.map i.op wW =
            t.xhat.hom.app (op T₀) (FormalSpace.presheafSection B S hS (T := t.Z) φ hφ) →
          ∃ (φ' : T₁ ⟶ V) (hφ' : Space.HasImageIn B S hS (yoneda.obj V) t.Z T₁ φ'),
            i ≫ φ' = φ ∧
              t.xhat.hom.app (op T₁) (FormalSpace.presheafSection B S hS (T := t.Z) φ' hφ') = wW)
    (y : Space.points B S hS w.V') (hy : Space.pointsMap B S hS w.V' w.p y ∈ t.Z)
    (hyO : Space.pointsToScheme B S hS V (Space.pointsMap B S hS w.V' w.p y) ∈ O) :
    Space.LiftsAt B S hS w.x' y (fun ⦃_ _⦄ φ => InfinitesimalLifting.IsSmallExtension φ) := by
  intro R' R φ hφ T T' i e e' hi _ p hp α β hpα hcomm
  obtain ⟨hR'l, -, hR'a, hRa, hsurj, -⟩ := hφ
  have := hR'l
  have := hR'a
  have := hRa
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T') := IsAffine.of_isIso e'.hom
  have : Subsingleton ((BigFppfOver.toScheme B S hS).obj T) :=
    ⟨fun a b => (Scheme.homeoOfIso e).injective
      (Deformation.Artin.subsingleton_spec_of_isArtinianRing R _ _)⟩
  have : Subsingleton ((BigFppfOver.toScheme B S hS).obj T') :=
    ⟨fun a b => (Scheme.homeoOfIso e').injective
      (Deformation.Artin.subsingleton_spec_of_isArtinianRing R' _ _)⟩
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) := by
    have := IsClosedImmersion.spec_of_surjective φ hsurj
    rw [hi]; infer_instance
  have hnil := isNilpotent_ker_appTop_of_iso_specMap φ e e' _ hi
  obtain ⟨α₀, rfl⟩ := yonedaEquiv.symm.surjective α
  obtain ⟨β₀, rfl⟩ := yonedaEquiv.symm.surjective β
  let pc := p.class B S hS (yoneda.obj T)
  -- the point of `T` and its images
  have hpy : Space.pointsMap B S hS _ (yonedaEquiv.symm α₀) pc = y := hpα
  let φT : T ⟶ V := w.p.app (op T) α₀
  have hφTy : yoneda.map φT = yonedaEquiv.symm α₀ ≫ w.p := by
    rw [yonedaEquiv_symm_naturality_right]
    ext; rfl
  have hφTpt : Space.pointsMap B S hS _ (yoneda.map φT) pc = Space.pointsMap B S hS w.V' w.p y := by
    rw [hφTy, Space.pointsMap_comp_apply, hpy]
  have hφT : Space.HasImageIn B S hS (yoneda.obj V) t.Z T φT := by
    refine hasImageIn_of_subsingleton t.Z φT pc ?_
    have : (yonedaEquiv.symm φT : yoneda.obj T ⟶ yoneda.obj V) = yoneda.map φT := by ext; rfl
    rw [this, hφTpt]; exact hy
  have hrange : Set.range ((BigFppfOver.toScheme B S hS).map φT) ⊆ O := by
    rintro _ ⟨t₁, rfl⟩
    have h1 : (BigFppfOver.toScheme B S hS).map φT t₁ =
        Space.pointsToScheme B S hS V (Space.pointsMap B S hS _ (yoneda.map φT) pc) := by
      rw [Space.pointsToScheme_pointsMap_yoneda]
      exact congrArg _ (Subsingleton.elim _ _)
    rw [h1, hφTpt]; exact hyO
  -- the image of the point of `T` in `X'` lies in `T'`
  have hx'y : Space.pointsMap B S hS w.V' w.x' y ∈ c.T' :=
    image_subset_of_completion_comp_eq c.isAlgebraicSpace_X' w.x' w.xhat' w.completion_x'
      ⟨y, hy, rfl⟩
  have hcomm₀ : c.X'.map i.op β₀ = w.x'.app (op T) α₀ := by
    have h := congrArg yonedaEquiv hcomm
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply, ← yonedaEquiv_naturality,
      Equiv.apply_symm_apply] at h
    exact h.symm
  have hβ : Space.HasImageIn B S hS c.X' c.T' T' β₀ := by
    refine hasImageIn_of_subsingleton c.T' β₀ (Space.pointsMap B S hS _ (yoneda.map i) pc) ?_
    rw [← Space.pointsMap_comp_apply, yonedaEquiv_symm_naturality_left, hcomm₀,
      ← yonedaEquiv_symm_naturality_right, Space.pointsMap_comp_apply, hpy]
    exact hx'y
  have hα₀ : Space.HasImageIn B S hS w.V' (Space.pointsMap B S hS w.V' w.p ⁻¹' t.Z) T α₀ := by
    refine hasImageIn_of_subsingleton _ α₀ pc ?_
    rw [hpy]; exact hy
  have hx'α : Space.HasImageIn B S hS c.X' c.T' T (w.x'.app (op T) α₀) := by
    refine hasImageIn_of_subsingleton c.T' _ pc ?_
    rw [← yonedaEquiv_symm_naturality_right, Space.pointsMap_comp_apply, hpy]
    exact hx'y
  -- the lifting problem for `x̂`
  let restr := Space.completionSheafRestrict B S hS w.p
    (Space.pointsMap B S hS w.V' w.p ⁻¹' t.Z) t.Z fun _ hz => hz
  have hrestr : ∀ (U : BigFppfOver B S hS) (a : w.V'.obj (op U)) (ha)
      (ha' : Space.HasImageIn B S hS (yoneda.obj V) t.Z U (w.p.app (op U) a)),
      restr.hom.app (op U) (FormalSpace.presheafSection B S hS a ha) =
        FormalSpace.presheafSection B S hS (w.p.app (op U) a) ha' :=
    fun U a ha ha' =>
      FormalSpace.completionSheafRestrict_presheafSection B S hS w.p _ t.Z _ a ha ha'
  have hsq : ∀ (U : BigFppfOver B S hS) (a), t.xhat.hom.app (op U) (restr.hom.app (op U) a) =
      c.g.hom.app (op U) (w.xhat'.hom.app (op U) a) := fun U a =>
    congrArg (fun m => m.hom.app (op U) a) w.isPullback_xhat'.w
  let wW := c.g.hom.app (op T') (FormalSpace.presheafSection B S hS β₀ hβ)
  have hmap : (Space.completionSheaf B S hS c.X' c.T').obj.map i.op
      (FormalSpace.presheafSection B S hS β₀ hβ) =
      FormalSpace.presheafSection B S hS (w.x'.app (op T) α₀) hx'α := by
    rw [FormalSpace.presheafSection_map B S hS i β₀ hβ (hcomm₀ ▸ hx'α)]
    exact FormalSpace.presheafSection_congr B S hS hcomm₀ _ _
  have hw : c.W.obj.map i.op wW =
      t.xhat.hom.app (op T) (FormalSpace.presheafSection B S hS (T := t.Z) φT hφT) := by
    rw [← NatTrans.naturality_apply c.g.hom i.op, hmap,
      ← w.xhat'_presheafSection c α₀ hα₀ hx'α, ← hsq, hrestr T α₀ hα₀ hφT]
  obtain ⟨φ', hφ', hcomp, hval⟩ := hlift T T' i hci hnil φT hφT hrange wW hw
  -- the cartesian square of completions, read on sections
  have hpb : ∀ U : BigFppfOver B S hS, IsPullback (restr.hom.app (op U))
      (w.xhat'.hom.app (op U)) (t.xhat.hom.app (op U)) (c.g.hom.app (op U)) := fun U =>
    (w.isPullback_xhat'.map (sheafToPresheaf (BigFppfOver.topology B S hS)
      (Type (u + 1)))).map ((evaluation _ (Type (u + 1))).obj (op U))
  obtain ⟨s', hs₁, hs₂⟩ := Types.exists_of_isPullback (hpb T')
    (FormalSpace.presheafSection B S hS (T := t.Z) φ' hφ')
    (FormalSpace.presheafSection B S hS β₀ hβ) hval
  let E := Space.completionSheafIsoSubfunctor B S hS w.isAlgebraicSpace_V'.isSheaf
    (Space.pointsMap B S hS w.V' w.p ⁻¹' t.Z)
  let γ₀ := (E.hom.app (op T') s').1.down
  have hγ₀ : Space.HasImageIn B S hS w.V' (Space.pointsMap B S hS w.V' w.p ⁻¹' t.Z) T' γ₀ :=
    (E.hom.app (op T') s').2
  have hsγ : FormalSpace.presheafSection B S hS γ₀ hγ₀ = s' :=
    congrArg (fun ψ => ψ.app (op T') s') E.hom_inv_id
  have hx'γ : Space.HasImageIn B S hS c.X' c.T' T' (w.x'.app (op T') γ₀) := by
    rw [Space.hasImageIn_iff_range_subset]
    rintro _ ⟨q, rfl⟩
    rw [← yonedaEquiv_symm_naturality_right, Space.pointsMap_comp_apply]
    exact image_subset_of_completion_comp_eq c.isAlgebraicSpace_X' w.x' w.xhat' w.completion_x'
      ⟨_, (Space.hasImageIn_iff_range_subset B S hS _ _ _).1 hγ₀ ⟨q, rfl⟩, rfl⟩
  have hγβ : w.x'.app (op T') γ₀ = β₀ :=
    presheafSection_injective c.isAlgebraicSpace_X'.isSheaf hx'γ hβ
      (by rw [← w.xhat'_presheafSection c γ₀ hγ₀ hx'γ, hsγ, hs₂])
  have hpγ : w.p.app (op T') γ₀ = φ' := by
    have hpγ' : Space.HasImageIn B S hS (yoneda.obj V) t.Z T' (w.p.app (op T') γ₀) :=
      (FormalSpace.hasImageIn_preimage_pointsMap_iff B S hS w.p t.Z T' γ₀).1 hγ₀
    exact presheafSection_injective (isAlgebraicSpace_yoneda B S hS V).isSheaf hpγ' hφ'
      (by rw [← hrestr T' γ₀ hγ₀ hpγ', hsγ, hs₁])
  refine ⟨yonedaEquiv.symm γ₀, ?_, ?_⟩
  · rw [yonedaEquiv_symm_naturality_left]
    congr 1
    have hγi : Space.HasImageIn B S hS w.V' (Space.pointsMap B S hS w.V' w.p ⁻¹' t.Z) T
        (w.V'.map i.op γ₀) :=
      (Space.completionSubfunctor B S hS w.V' (Space.pointsMap B S hS w.V' w.p ⁻¹' t.Z)).map
        i.op (a := ULift.up γ₀) hγ₀
    have hpi : w.p.app (op T) (w.V'.map i.op γ₀) = φT := by
      rw [NatTrans.naturality_apply, hpγ]
      exact hcomp
    have hx'i : w.x'.app (op T) (w.V'.map i.op γ₀) = w.x'.app (op T) α₀ := by
      rw [NatTrans.naturality_apply, hγβ, hcomm₀]
    apply presheafSection_injective w.isAlgebraicSpace_V'.isSheaf hγi hα₀
    apply Types.ext_of_isPullback (hpb T)
    · rw [hrestr T _ hγi (hpi ▸ hφT), hrestr T α₀ hα₀ hφT]
      exact FormalSpace.presheafSection_congr B S hS hpi _ _
    · rw [w.xhat'_presheafSection c _ hγi (hx'i ▸ hx'α), w.xhat'_presheafSection c α₀ hα₀ hx'α]
      exact FormalSpace.presheafSection_congr B S hS hx'i _ _
  · rw [yonedaEquiv_symm_naturality_right, hγβ]

/-- The structure morphism of `X'` to the represented terminal object of the site is locally of
finite type. -/
theorem isLocallyOfFiniteType_toTerminalYoneda (h : c.X' ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS)))) :
    Space.IsLocallyOfFiniteType B S hS h := by
  let e : yoneda.obj (Over.mk (𝟙 (B.obj hS))) ≅ ⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    ((Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _).uniqueUpToIso terminalIsTerminal
  have hT : IsAlgebraicSpace B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
    isAlgebraicSpace_of_iso B S hS e.symm (isAlgebraicSpace_yoneda B S hS _)
  refine Space.isLocallyOfFiniteType_of_comp B S hS c.isAlgebraicSpace_X'
    (isAlgebraicSpace_yoneda B S hS _) hT h e.hom ?_
  rw [show h ≫ e.hom = terminal.from c.X' from terminal.hom_ext _ _]
  exact c.isLocallyOfFiniteType_X'

/-- `X'` is locally Noetherian, in the atlas form: it is locally of finite type over the locally
Noetherian `S`. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_X' :
    Space.HasEtaleLocalProperty B S hS c.X'
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian T) := by
  have := c.isLocallyNoetherian_base
  let h : c.X' ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))) :=
    ((Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _).from _
  exact FormalSpace.hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType
    c.isAlgebraicSpace_X' (isAlgebraicSpace_yoneda B S hS _) h
    (c.isLocallyOfFiniteType_toTerminalYoneda h)
    (Space.hasEtaleLocalProperty_isLocallyNoetherian_yoneda
      (inferInstanceAs (_root_.AlgebraicGeometry.IsLocallyNoetherian S)))

/-- The witness `x'` is locally of finite type, as soon as `V` is locally of finite type over
`S`: `V' ⟶ V` is proper. -/
theorem CompatibilityWitness.isLocallyOfFiniteType_x' {V : BigFppfOver B S hS}
    {Z : Set (Space.points B S hS (yoneda.obj V))}
    {u' : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ c.U'.toFunctor}
    {xhat : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ c.W}
    (w : CompatibilityWitness c V Z u' xhat)
    (hV : LocallyOfFiniteType ((Over.post B.inclusion).obj V).hom) :
    Space.IsLocallyOfFiniteType B S hS w.x' := by
  let k : V ⟶ Over.mk (𝟙 (B.obj hS)) := Over.homMk V.hom
  let h : c.X' ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))) :=
    ((Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _).from _
  have hcomp : Space.IsLocallyOfFiniteType B S hS (w.x' ≫ h) := by
    rw [show w.x' ≫ h = w.p ≫ yoneda.map k from
      ((Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _).hom_ext _ _]
    exact Space.isLocallyOfFiniteType_comp' B S hS _ _ (isAlgebraicSpace_yoneda B S hS V)
      (isAlgebraicSpace_yoneda B S hS _) w.isProper_p.2.1.1
      ((Space.isLocallyOfFiniteType_yoneda_map_iff B S hS k).2 hV)
  exact Space.isLocallyOfFiniteType_of_comp B S hS w.isAlgebraicSpace_V' c.isAlgebraicSpace_X'
    (isAlgebraicSpace_yoneda B S hS _) w.x' h hcomp

/-- **The witness `x'` is smooth at the points of `V'` over `Z`** (the second case of the proof of
Stacks 0GIA, by Stacks 0APN, (3) ⟹ (1)), when `V` is locally of finite type over `S` and `x̂`
lifts along nilpotent thickenings of sections landing in a set `O`: at a point `y` over a point of
`Z ∩ O`, `x'` lifts against small extensions
(`AlgebraicGeometry.Artin.ContractionSituation.CompatibilityWitness.liftsAt_x'`), it is locally of
finite type and `X'` is locally Noetherian. -/
theorem CompatibilityWitness.isSmoothAt_x' {V : BigFppfOver B S hS} {t : Triple c V}
    (w : CompatibilityWitness c V t.Z t.u t.xhat)
    (hV : LocallyOfFiniteType ((Over.post B.inclusion).obj V).hom)
    (O : Set ((BigFppfOver.toScheme B S hS).obj V))
    (hlift : ∀ (T₀ T₁ : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T₁)]
      (i : T₀ ⟶ T₁),
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) →
      IsNilpotent (RingHom.ker ((BigFppfOver.toScheme B S hS).map i).appTop.hom) →
      ∀ (φ : T₀ ⟶ V) (hφ : Space.HasImageIn B S hS (yoneda.obj V) t.Z T₀ φ),
        Set.range ((BigFppfOver.toScheme B S hS).map φ) ⊆ O →
        ∀ wW : c.W.obj.obj (op T₁),
          c.W.obj.map i.op wW =
            t.xhat.hom.app (op T₀) (FormalSpace.presheafSection B S hS (T := t.Z) φ hφ) →
          ∃ (φ' : T₁ ⟶ V) (hφ' : Space.HasImageIn B S hS (yoneda.obj V) t.Z T₁ φ'),
            i ≫ φ' = φ ∧
              t.xhat.hom.app (op T₁) (FormalSpace.presheafSection B S hS (T := t.Z) φ' hφ') = wW)
    (y : Space.points B S hS w.V') (hy : Space.pointsMap B S hS w.V' w.p y ∈ t.Z)
    (hyO : Space.pointsToScheme B S hS V (Space.pointsMap B S hS w.V' w.p y) ∈ O) :
    Space.IsSmoothAt B S hS w.x' y :=
  Space.isSmoothAt_of_liftsAt_isSmallExtension B S hS w.isAlgebraicSpace_V' c.isAlgebraicSpace_X'
    w.x' y c.hasEtaleLocalProperty_isLocallyNoetherian_X' (w.isLocallyOfFiniteType_x' c hV)
    (w.liftsAt_x' c O hlift y hy hyO)

end Artin.ContractionSituation

end AlgebraicGeometry

end
