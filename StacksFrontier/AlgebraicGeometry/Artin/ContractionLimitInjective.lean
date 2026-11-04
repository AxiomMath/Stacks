module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitEqualizerTorsion
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitWitnessHom
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitOpenPart
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionWitnessOfProper
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionWitnessComparison
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEqualizerSmallerBase
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MonomorphismClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTargetRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlgebraicSpaceAtlas

/-!
# Injectivity in the limit preservation of Artin's contraction functor

Ingredients of the injectivity half of the proof of Stacks 0GI5 for an arbitrary `X'`, separated
or not.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.completionSheaf_hom_ext_of_isAffine`: morphisms
  out of `V_{/Z}` are determined on affine sections.
* `AlgebraicGeometry.Artin.ContractionSituation.isClosedImmersion_equalizer_of_reduction_eq`:
  formal morphisms into `W` whose reductions agree have closed equalizer (Stacks 0GHZ).
* `AlgebraicGeometry.Artin.ContractionSituation.exists_stage_completionSheafMap_comp_eq`: two
  formal morphisms out of a stage agreeing in the limit, with closed equalizer and a proper witness
  on whose completion they agree, agree at a later stage.
* `AlgebraicGeometry.Artin.ContractionSituation.exists_stage_witness_hom`: the comparison of the
  witnesses of two elements agreeing in the limit descends to a stage.
* `AlgebraicGeometry.Artin.ContractionSituation.exists_mapTriple_eq_of_xhat_heq`: once the formal
  components agree, the triples agree at a stage.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
* [Stacks Project, Tag 0GHZ](https://stacks.math.columbia.edu/tag/0GHZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.pointTopology

/-- **Morphisms out of the completion of a representable along a set of points are determined
on affine sections.** -/
theorem completionSheaf_hom_ext_of_isAffine {V : BigFppfOver B S hS}
    {Z : Set (Space.points B S hS (yoneda.obj V))}
    {G : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    {φ ψ : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ G}
    (H : ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      ∀ (t : T ⟶ V) (ht : Space.HasImageIn B S hS (yoneda.obj V) Z T t),
        φ.hom.app (op T) (FormalSpace.presheafSection B S hS t ht) =
          ψ.hom.app (op T) (FormalSpace.presheafSection B S hS t ht)) :
    φ = ψ := by
  apply Sheaf.hom_ext
  apply (BigFppfOver.topology B S hS).sheafify_hom_ext _ _ G.property
  ext U ⟨⟨x⟩, hx⟩
  show φ.hom.app U (FormalSpace.presheafSection B S hS x hx) =
    ψ.hom.app U (FormalSpace.presheafSection B S hS x hx)
  have : (BigAffineFppf.inclusion B S hS).IsCoverDense (BigFppfOver.topology B S hS) :=
    Functor.IsDenseSubsite.isCoverDense (BigAffineFppf.topology B S hS)
      (BigFppfOver.topology B S hS) (BigAffineFppf.inclusion B S hS)
  refine Functor.IsCoverDense.ext (BigAffineFppf.inclusion B S hS) G U.unop fun T f => ?_
  have hx' : Space.HasImageIn B S hS (yoneda.obj V) Z _ ((yoneda.obj V).map f.op x) :=
    ((Space.completionSubfunctor B S hS (yoneda.obj V) Z).map f.op hx :)
  have key : ∀ θ : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ G,
      G.obj.map f.op (θ.hom.app U (FormalSpace.presheafSection B S hS x hx)) =
        θ.hom.app (op ((BigAffineFppf.inclusion B S hS).obj T))
          (FormalSpace.presheafSection B S hS ((yoneda.obj V).map f.op x) hx') := by
    intro θ
    rw [← FormalSpace.presheafSection_map (F := yoneda.obj V) (TF := Z) B S hS f x hx hx']
    exact (NatTrans.naturality_apply θ.hom f.op _).symm
  rw [key φ, key ψ]
  exact H _ T.property _ hx'

/-- **The equalizer of two morphisms into `W` is relatively locally of finite type**, as a base
change of the diagonal of the formal algebraic space `W` (Stacks 0AIP). -/
theorem isRepresentableByAlgebraicSpacesULift_equalizer_ι (c : ContractionSituation B S hS)
    {F : FormalSpace.FppfSheaf B S hS} (x₁ x₂ : F ⟶ c.W) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (equalizer.ι x₁ x₂).hom := by
  let J := BigFppfOver.topology B S hS
  let L := MorphismProperty.inverseImage (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have hd := FormalSpace.relative_locallyOfFiniteType_diag_of_isFormalAlgebraicSpace B S hS
    c.isLocallyNoetherian_W.1
  have h1 : L.relative (Sheaf.sheafifiedYoneda J) (equalizer.ι x₁ x₂) :=
    (MorphismProperty.relative_isStableUnderBaseChange L).of_isPullback
      (isPullback_equalizer_prod x₁ x₂).flip hd
  have h2 : L.relative uliftYoneda.{u + 1} (equalizer.ι x₁ x₂).hom :=
    FormalSpace.relative_of_natIso (FormalSpace.sheafifiedYonedaPresheafIso B S hS) L _
      ((Space.relative_comp_map_iff (Sheaf.sheafifiedYoneda J) (sheafToPresheaf J (Type (u + 1)))
        L _).mpr h1)
  exact FormalSpace.isRepresentableByAlgebraicSpacesULift_of_relativelyRepresentable B S hS h2.rep

/-- An element of a Noetherian ring killed by a power of `I` and lying in every power of `I` is
zero (Krull's intersection theorem). -/
theorem _root_.Ideal.eq_zero_of_pow_mul_eq_zero_of_forall_mem_pow {A : Type*} [CommRing A]
    [IsNoetherianRing A] {I : Ideal A} {a : A} {N : ℕ} (hN : ∀ b ∈ I ^ N, b * a = 0)
    (ha : ∀ n, a ∈ I ^ n) : a = 0 := by
  have hmem : a ∈ (⨅ i : ℕ, I ^ i • ⊤ : Submodule A A) :=
    Submodule.mem_iInf _ |>.mpr fun i => by rw [smul_eq_mul, Ideal.mul_top]; exact ha i
  obtain ⟨⟨r, hr⟩, hra⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff I a).mp hmem
  have hra' : r * a = a := hra
  have hk : ∀ k : ℕ, r ^ k * a = a := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_assoc, hra', ih]
  rw [← hk N]
  exact hN _ (Ideal.pow_mem_pow hr N)

/-- The formal component of a transported triple, read on a section. -/
theorem mapTriple_xhat_app_presheafSection (c : ContractionSituation B S hS)
    {V' V : BigFppfOver B S hS} (f : V' ⟶ V) (s : Triple c V) {U : BigFppfOver B S hS}
    (t : U ⟶ V') (ht : Space.HasImageIn B S hS (yoneda.obj V') (mapTriple c f s).Z U t) :
    (mapTriple c f s).xhat.hom.app (op U) (FormalSpace.presheafSection B S hS t ht) =
      s.xhat.hom.app (op U) (FormalSpace.presheafSection B S hS (t ≫ f)
        ((FormalSpace.hasImageIn_preimage_pointsMap_iff B S hS (yoneda.map f) s.Z U t).mp ht)) := by
  show s.xhat.hom.app (op U) ((Space.completionSheafMap B S hS (yoneda.map f) s.Z).hom.app (op U)
    (FormalSpace.presheafSection B S hS t ht)) = _
  rw [FormalSpace.completionSheafMap_presheafSection B S hS (yoneda.map f) s.Z t ht]
  rfl

/-- Restriction to the limit of a restriction to a stage is restriction to the limit. -/
theorem mapTriple_π_mapTriple (c : ContractionSituation B S hS) {I : Type u} [Category.{u} I]
    {D : I ⥤ LocallyNoetherianOver B S hS} (κ : Cone D) {i j : I} (f : j ⟶ i)
    (t : Triple c (D.obj i).obj) :
    mapTriple c (κ.π.app j).hom (mapTriple c (D.map f).hom t) = mapTriple c (κ.π.app i).hom t := by
  rw [← mapTriple_comp]
  congr 1
  exact congrArg (fun k => k.hom) (κ.w f)

/-- Restriction along a composite of stage maps. -/
theorem mapTriple_map_comp (c : ContractionSituation B S hS) {I : Type u} [Category.{u} I]
    (D : I ⥤ LocallyNoetherianOver B S hS) {i j k : I} (g : k ⟶ j) (f : j ⟶ i)
    (t : Triple c (D.obj i).obj) :
    mapTriple c (D.map (g ≫ f)).hom t =
      mapTriple c (D.map g).hom (mapTriple c (D.map f).hom t) := by
  rw [← mapTriple_comp, D.map_comp]
  rfl

section Generic

variable {V V' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
  {Iz : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
  {Z : Set (Space.points B S hS (yoneda.obj V))}
  (hIz : ∀ x, x ∈ Z ↔ Space.pointsToScheme B S hS V x ∈
    ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
      (Iz : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
  {W : FormalSpace.FppfSheaf B S hS}
  (x₁ x₂ : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ W)
  {sF : Finset Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
  (hsF : ∀ (n : ℕ) (T : BigFppfOver B S hS) (t : T ⟶ V)
    (ht : Space.HasImageIn B S hS (yoneda.obj V) Z T t),
      Iz ^ n ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map t).appTop.hom →
      (x₁.hom.app (op T) (FormalSpace.presheafSection B S hS t ht) =
          x₂.hom.app (op T) (FormalSpace.presheafSection B S hS t ht) ↔
        ∀ a ∈ sF, ((BigFppfOver.toScheme B S hS).map t).appTop a = 0))

omit [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] in
include hIz hsF in
/-- **The torsion functions cutting out the equalizer vanish wherever the two formal morphisms
agree**, over an affine Noetherian `V'`: on each thickening of `V'` they vanish by the criterion,
so they lie in every power of the ideal, and being torsion they vanish (Krull). -/
theorem appTop_eq_zero_of_completionSheafMap_comp_eq
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)] (g : V' ⟶ V)
    (hlim : Space.completionSheafMap B S hS (yoneda.map g) Z ≫ x₁ =
      Space.completionSheafMap B S hS (yoneda.map g) Z ≫ x₂)
    {a : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)} (ha : a ∈ sF) {N : ℕ}
    (hN : ∀ b ∈ Iz ^ N, b * a = 0) :
    ((BigFppfOver.toScheme B S hS).map g).appTop a = 0 := by
  let K := Iz.map ((BigFppfOver.toScheme B S hS).map g).appTop.hom
  refine Ideal.eq_zero_of_pow_mul_eq_zero_of_forall_mem_pow (I := K) (N := N) ?_ ?_
  · intro b hb
    rw [← Ideal.map_pow] at hb
    refine Submodule.span_induction
      (p := fun b _ => b * ((BigFppfOver.toScheme B S hS).map g).appTop a = 0) ?_ ?_ ?_ ?_ hb
    · rintro _ ⟨y, hy, rfl⟩
      rw [← map_mul, hN y hy, map_zero]
    · exact zero_mul _
    · intro x y _ _ hx hy
      rw [add_mul, hx, hy, add_zero]
    · intro r x _ hx
      rw [smul_eq_mul, mul_assoc, hx, mul_zero]
  · intro n
    let q := Space.adicCompletionQuotientObjHom B S hS V' K n
    have hIn : Iz ^ n ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map (q ≫ g)).appTop.hom := by
      intro b hb
      rw [RingHom.mem_ker, Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        ← RingHom.mem_ker, Space.ker_appTop_adicCompletionQuotientObjHom, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hb
    have ht := Space.hasImageIn_of_pow_le_ker hIz (q ≫ g) hIn
    have hq := (FormalSpace.hasImageIn_preimage_pointsMap_iff B S hS (yoneda.map g) Z _ q).mpr ht
    have hag : x₁.hom.app (op _) (FormalSpace.presheafSection B S hS (q ≫ g) ht) =
        x₂.hom.app (op _) (FormalSpace.presheafSection B S hS (q ≫ g) ht) := by
      have e := congrArg (fun θ => θ.hom.app (op _) (FormalSpace.presheafSection B S hS q hq)) hlim
      change x₁.hom.app _ ((Space.completionSheafMap B S hS (yoneda.map g) Z).hom.app _ _) =
        x₂.hom.app _ ((Space.completionSheafMap B S hS (yoneda.map g) Z).hom.app _ _) at e
      rwa [FormalSpace.completionSheafMap_presheafSection (F := yoneda.obj V') (G := yoneda.obj V)
        B S hS (yoneda.map g) Z q hq ht] at e
    have hz := (hsF n _ (q ≫ g) ht hIn).mp hag a ha
    rwa [Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← RingHom.mem_ker,
      Space.ker_appTop_adicCompletionQuotientObjHom] at hz

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
include hIz hsF in
/-- **Wherever the torsion functions vanish, the two formal morphisms agree.** -/
theorem completionSheafMap_comp_eq_of_appTop_eq_zero (g : V' ⟶ V)
    (hg : ∀ a ∈ sF, ((BigFppfOver.toScheme B S hS).map g).appTop a = 0) :
    Space.completionSheafMap B S hS (yoneda.map g) Z ≫ x₁ =
      Space.completionSheafMap B S hS (yoneda.map g) Z ≫ x₂ := by
  refine completionSheaf_hom_ext_of_isAffine fun T hT t ht => ?_
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hT
  have ht' := (FormalSpace.hasImageIn_preimage_pointsMap_iff B S hS (yoneda.map g) Z T t).mp ht
  show x₁.hom.app _ ((Space.completionSheafMap B S hS _ Z).hom.app _ _) =
    x₂.hom.app _ ((Space.completionSheafMap B S hS _ Z).hom.app _ _)
  rw [FormalSpace.completionSheafMap_presheafSection (F := yoneda.obj V') (G := yoneda.obj V)
    B S hS _ Z t ht ht']
  obtain ⟨n, hn⟩ := Scheme.exists_pow_le_ker_appTop ((BigFppfOver.toScheme B S hS).map (t ≫ g))
    Iz (Ideal.fg_of_isNoetherianRing Iz) (Space.toScheme_map_mem_zeroLocus_of_hasImageIn hIz ht')
  refine (hsF n T (t ≫ g) ht' hn).mpr fun a ha => ?_
  rw [Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hg a ha, map_zero]

end Generic

/-- **The equalizer of two formal morphisms out of the completion of a locally Noetherian object
whose reductions agree is a closed immersion** (Stacks 0GHZ). -/
theorem isClosedImmersion_equalizer_of_reduction_eq (c : ContractionSituation B S hS)
    {V : BigFppfOver B S hS} (hV : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V))
    {Z : Set (Space.points B S hS (yoneda.obj V))} (hZ : IsClosed Z)
    (y₁ y₂ : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ c.W)
    (hred : FormalSpace.reducedClosedSubsetToCompletionSheaf B S hS
        (isAlgebraicSpace_yoneda B S hS V) Z hZ ≫ y₁ =
      FormalSpace.reducedClosedSubsetToCompletionSheaf B S hS
        (isAlgebraicSpace_yoneda B S hS V) Z hZ ≫ y₂) :
    FormalSpace.IsClosedImmersion B S hS (equalizer.ι y₁ y₂) :=
  FormalSpace.isClosedImmersion_of_mono_of_reduction_factors B S hS
    (isRepresentableByAlgebraicSpacesULift_equalizer_ι c _ _) inferInstance
    (FormalSpace.isReduction_completionSheaf B S hS (isAlgebraicSpace_yoneda B S hS V) Z hZ)
    (equalizer.lift _ hred) (equalizer.lift_ι _ _)
    (Or.inr (FormalSpace.isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian
      (isAlgebraicSpace_yoneda B S hS V) (Space.isLocallyNoetherian_yoneda B S hS _ hV) _ hZ))

/-- A map from a pullback of the first witness to the second witness's source, compatible with the
structure maps, induces a comparison of the pulled back witnesses. -/
private theorem exists_hom_pullback_of_lift (c : ContractionSituation B S hS)
    {V V' : BigFppfOver B S hS} (φ : V' ⟶ V) {s₁ s₂ : Triple c V}
    (W₁ : CompatibilityWitness c V s₁.Z s₁.u s₁.xhat)
    (W₂ : CompatibilityWitness c V s₂.Z s₂.u s₂.xhat) (b : pullback (yoneda.map φ) W₁.p ⟶ W₂.V')
    (hbp : b ≫ W₂.p = pullback.fst (yoneda.map φ) W₁.p ≫ yoneda.map φ)
    (hbx : b ≫ W₂.x' = pullback.snd (yoneda.map φ) W₁.p ≫ W₁.x') :
    ∃ ψ' : (W₁.pullback φ s₁).V' ⟶ (W₂.pullback φ s₂).V',
      ψ' ≫ (W₂.pullback φ s₂).p = (W₁.pullback φ s₁).p ∧
        ψ' ≫ (W₂.pullback φ s₂).x' = (W₁.pullback φ s₁).x' := by
  let ψ' : pullback (yoneda.map φ) W₁.p ⟶ pullback (yoneda.map φ) W₂.p :=
    pullback.lift (pullback.fst _ _) b hbp.symm
  have e : ψ' ≫ pullback.snd (yoneda.map φ) W₂.p = b := pullback.lift_snd _ _ _
  exact ⟨ψ', pullback.lift_fst _ _ _, (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ W₂.x') e).trans hbx)⟩

/-- **A comparison of two witnesses restricts along a morphism of the base.** -/
theorem exists_hom_pullback_of_hom (c : ContractionSituation B S hS) {V V' : BigFppfOver B S hS}
    (φ : V' ⟶ V) {s₁ s₂ : Triple c V} (W₁ : CompatibilityWitness c V s₁.Z s₁.u s₁.xhat)
    (W₂ : CompatibilityWitness c V s₂.Z s₂.u s₂.xhat) (ψ : W₁.V' ⟶ W₂.V')
    (hψp : ψ ≫ W₂.p = W₁.p) (hψx : ψ ≫ W₂.x' = W₁.x') :
    ∃ ψ' : (W₁.pullback φ s₁).V' ⟶ (W₂.pullback φ s₂).V',
      ψ' ≫ (W₂.pullback φ s₂).p = (W₁.pullback φ s₁).p ∧
        ψ' ≫ (W₂.pullback φ s₂).x' = (W₁.pullback φ s₁).x' :=
  exists_hom_pullback_of_lift c φ W₁ W₂ (pullback.snd _ _ ≫ ψ)
    (by rw [Category.assoc, hψp]; exact pullback.condition.symm) (by rw [Category.assoc, hψx])

section Injective

variable (c : ContractionSituation B S hS)
  {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ LocallyNoetherianOver B S hS}
  {κ : Cone D} (hκ : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ))
  (hD : ∀ i, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj i)))
  (hpt : IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj κ.pt))

include hκ hD hpt in
/-- **Two formal morphisms out of a stage agreeing in the limit agree at a later stage**, as soon
as their equalizer is a closed immersion through which some proper `Y ⟶ V_i` lifting `V_i ∖ Z`
factors on completions: the finitely many torsion functions cutting out the equalizer
(`AlgebraicGeometry.Space.exists_finset_torsion_iff_of_isProper`) vanish in the limit, hence at a
stage. -/
theorem exists_stage_completionSheafMap_comp_eq (i : I)
    {Z : Set (Space.points B S hS (yoneda.obj (D.obj i).obj))} (hZ : IsClosed Z)
    (x₁ x₂ : Space.completionSheaf B S hS (yoneda.obj (D.obj i).obj) Z ⟶ c.W)
    (hlim : Space.completionSheafMap B S hS (yoneda.map (κ.π.app i).hom) Z ≫ x₁ =
      Space.completionSheafMap B S hS (yoneda.map (κ.π.app i).hom) Z ≫ x₂)
    (hE : FormalSpace.IsClosedImmersion B S hS (equalizer.ι x₁ x₂))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (p : Y ⟶ yoneda.obj (D.obj i).obj) (hp : Space.IsProper B S hS p)
    (j : (Space.openSubspaceOfPoints B S hS (yoneda.obj (D.obj i).obj) Zᶜ).toFunctor ⟶ Y)
    (hj : j ≫ p = (Space.openSubspaceOfPoints B S hS (yoneda.obj (D.obj i).obj) Zᶜ).ι)
    (hYx : Space.completionSheafMap B S hS p Z ≫ x₁ = Space.completionSheafMap B S hS p Z ≫ x₂) :
    ∃ (k : I) (f : k ⟶ i), Space.completionSheafMap B S hS (yoneda.map (D.map f).hom) Z ≫ x₁ =
      Space.completionSheafMap B S hS (yoneda.map (D.map f).hom) Z ≫ x₂ := by
  classical
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i).obj) := hD i
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj (D.obj i).obj) :=
    (D.obj i).property
  have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj (D.obj i).obj, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj κ.pt.obj) := hpt
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj κ.pt.obj) := κ.pt.property
  have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  obtain ⟨Iz, hIz⟩ := Space.exists_ideal_mem_iff_mem_zeroLocus B S hS (D.obj i).obj hZ
  obtain ⟨sF, hsF_tors, hsF⟩ := Space.exists_finset_torsion_iff_of_isProper hIz x₁ x₂ hE hY p hp
    j hj hYx
  let κi : κ.pt.obj ⟶ (D.obj i).obj := (κ.π.app i).hom
  have hvan : ∀ a ∈ sF, ((BigFppfOver.toScheme B S hS).map κi).appTop a = 0 := fun a ha =>
    appTop_eq_zero_of_completionSheafMap_comp_eq hIz x₁ x₂ hsF κi hlim ha
      (hsF_tors a ha).choose_spec
  have : ∀ k, IsAffine ((D ⋙ LocallyNoetherianOver.toScheme B S hS).obj k) := hD
  have hstage : ∀ a : sF, ∃ (k : I) (g : k ⟶ i),
      ((BigFppfOver.toScheme B S hS).map (D.map g).hom).appTop a.1 = 0 := fun a =>
    exists_appTop_map_eq_zero_of_isAffine_of_isLimit (D ⋙ LocallyNoetherianOver.toScheme B S hS)
      _ hκ i a.1 (hvan a.1 a.2)
  choose kk gg hgg using hstage
  obtain ⟨ν, hν⟩ := IsCofiltered.inf_objs_exists
    (Finset.univ.image (fun a : sF => (Over.mk (gg a) : Over i)))
  refine ⟨ν.left, ν.hom, completionSheafMap_comp_eq_of_appTop_eq_zero hIz x₁ x₂ hsF _
    fun a ha => ?_⟩
  obtain ⟨m⟩ := hν (Finset.mem_image_of_mem _ (Finset.mem_univ (⟨a, ha⟩ : sF)))
  have e : ν.hom = m.left ≫ gg ⟨a, ha⟩ := (Over.w m).symm
  rw [e, D.map_comp]
  show ((BigFppfOver.toScheme B S hS).map ((D.map m.left).hom ≫ (D.map (gg ⟨a, ha⟩)).hom)).appTop
    a = 0
  rw [Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hgg, map_zero]

include hκ hD hpt in
/-- **The comparison of the two transported witnesses descends to a stage.** If two elements of
`F(V_i)` agree in `F(V)`, their witnesses transported to `V` are related by a morphism over `V`
(`CompatibilityWitness.exists_hom_of_eq`); it descends to the witnesses transported to some
stage (`AlgebraicGeometry.Space.exists_stage_hom_of_isLimit`). -/
theorem exists_stage_witness_hom (i : I) (t₁ t₂ : Triple c (D.obj i).obj)
    (h : mapTriple c (κ.π.app i).hom t₁ = mapTriple c (κ.π.app i).hom t₂) :
    ∃ (k : I) (f : k ⟶ i)
      (W₁ : CompatibilityWitness c (D.obj k).obj (mapTriple c (D.map f).hom t₁).Z
        (mapTriple c (D.map f).hom t₁).u (mapTriple c (D.map f).hom t₁).xhat)
      (W₂ : CompatibilityWitness c (D.obj k).obj (mapTriple c (D.map f).hom t₂).Z
        (mapTriple c (D.map f).hom t₂).u (mapTriple c (D.map f).hom t₂).xhat)
      (ψ : W₁.V' ⟶ W₂.V'), ψ ≫ W₂.p = W₁.p ∧ ψ ≫ W₂.x' = W₁.x' := by
  let ω₁ := Classical.choice t₁.compatible
  let ω₂ := Classical.choice t₂.compatible
  have : IsLocallyNoetherian S := c.isLocallyNoetherian_base
  have hX'lp := Space.limitPreserving_of_isLocallyOfFiniteType B S hS c.isAlgebraicSpace_X'
    c.isLocallyOfFiniteType_X'
  let φ := (κ.π.app i).hom
  obtain ⟨ψ, hψp, hψx⟩ := CompatibilityWitness.exists_hom_of_eq κ.pt.property h
    (ω₁.pullback φ t₁) (ω₂.pullback φ t₂)
  let ψ' : pullback (yoneda.map φ) ω₁.p ⟶ pullback (yoneda.map φ) ω₂.p := ψ
  have hψp' : ψ' ≫ pullback.fst (yoneda.map φ) ω₂.p = pullback.fst (yoneda.map φ) ω₁.p := hψp
  have hψx' : ψ' ≫ pullback.snd (yoneda.map φ) ω₂.p ≫ ω₂.x' =
      pullback.snd (yoneda.map φ) ω₁.p ≫ ω₁.x' := hψx
  have hap : (ψ' ≫ pullback.snd (yoneda.map φ) ω₂.p) ≫ ω₂.p =
      pullback.fst (yoneda.map φ) ω₁.p ≫ yoneda.map φ := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hψp']
  have hax : (ψ' ≫ pullback.snd (yoneda.map φ) ω₂.p) ≫ ω₂.x' =
      pullback.snd (yoneda.map φ) ω₁.p ≫ ω₁.x' := by
    rw [Category.assoc, hψx']
  have hlfp : Space.IsLocallyOfFinitePresentation B S hS ω₂.p :=
    Space.isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B S hS ω₂.isAlgebraicSpace_V'
      (isAlgebraicSpace_yoneda B S hS _) ω₂.p
      (Space.hasEtaleLocalProperty_of_representable B S hS _
        (fun T : Scheme.{u} => IsLocallyNoetherian T) (D.obj i).obj (Iso.refl _)
        (D.obj i).property) ω₂.isProper_p.2.1.1
  obtain ⟨k₁, b₁, hb₁p, hb₁x⟩ := Space.exists_stage_hom_of_isLimit
    (E := D ⋙ ObjectProperty.ι _) (c := (ObjectProperty.ι _).mapCone κ) hκ hD hpt i
    ω₁.isAlgebraicSpace_V' ω₂.isAlgebraicSpace_V' c.isAlgebraicSpace_X'.isSheaf hX'lp ω₁.p
    ω₁.isProper_p ω₂.p hlfp ω₁.x' ω₂.x' _ hap hax
  obtain ⟨ψA, hψAp, hψAx⟩ := exists_hom_pullback_of_lift c (D.map k₁.hom).hom ω₁ ω₂ b₁ hb₁p hb₁x
  exact ⟨k₁.left, k₁.hom, ω₁.pullback _ t₁, ω₂.pullback _ t₂, ψA, hψAp, hψAx⟩

include hκ hD hpt in
/-- **Once the formal components agree, the triples agree at a stage**: the second components
agree at a stage by limit preservation of `X'` (Stacks 01ZC). -/
theorem exists_mapTriple_eq_of_xhat_heq (i : I) (t₁ t₂ : Triple c (D.obj i).obj)
    (hZ : t₁.Z = t₂.Z) (hx : HEq t₁.xhat t₂.xhat)
    (h : mapTriple c (κ.π.app i).hom t₁ = mapTriple c (κ.π.app i).hom t₂) :
    ∃ (k : I) (f : k ⟶ i), mapTriple c (D.map f).hom t₁ = mapTriple c (D.map f).hom t₂ := by
  obtain ⟨Z, hcZ, u₁, x₁, a₁, w₁⟩ := t₁
  obtain ⟨Z₂, hcZ₂, u₂, x₂, a₂, w₂⟩ := t₂
  dsimp only at hZ hx
  subst hZ
  obtain rfl : x₁ = x₂ := eq_of_heq hx
  have : IsLocallyNoetherian S := c.isLocallyNoetherian_base
  have hX'lp := Space.limitPreserving_of_isLocallyOfFiniteType B S hS c.isAlgebraicSpace_X'
    c.isLocallyOfFiniteType_X'
  have hu : Space.openSubspaceOfPointsRestrict B S hS (yoneda.map (κ.π.app i).hom)
        (Space.pointsMap B S hS _ (yoneda.map (κ.π.app i).hom) ⁻¹' Z)ᶜ Zᶜ (fun _ hz => hz) ≫
        u₁ =
      Space.openSubspaceOfPointsRestrict B S hS (yoneda.map (κ.π.app i).hom)
        (Space.pointsMap B S hS _ (yoneda.map (κ.π.app i).hom) ⁻¹' Z)ᶜ Zᶜ (fun _ hz => hz) ≫ u₂ :=
    eq_of_heq (congr_arg_heq Triple.u h)
  obtain ⟨k, g, hg⟩ := exists_restrict_eq_of_isLimit c.X' c.isAlgebraicSpace_X'.isSheaf hX'lp
    hκ hD hpt i hcZ (u₁ ≫ c.U'.ι) (u₂ ≫ c.U'.ι) (by
      rw [← Category.assoc, ← Category.assoc, hu])
  refine ⟨k, g, Triple.mk_congr rfl (heq_of_eq ?_) (heq_of_eq ?_)⟩
  · rwa [← cancel_mono c.U'.ι, Category.assoc, Category.assoc]
  · rfl

end Injective

end AlgebraicGeometry.Artin.ContractionSituation

end
