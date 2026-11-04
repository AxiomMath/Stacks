module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitFormalTower
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionClosedImmersionChartAdic
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitEqualizerTorsion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.FormalFunctionsFibres

/-!
# The fibres of a proper algebraic space over the quotient stages

Let `V` be an affine Noetherian object of the site, `A = Γ(V, 𝒪_V)` and `I ⊆ A` an ideal. The
fibre `X ×_V Spec (A / I^{n+1})` of a morphism `f : X ⟶ V` maps to `Spec (A / I^{n+1})`, which
maps over `V` to the quotient stage `Spec (A^∧ ⧸ I^{n+1} A^∧)` of `V_{/V(I)} ≅ Spf A^∧`. This
is how the fibres of the descended witness `V'_μ` of the proof of Stacks 0GI5 reach the
quotient stages of `Spf A^∧`, on which
`AlgebraicGeometry.Artin.FormalRing.formalRingHom_toCompletion_comp_continuousHomEquiv`
computes ring maps.

## Main definitions

* `AlgebraicGeometry.Artin.FormalRing.adicQuotToPowStage`: the morphism
  `Spec (A / I^{n+1}) ⟶ Spec (A^∧ ⧸ I^{n+1} A^∧)` over `V`.
* `AlgebraicGeometry.Artin.FormalRing.fibreToPowStage`: the morphism
  `X ×_V Spec (A / I^{n+1}) ⟶ Spec (A^∧ ⧸ I^{n+1} A^∧)` over `V`.
* `AlgebraicGeometry.Artin.FormalRing.fibreRingHom`: the ring map
  `B ⟶ Γ(X ×_V Spec (A / I^{n+1}), 𝒪)` of a morphism `X_{/g⁻¹ V(I)} ⟶ Spf B`.

## Main results

* `AlgebraicGeometry.Artin.FormalRing.fibreRingHom_transition`: the ring maps are compatible.
* `AlgebraicGeometry.Artin.FormalRing.completionSheaf_hom_ext_fibre`: morphisms out of
  `X_{/g⁻¹ V(I)}` are determined on the fibres.
* `AlgebraicGeometry.Artin.FormalRing.eq_of_fibreRingHom_eq`: a morphism
  `X_{/g⁻¹ V(I)} ⟶ Spf B` is determined by its ring maps on the fibres.
* `AlgebraicGeometry.Artin.FormalRing.fibreRingHom_completionSheafRestrict_comp_continuousHomEquiv`
  computes the ring maps of `X_{/g⁻¹ V(I)} ⟶ V_{/V(I)} ⟶ Spf B` on the fibres.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.FormalRing

open Space FormalSpace FormalDictionary

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The `I`-adic topology on the completion `A^∧`, as a module over `A`. -/
local instance instTopologicalSpaceAdicCompletion''' {A : Type u} [CommRing A] (I : Ideal A) :
    TopologicalSpace (AdicCompletion I A) :=
  I.adicModuleTopology (AdicCompletion I A)

variable (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
  (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))

/-- A morphism of the site whose underlying morphism of schemes is a closed immersion is a
monomorphism. -/
theorem mono_of_isClosedImmersion {T T' : BigFppfOver B S hS} (g : T ⟶ T')
    [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map g)] : Mono g :=
  (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance

/-- The isomorphism `V ⟶ Spec Γ(V)` of objects of the site, inverse to `affineModelHom`. -/
def affineModelHomInv : V ⟶ affineModel V :=
  FormalSpace.siteHom B S hS ((BigFppfOver.toScheme B S hS).obj V).isoSpec.hom (by
    change _ ≫ ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv ≫ V.hom.hom = _
    rw [Iso.hom_inv_id_assoc])

omit [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] in
/-- `affineModelHomInv V` is a section of `affineModelHom V : Spec Γ(V) ⟶ V`. -/
theorem affineModelHomInv_comp : affineModelHomInv V ≫ affineModelHom V = 𝟙 V :=
  BigFppfOver.map_toScheme_injective B S hS ((Functor.map_comp _ _ _).trans
    ((Iso.hom_inv_id _).trans (CategoryTheory.Functor.map_id _ _).symm))

/-- The morphism `Spec (A / I^{n+1}) ⟶ Spec (A^∧ ⧸ I^{n+1} A^∧)` over `V`. -/
theorem exists_adicCompletionQuotientObj_toPowStage (n : ℕ) :
    ∃ c : adicCompletionQuotientObj B S hS V I (n + 1) ⟶ powStage V I n,
      c ≫ powStageToV V I n = adicCompletionQuotientObjHom B S hS V I (n + 1) := by
  let v := adicCompletionQuotientObjHom B S hS V I (n + 1) ≫ affineModelHomInv V
  have hv : ∀ a ∈ I ^ (n + 1), FormalSpace.chartRing v a = 0 := by
    intro a ha
    have e1 : FormalSpace.chartRing v a = ((BigFppfOver.toScheme B S hS).map
        (adicCompletionQuotientObjHom B S hS V I (n + 1))).appTop
          (FormalSpace.chartRing (affineModelHomInv V) a) :=
      FormalSpace.chartRing_comp _ _ a
    have e2 : FormalSpace.chartRing (affineModelHomInv V) a = a := by
      change ((Scheme.ΓSpecIso _).inv ≫
        (((BigFppfOver.toScheme B S hS).obj V).isoSpec.hom).appTop).hom a = a
      rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop, Iso.inv_hom_id]
      rfl
    rw [e1, e2]
    exact RingHom.mem_ker.1 (by rwa [Space.ker_appTop_adicCompletionQuotientObjHom])
  obtain ⟨c, hc, -⟩ := FormalSpace.exists_stage_factor (Space.contains_spec_globalSections B S hS V)
    (specStructure V) I I.fg_of_isNoetherianRing n v hv
  refine ⟨c, ?_⟩
  have hc' : c ≫ powStageToAffine V I n = v := hc
  change c ≫ powStageToAffine V I n ≫ affineModelHom V = _
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ affineModelHom V) hc').trans
    ((Category.assoc _ _ _).trans ((congrArg (adicCompletionQuotientObjHom B S hS V I (n + 1) ≫ ·)
      (affineModelHomInv_comp V)).trans (Category.comp_id _))))

/-- The morphism `Spec (A / I^{n+1}) ⟶ Spec (A^∧ ⧸ I^{n+1} A^∧)` over `V`. -/
def adicQuotToPowStage (n : ℕ) : adicCompletionQuotientObj B S hS V I (n + 1) ⟶ powStage V I n :=
  (exists_adicCompletionQuotientObj_toPowStage V I n).choose

/-- `adicQuotToPowStage V I n` is a morphism over `V`. -/
theorem adicQuotToPowStage_comp (n : ℕ) :
    adicQuotToPowStage V I n ≫ powStageToV V I n =
      adicCompletionQuotientObjHom B S hS V I (n + 1) :=
  (exists_adicCompletionQuotientObj_toPowStage V I n).choose_spec

section Fibre

variable {X : AlgebraicSpaces B S hS} (g : X.1 ⟶ yoneda.obj V)

/-- `g`, as a morphism of algebraic spaces. -/
abbrev spaceHom : X ⟶ schemeSpace V := ObjectProperty.homMk g

/-- The closed immersion `Spec (A / Iⁿ) ⟶ V` is a monomorphism. -/
instance mono_adicCompletionQuotientObjHom (n : ℕ) :
    Mono (adicCompletionQuotientObjHom B S hS V I n) :=
  mono_of_isClosedImmersion _

omit [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] in
/-- A section of the fibre `X ×_V Spec (A / Iⁿ)` over `T` gives a morphism `T ⟶ Spec (A / Iⁿ)`
whose composite with `Spec (A / Iⁿ) ⟶ V` is the image of the section under `g`. -/
theorem exists_fibre_lift (n : ℕ) {T : (BigFppfOver B S hS)ᵒᵖ}
    (y : (fibreSpace V I (spaceHom V g) n).1.obj T) :
    ∃ z : T.unop ⟶ adicCompletionQuotientObj B S hS V I n,
      z ≫ adicCompletionQuotientObjHom B S hS V I n = g.app T y.1 := by
  obtain ⟨z, hz⟩ := y.2
  exact ⟨z, hz⟩

/-- The morphism `X ×_V Spec (A / Iⁿ) ⟶ Spec (A / Iⁿ)`. -/
def fibreToQuot (n : ℕ) :
    (fibreSpace V I (spaceHom V g) n).1 ⟶ yoneda.obj (adicCompletionQuotientObj B S hS V I n) where
  app T := ↾fun y => (exists_fibre_lift V I g n y).choose
  naturality T T' k := by
    ext y
    change (exists_fibre_lift V I g n _).choose = k.unop ≫ (exists_fibre_lift V I g n y).choose
    rw [← cancel_mono (adicCompletionQuotientObjHom B S hS V I n),
      (exists_fibre_lift V I g n _).choose_spec, Category.assoc,
      (exists_fibre_lift V I g n y).choose_spec]
    exact NatTrans.naturality_apply g k y.1

omit [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] in
/-- The square of the fibre `X ×_V Spec (A / Iⁿ)` commutes. -/
theorem fibreToQuot_comp (n : ℕ) :
    fibreToQuot V I g n ≫ yoneda.map (adicCompletionQuotientObjHom B S hS V I n) =
      (fibreInclusion V I (spaceHom V g) n).hom ≫ g := by
  ext T y
  change (exists_fibre_lift V I g n y).choose ≫ adicCompletionQuotientObjHom B S hS V I n =
    g.app T y.1
  exact (exists_fibre_lift V I g n y).choose_spec

/-- The morphism `X ×_V Spec (A / I^{n+1}) ⟶ Spec (A^∧ ⧸ I^{n+1} A^∧)`. -/
def fibreToPowStage (n : ℕ) :
    (fibreSpace V I (spaceHom V g) (n + 1)).1 ⟶ yoneda.obj (powStage V I n) :=
  fibreToQuot V I g (n + 1) ≫ yoneda.map (adicQuotToPowStage V I n)

/-- `fibreToPowStage V I g n` is compatible with the morphisms to `V`. -/
theorem fibreToPowStage_comp (n : ℕ) :
    fibreToPowStage V I g n ≫ yoneda.map (powStageToV V I n) =
      (fibreInclusion V I (spaceHom V g) (n + 1)).hom ≫ g := by
  rw [fibreToPowStage, Category.assoc, ← Functor.map_comp, adicQuotToPowStage_comp,
    fibreToQuot_comp]

variable {V I} {Z : Set (Space.points B S hS (yoneda.obj V))}
  (hZI : ∀ x, x ∈ Z ↔ Space.pointsToScheme B S hS V x ∈
    ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
      (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))

include hZI in
/-- The points of `Spec (A^∧ ⧸ I^{n+1} A^∧)` map into `Z = V(I)`. -/
theorem pointsMap_powStageToV_mem (n : ℕ)
    (x : Space.points B S hS (yoneda.obj (powStage V I n))) :
    pointsMap B S hS _ (yoneda.map (powStageToV V I n)) x ∈ Z := by
  have hh := hasImageIn_powStageToV hZI n
  rw [Space.hasImageIn_iff_range_subset] at hh
  have e : yonedaEquiv.symm (powStageToV V I n) = yoneda.map (powStageToV V I n) :=
    yonedaEquiv.injective (by rw [Equiv.apply_symm_apply, yonedaEquiv_yoneda_map])
  rw [e] at hh
  exact hh ⟨x, rfl⟩

include hZI in
/-- The points of the fibre `X ×_V Spec (A / I^{n+1})` map into `g⁻¹ Z`. -/
theorem pointsMap_fibreInclusion_mem (n : ℕ)
    (x : Space.points B S hS (fibreSpace V I (spaceHom V g) (n + 1)).1) :
    pointsMap B S hS _ (fibreInclusion V I (spaceHom V g) (n + 1)).hom x ∈
      pointsMap B S hS X.1 g ⁻¹' Z := by
  have h₁ := pointsMap_powStageToV_mem hZI n (pointsMap B S hS _ (fibreToPowStage V I g n) x)
  have h₂ := Space.pointsMap_comp_apply B S hS (fibreToPowStage V I g n)
    (yoneda.map (powStageToV V I n)) x
  have h₃ := congrArg (fun m => pointsMap B S hS _ m x) (fibreToPowStage_comp V I g n)
  have h₄ := Space.pointsMap_comp_apply B S hS (fibreInclusion V I (spaceHom V g) (n + 1)).hom g x
  change pointsMap B S hS _ g (pointsMap B S hS _ _ x) ∈ Z
  rw [← h₄, ← h₃, h₂]
  exact h₁

variable {Bt : Type u} [CommRing Bt] [TopologicalSpace Bt] [IsTopologicalRing Bt]
  [IsLinearTopology Bt Bt] (hB : TopologicalRing.IsWeaklyAdmissible Bt)
  {DB : QuotientSystem B S hS Bt}

/-- **The ring map `B ⟶ Γ(X ×_V Spec (A / I^{n+1}), 𝒪)` of a morphism
`X_{/g⁻¹ V(I)} ⟶ Spf B`.** -/
def fibreRingHom (hqc : ∀ n, IsQuasiCompactSpace B S hS (fibreSpace V I (spaceHom V g) n).1)
    (F : completionSheaf B S hS X.1 (pointsMap B S hS X.1 g ⁻¹' Z) ⟶ formalSpectrum DB)
    (n : ℕ) :
    Bt →+* ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B S hS (fibreSpace V I (spaceHom V g) (n + 1)).1
          (fibreSpace V I (spaceHom V g) (n + 1)).2).O)) :=
  formalRingHom hB (fibreSpace V I (spaceHom V g) (n + 1)) (hqc (n + 1))
    (toCompletion (fibreInclusion V I (spaceHom V g) (n + 1)).hom _
      (pointsMap_fibreInclusion_mem g hZI n) ≫ F)

/-- `toCompletion m T h` only depends on the morphism `m`, not on the proof `h`. -/
theorem toCompletion_congr {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m m' : X ⟶ Y}
    (e : m = m') (T : Set (points B S hS Y)) (h : ∀ x, pointsMap B S hS X m x ∈ T)
    (h' : ∀ x, pointsMap B S hS X m' x ∈ T) : toCompletion m T h = toCompletion m' T h' := by
  subst e
  rfl

/-- Points of the source of `m` map into `T` through `m'` if `m = m'` and through `m`. -/
private theorem pointsMap_mem_of_eq {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m m' : X ⟶ Y}
    (e : m = m') {T : Set (points B S hS Y)} (h : ∀ x, pointsMap B S hS X m x ∈ T) :
    ∀ x, pointsMap B S hS X m' x ∈ T := by
  subst e
  exact h

/-- **The ring maps of the fibres are compatible.** -/
theorem fibreRingHom_transition
    (hqc : ∀ n, IsQuasiCompactSpace B S hS (fibreSpace V I (spaceHom V g) n).1)
    (F : completionSheaf B S hS X.1 (pointsMap B S hS X.1 g ⁻¹' Z) ⟶ formalSpectrum DB)
    (n : ℕ) :
    (globalSectionsRingHomSite B S hS
        (fibreTransition V I (spaceHom V g) (Nat.le_succ (n + 1)))).comp
        (fibreRingHom g hZI hB hqc F (n + 1)) = fibreRingHom g hZI hB hqc F n := by
  have hm := congrArg (fun m => m.hom)
    (fibreTransition_comp V I (spaceHom V g) (Nat.le_succ (n + 1)))
  have e := toCompletion_congr hm (pointsMap B S hS X.1 g ⁻¹' Z)
    (pointsMap_mem_of_eq hm.symm (pointsMap_fibreInclusion_mem g hZI n))
    (pointsMap_fibreInclusion_mem g hZI n)
  rw [fibreRingHom, fibreRingHom, ← formalRingHom_comp, ← Category.assoc,
    ← toCompletion_comp_left, ← e]
  rfl


omit [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] in
/-- **Morphisms out of `X_{/g⁻¹ V(I)}` are determined on the fibres** `X ×_V Spec (A / I^{n+1})`:
a section of the completion over an affine object maps to `V` through some `Spec (A / I^N)`,
the functions in `I` being nilpotent on it. -/
theorem completionSheaf_hom_ext_fibre
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    {G : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    {F₁ F₂ : completionSheaf B S hS X.1 (pointsMap B S hS X.1 g ⁻¹' Z) ⟶ G}
    (H : ∀ n, toCompletion (fibreInclusion V I (spaceHom V g) (n + 1)).hom _
        (pointsMap_fibreInclusion_mem g hZI n) ≫ F₁ =
      toCompletion (fibreInclusion V I (spaceHom V g) (n + 1)).hom _
        (pointsMap_fibreInclusion_mem g hZI n) ≫ F₂) :
    F₁ = F₂ := by
  apply Sheaf.hom_ext
  apply (BigFppfOver.topology B S hS).sheafify_hom_ext _ _ G.property
  ext W ⟨⟨x⟩, hx⟩
  change F₁.hom.app W (presheafSection B S hS x hx) = F₂.hom.app W (presheafSection B S hS x hx)
  have : (BigAffineFppf.inclusion B S hS).IsCoverDense (BigFppfOver.topology B S hS) :=
    Functor.IsDenseSubsite.isCoverDense (BigAffineFppf.topology B S hS)
      (BigFppfOver.topology B S hS) (BigAffineFppf.inclusion B S hS)
  refine Functor.IsCoverDense.ext (BigAffineFppf.inclusion B S hS) G W.unop fun V' φ => ?_
  let x' := X.1.map φ.op x
  have hx' : HasImageIn B S hS X.1 (pointsMap B S hS X.1 g ⁻¹' Z) _ x' :=
    ((completionSubfunctor B S hS X.1 (pointsMap B S hS X.1 g ⁻¹' Z)).map φ.op hx :)
  rw [← NatTrans.naturality_apply F₁.hom, ← NatTrans.naturality_apply F₂.hom,
    presheafSection_map B S hS φ x hx hx']
  -- the composite `V' ⟶ V` kills a power of `I`
  have hgx : HasImageIn B S hS (yoneda.obj V) Z _ (g.app _ x') :=
    ((completionMap B S hS g Z).app (op ((BigAffineFppf.inclusion B S hS).obj V'))
      ⟨ULift.up x', hx'⟩).2
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj V')) :=
    V'.2
  obtain ⟨N, hN⟩ := Scheme.exists_pow_le_ker_appTop ((BigFppfOver.toScheme B S hS).map (g.app _ x'))
    I I.fg_of_isNoetherianRing (toScheme_map_mem_zeroLocus_of_hasImageIn hZI hgx)
  obtain ⟨z, hz⟩ := (exists_comp_adicCompletionQuotientObjHom_iff V I (g.app _ x') (N + 1)).2
    ((Ideal.pow_le_pow_right (Nat.le_succ N)).trans hN)
  let y : (fibreSpace V I (spaceHom V g) (N + 1)).1.obj
      (op ((BigAffineFppf.inclusion B S hS).obj V')) := ⟨x', z, hz⟩
  let s := ((BigFppfOver.topology B S hS).toSheafify
    ((fibreSpace V I (spaceHom V g) (N + 1)).1 ⋙ uliftFunctor.{u + 1})).app
      (op ((BigAffineFppf.inclusion B S hS).obj V')) (ULift.up y)
  have hsec : presheafSection B S hS x' hx' =
      (toCompletion (fibreInclusion V I (spaceHom V g) (N + 1)).hom _
        (pointsMap_fibreInclusion_mem g hZI N)).hom.app _ s := by
    have hnat := congrArg (fun φ => φ.app (op ((BigAffineFppf.inclusion B S hS).obj V'))
      (ULift.up y)) ((BigFppfOver.topology B S hS).toSheafify_naturality (toCompletionPre
        (fibreInclusion V I (spaceHom V g) (N + 1)).hom _
        (pointsMap_fibreInclusion_mem g hZI N)))
    refine Eq.trans ?_ (hnat.trans ?_)
    · rfl
    · rfl
  rw [hsec]
  exact congrArg (fun F => F.hom.app _ s) (H N)

omit [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] in
/-- **A morphism `X_{/g⁻¹ V(I)} ⟶ Spf B` is determined by its ring maps on the fibres.** -/
theorem eq_of_fibreRingHom_eq [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    (hqc : ∀ n, IsQuasiCompactSpace B S hS (fibreSpace V I (spaceHom V g) n).1)
    {F₁ F₂ : completionSheaf B S hS X.1 (pointsMap B S hS X.1 g ⁻¹' Z) ⟶ formalSpectrum DB}
    (h : ∀ n, fibreRingHom g hZI hB hqc F₁ n = fibreRingHom g hZI hB hqc F₂ n) : F₁ = F₂ :=
  completionSheaf_hom_ext_fibre g hZI fun n => formalRingHom_injective hB _ (hqc (n + 1)) (h n)

section Dictionary

include hZI in
/-- **The ring maps of `X_{/g⁻¹ V(I)} ⟶ V_{/V(I)} ⟶ Spf B` on the fibres**, for a continuous
`φ : B ⟶ A^∧`: `B ⟶ A^∧ ⟶ A^∧ ⧸ I^{n+1} A^∧ ⟶ Γ(X ×_V Spec (A / I^{n+1}), 𝒪)`. -/
theorem fibreRingHom_completionSheafRestrict_comp_continuousHomEquiv
    (hqc : ∀ n, IsQuasiCompactSpace B S hS (fibreSpace V I (spaceHom V g) n).1)
    (φ : ContinuousHom DB (completionQuotientSystem V I)) (n : ℕ) :
    fibreRingHom g hZI hB hqc (completionSheafRestrict B S hS g (pointsMap B S hS X.1 g ⁻¹' Z) Z
        (fun _ hx => hx) ≫ continuousHomEquiv hZI hB φ) n =
      (pullbackRingHom B (powStage V I n) (ObjectProperty.homMk (fibreToPowStage V I g n))).comp
        ((powStageRingHom' I n).comp φ.toRingHom) := by
  have hpts : ∀ x, pointsMap B S hS _ (fibreToPowStage V I g n ≫ yoneda.map (powStageToV V I n))
      x ∈ Z := fun x => by
    rw [Space.pointsMap_comp_apply]
    exact pointsMap_powStageToV_mem hZI n _
  have hpts' := pointsMap_mem_of_eq (fibreToPowStage_comp V I g n) hpts
  have e₁ := toCompletion_comp_completionSheafRestrict
    (fibreInclusion V I (spaceHom V g) (n + 1)).hom g (pointsMap B S hS X.1 g ⁻¹' Z) Z
    (pointsMap_fibreInclusion_mem g hZI n) (fun _ hx => hx) hpts'
  have e₂ := toCompletion_congr (fibreToPowStage_comp V I g n) Z hpts hpts'
  rw [fibreRingHom, ← Category.assoc, e₁, ← e₂]
  exact formalRingHom_toCompletion_comp_continuousHomEquiv hZI hB _ (hqc (n + 1)) n _ hpts φ

end Dictionary

end Fibre

end AlgebraicGeometry.Artin.FormalRing

end
