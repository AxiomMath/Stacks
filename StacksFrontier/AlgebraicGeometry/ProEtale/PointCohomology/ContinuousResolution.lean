module

public import StacksFrontier.AlgebraicGeometry.ProEtale.PointCohomology.CoinducedAcyclic
public import StacksFrontier.CategoryTheory.Sites.AbelianSheavesAbelian
public import StacksFrontier.Homology.CompositeCollapse
public import StacksFrontier.Topology.Algebra.ContinuousMapProDiscrete
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

/-!
# The continuous cochain resolution on the pro-étale site of a field

Let `X` be a topological representation of the absolute Galois group `G` of a field `K`. The
standard resolution `X → C(G, X) → C(G, C(G, X)) → ⋯` by coinduced modules induces a resolution
of the sheaf of continuous equivariant functions with values in `X` on the pro-étale site of
`Spec K` by the sheaves attached to the coinduced modules. Exactness is local: over an object
which receives a map to `Spec Kˢᵉᵖ`, the geometric points form a trivial `G`-torsor, and the
contracting homotopy `f ↦ f(1)` of the standard resolution, twisted by the torsor, splits the
complex of sections. Global sections of these sheaves are the invariants, so the global sections
of the resolution are the homogeneous continuous cochains.

## Main results

* `AlgebraicGeometry.GaloisSheaf.GeomPt.pointHomeomorph`: the geometric points of `Spec Kˢᵉᵖ`
  form a trivial `G`-torsor.
* `AlgebraicGeometry.GaloisSheaf.exact_repAbSheaf`: a complex of representations split by a
  continuous function on cycles gives an exact complex of sheaves.
* `AlgebraicGeometry.GaloisSheaf.quasiIso_sheafResolutionι`: the sheafified standard resolution
  is a resolution.
* `AlgebraicGeometry.GaloisSheaf.rightDerivedRepAbSheafIso`: the pro-étale cohomology of the
  sheaf attached to a representation with good coefficients is its continuous cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology

universe u r w

namespace AlgebraicGeometry.GaloisSheaf

variable {K : Type u} [Field K]

/-- The absolute Galois group is locally compact, being compact and Hausdorff (instance search
does not find this within its budget). -/
instance : LocallyCompactSpace (galoisGroup K) :=
  haveI : R1Space (galoisGroup K) := T2Space.r1Space (X := galoisGroup K)
  haveI : WeaklyLocallyCompactSpace (galoisGroup K) :=
    ⟨fun _ ↦ ⟨Set.univ, isCompact_univ, Filter.univ_mem⟩⟩
  WeaklyLocallyCompactSpace.locallyCompactSpace (X := galoisGroup K)

/-! ### The geometric points of `Spec Kˢᵉᵖ` -/

/-- The geometric point `Spec Kˢᵉᵖ` is affine. -/
instance : IsAffine (pointObj K).left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (SeparableClosure K))))

namespace GeomPt

/-- Evaluation at a translate `g • φ` is evaluation at `φ` followed by `g`. -/
lemma evalRingHom_smul {V : (base K).ProEt} (g : galoisGroup K) (φ : GeomPt K V) :
    evalRingHom (g • φ) = g.toRingHom.comp (evalRingHom φ) :=
  RingHom.ext fun s ↦ eval_smul s g φ

/-- Evaluation at the tautological geometric point is bijective. -/
lemma evalRingHom_unitPt_bijective : Function.Bijective (evalRingHom (unitPt (K := K))) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (SeparableClosure K))).commRingCatIsoToRingEquiv).bijective

/-- The orbit map of the tautological geometric point of `Spec Kˢᵉᵖ`. -/
def orbitMap (g : galoisGroup K) : GeomPt K (pointObj K) := g • unitPt

/-- The orbit map of the tautological geometric point is bijective: the geometric points of
`Spec Kˢᵉᵖ` form a single free orbit. -/
lemma orbitMap_bijective : Function.Bijective (orbitMap (K := K)) := by
  let ι := evalRingHom (unitPt (K := K))
  have hι := evalRingHom_unitPt_bijective (K := K)
  constructor
  · intro g g' h
    have := congrArg evalRingHom h
    simp only [orbitMap, evalRingHom_smul] at this
    refine AlgEquiv.ext fun c ↦ ?_
    obtain ⟨s, rfl⟩ := hι.2 c
    exact congrArg (fun f : _ →+* _ ↦ f s) this
  · intro φ
    let e := RingEquiv.ofBijective ι hι
    let σ : SeparableClosure K →+* SeparableClosure K := (evalRingHom φ).comp e.symm.toRingHom
    have hσ : ∀ a : K, σ (algebraMap K _ a) = algebraMap K _ a := by
      intro a
      have h1 := congrArg (fun f : K →+* SeparableClosure K ↦ f a)
        (evalRingHom_comp_structureMap φ)
      have h2 := congrArg (fun f : K →+* SeparableClosure K ↦ f a)
        (evalRingHom_comp_structureMap (unitPt (K := K)))
      simp only [RingHom.comp_apply] at h1 h2
      have h3 : e.symm (algebraMap K _ a) = (structureMap (pointObj K)).hom a := by
        rw [← h2]
        exact e.symm_apply_apply _
      change evalRingHom φ (e.symm (algebraMap K _ a)) = _
      rw [h3, h1]
    let σa : SeparableClosure K →ₐ[K] SeparableClosure K := { σ with commutes' := hσ }
    let g : galoisGroup K := AlgEquiv.ofBijective σa (Algebra.IsAlgebraic.algHom_bijective σa)
    refine ⟨g, evalRingHom_injective ?_⟩
    rw [orbitMap, evalRingHom_smul]
    refine RingHom.ext fun s ↦ ?_
    change evalRingHom φ (e.symm (e s)) = _
    rw [e.symm_apply_apply]

/-- The orbit map of the tautological geometric point is continuous. -/
lemma continuous_orbitMap : Continuous (orbitMap (K := K)) :=
  continuous_smul_comp (pointObj K) continuous_id continuous_const

/-- **The geometric points of `Spec Kˢᵉᵖ` form a trivial torsor** under the absolute Galois
group, trivialized by the tautological point. -/
def pointHomeomorph : galoisGroup K ≃ₜ GeomPt K (pointObj K) :=
  continuous_orbitMap.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ orbitMap_bijective)

/-- `pointHomeomorph` sends `g` to the translate `g • unitPt` of the tautological point. -/
lemma pointHomeomorph_apply (g : galoisGroup K) : pointHomeomorph g = g • unitPt := rfl

/-- The inverse of `pointHomeomorph` is equivariant for left multiplication. -/
lemma pointHomeomorph_symm_smul (g : galoisGroup K) (φ : GeomPt K (pointObj K)) :
    pointHomeomorph.symm (g • φ) = g * pointHomeomorph.symm φ := by
  rw [Homeomorph.symm_apply_eq, pointHomeomorph_apply, mul_smul, ← pointHomeomorph_apply,
    Homeomorph.apply_symm_apply]

end GeomPt

/-! ### The covering by the separable closure -/

variable (K) in
/-- The structure morphism of `Spec Kˢᵉᵖ`, as a morphism of the site. -/
def toFinal : pointObj K ⟶ finalObj K :=
  MorphismProperty.Over.homMk (point K).hom (Category.comp_id _)

/-- The structure morphism `Spec Kˢᵉᵖ ⟶ Spec K` is surjective. -/
instance : Surjective (point K).hom := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of (SeparableClosure K))) := inferInstance
  exact ⟨y, Subsingleton.elim _ _⟩

variable (K) in
/-- **`Spec Kˢᵉᵖ ⟶ Spec K` is a covering** of the pro-étale site. -/
lemma generate_toFinal_mem :
    Sieve.generate (Presieve.singleton (toFinal K)) ∈
      Scheme.ProEt.topology (base K) (finalObj K) := by
  have : CompactSpace (point K).left :=
    inferInstanceAs (CompactSpace (Spec (CommRingCat.of (SeparableClosure K))))
  have : QuasiCompact (point K).hom := quasiCompact_of_compactSpace _
  apply Precoverage.generate_mem_toGrothendieck
  change (Presieve.singleton (toFinal K)).map (Scheme.ProEt.forget (base K) ⋙ Over.forget _) ∈
    Scheme.proetalePrecoverage _
  rw [Presieve.map_singleton]
  exact Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) (f := (point K).hom)
    inferInstance

/-- The objects receiving a map to `Spec Kˢᵉᵖ` form a covering sieve of every object. -/
lemma pullback_toFinal_mem (V : (base K).ProEt) :
    (Sieve.generate (Presieve.singleton (toFinal K))).pullback ((isTerminal_finalObj K).from V) ∈
      Scheme.ProEt.topology (base K) V :=
  (Scheme.ProEt.topology (base K)).pullback_stable _ (generate_toFinal_mem K)

/-- A morphism in the pullback of the covering sieve generated by `Spec Kˢᵉᵖ ⟶ Spec K` has a
source which receives a map to `Spec Kˢᵉᵖ`. -/
lemma exists_toPoint_of_mem_pullback {V W : (base K).ProEt} {p : W ⟶ V}
    (hp : (Sieve.generate (Presieve.singleton (toFinal K))).pullback
      ((isTerminal_finalObj K).from V) p) : Nonempty (W ⟶ pointObj K) := by
  obtain ⟨Z, h, f, hf, -⟩ := hp
  cases hf
  exact ⟨h⟩

/-! ### Abelian sheaves on the pro-étale site of `Spec K` -/

private theorem smallSiteWEqualsLocallyBijective_ab {D : Type w} [SmallCategory D]
    (J : GrothendieckTopology D) : J.WEqualsLocallyBijective AddCommGrpCat.{w} :=
  inferInstance

set_option linter.checkUnivs false in
variable (K) in
/-- Morphisms of abelian presheaves on the pro-étale site of `Spec K` with isomorphic
sheafifications are the locally bijective ones. -/
theorem wEqualsLocallyBijective_galois :
    (Scheme.ProEt.topology (base K)).WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) r w} := by
  let := smallSiteWEqualsLocallyBijective_ab.{max (u + 1) r w}
    ((equivSmallModel.{max (u + 1) r w} (base K).ProEt).inverse.inducedTopology
      (Scheme.ProEt.topology (base K)))
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, _, u + 1, _,
    max (u + 1) r w} _

/-! ### The sheaf attached to a topological representation -/

section RepSheaf

variable (Λ : Type r) [Ring Λ] [TopologicalSpace Λ]

/-- The sheaf of continuous equivariant functions on geometric points with values in a
topological representation of the absolute Galois group. -/
def repSheaf : TopRep.{w} Λ (galoisGroup K) ⥤
    Sheaf (Scheme.ProEt.topology (base K)) (ModuleCat.{max (u + 1) r w} Λ) where
  obj Y := contSheaf Λ Y.ρ.toRepresentation
  map f := contSheafMap f.hom.toContinuousLinearMap.toLinearMap f.hom.toContinuousLinearMap.cont
    (fun g y ↦ f.hom.isIntertwining g y)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The underlying abelian sheaf of `repSheaf`. -/
abbrev repAbSheaf : TopRep.{w} Λ (galoisGroup K) ⥤
    Sheaf (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w} :=
  repSheaf Λ ⋙ sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) r w} Λ) AddCommGrpCat)

/-- On sections, `repAbSheaf Λ` applies a morphism of representations pointwise. -/
lemma repAbSheaf_map_app_apply {Y Y' : TopRep.{w} Λ (galoisGroup K)} (f : Y ⟶ Y')
    (V : (base K).ProEt) (z : ToType (((repAbSheaf Λ).obj Y).obj.obj (op V)))
    (φ : GeomPt K V) :
    (((repAbSheaf Λ).map f).hom.app (op V) z).down.1 φ = f.hom (z.down.1 φ) := rfl

/-- The functor `repAbSheaf Λ` is additive. -/
instance additive_repAbSheaf : (repAbSheaf.{u, r, w} (K := K) Λ).Additive where
  map_add {Y Y' f g} := by
    ext V z
    rfl

variable {Λ}

/-- Sections of `repAbSheaf Λ` over `V` are equal iff they agree at every geometric point. -/
private lemma repAbSheaf_section_eq_iff {Y : TopRep.{w} Λ (galoisGroup K)} {V : (base K).ProEt}
    {z z' : ToType (((repAbSheaf Λ).obj Y).obj.obj (op V))} :
    z = z' ↔ ∀ φ : GeomPt K V, z.down.1 φ = z'.down.1 φ :=
  ⟨fun h φ ↦ congrArg (fun w : ToType (((repAbSheaf Λ).obj Y).obj.obj (op V)) ↦ w.down.1 φ) h,
    fun h ↦ ULift.ext (Subtype.ext (funext h))⟩

/-- The action of a product is the composite of the actions. -/
lemma TopRep_ρ_mul_apply (Y : TopRep.{w} Λ (galoisGroup K)) (g h : galoisGroup K) (y : Y) :
    Y.ρ (g * h) y = Y.ρ g (Y.ρ h y) := by
  rw [map_mul]
  rfl

/-- Acting by `g` undoes the action of `g⁻¹`. -/
lemma TopRep_ρ_apply_inv_apply (Y : TopRep.{w} Λ (galoisGroup K)) (g : galoisGroup K) (y : Y) :
    Y.ρ g (Y.ρ g⁻¹ y) = y := by
  rw [← TopRep_ρ_mul_apply, mul_inv_cancel, map_one]
  rfl

set_option maxHeartbeats 1000000 in
-- the proof unfolds sections of the sheafified pro-étale representation sheaves and checks
-- `change`/`rw` steps against them, which is slow to elaborate
/-- **Local splitting.** Let `Y₁ ⟶ Y₂ ⟶ Y₃` be a complex of topological representations whose
first two terms have jointly continuous actions, and suppose that a continuous function
`s : Y₂ → Y₁` splits the first map on the kernel of the second. Then the induced complex of
sheaves on the pro-étale site of `Spec K` is exact: over an object mapping to `Spec Kˢᵉᵖ`, a
cycle `z` is the image of `ψ ↦ γ s (γ⁻¹ z(ψ))`, `γ` the torsor coordinate of `ψ`. -/
theorem exact_repAbSheaf
    [HasSheafify (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w}]
    {Y₁ Y₂ Y₃ : TopRep.{w} Λ (galoisGroup K)}
    (a : Y₁ ⟶ Y₂) (b : Y₂ ⟶ Y₃) (hab : a ≫ b = 0)
    (h₁ : Continuous fun p : galoisGroup K × Y₁ ↦ Y₁.ρ p.1 p.2)
    (h₂ : Continuous fun p : galoisGroup K × Y₂ ↦ Y₂.ρ p.1 p.2)
    (s : Y₂ → Y₁) (hs : Continuous s) (hsplit : ∀ y, b.hom y = 0 → a.hom (s y) = y) :
    (ShortComplex.mk ((repAbSheaf Λ).map a) ((repAbSheaf Λ).map b)
      (by rw [← Functor.map_comp, hab, Functor.map_zero])).Exact := by
  have := wEqualsLocallyBijective_galois.{u, r, w} K
  refine (Stacks.AbelianSheaves.exact_iff_locallyLiftable.{max (u + 1) r w, u, u + 1} _).2 ?_
  intro V z hz
  refine ⟨_, pullback_toFinal_mem V, fun W p hp ↦ ?_⟩
  obtain ⟨t⟩ := exists_toPoint_of_mem_pullback hp
  let γ : GeomPt K W → galoisGroup K := fun ψ ↦ GeomPt.pointHomeomorph.symm (GeomPt.map t ψ)
  have hγ : ∀ (g : galoisGroup K) ψ, γ (g • ψ) = g * γ ψ := fun g ψ ↦ by
    simp only [γ, GeomPt.map_smul, GeomPt.pointHomeomorph_symm_smul]
  have hz' : ∀ φ, b.hom (z.down.1 φ) = 0 := repAbSheaf_section_eq_iff.1 hz
  let x : GeomPt K W → Y₁ := fun ψ ↦
    Y₁.ρ (γ ψ) (s (Y₂.ρ (γ ψ)⁻¹ (z.down.1 (GeomPt.map p ψ))))
  have hx : x ∈ contSections Λ Y₁.ρ.toRepresentation W := by
    refine ⟨fun g ψ ↦ ?_, fun A c hA ↦ ?_⟩
    · change x (g • ψ) = Y₁.ρ g (x ψ)
      have hzg : z.down.1 (GeomPt.map p (g • ψ)) = Y₂.ρ g (z.down.1 (GeomPt.map p ψ)) := by
        rw [GeomPt.map_smul]
        exact z.down.2.1 g _
      simp only [x]
      rw [hγ, hzg, mul_inv_rev, TopRep_ρ_mul_apply Y₂ (γ ψ)⁻¹ g⁻¹, ← TopRep_ρ_mul_apply Y₂ g⁻¹ g,
        inv_mul_cancel, map_one, TopRep_ρ_mul_apply Y₁]
      rfl
    · have hγc : Continuous fun φ ↦ γ (GeomPt.map c φ) := by
        change Continuous fun φ ↦ GeomPt.pointHomeomorph.symm (GeomPt.map t (GeomPt.map c φ))
        exact GeomPt.pointHomeomorph.symm.continuous.comp
          ((GeomPt.continuous_map t).comp (GeomPt.continuous_map c))
      have hzc : Continuous fun φ ↦ z.down.1 (GeomPt.map p (GeomPt.map c φ)) := by
        convert z.down.2.2 A (c ≫ p) hA using 1
        funext φ
        simp [GeomPt.map_comp]
      have h3 : Continuous fun φ ↦ Y₂.ρ (γ (GeomPt.map c φ))⁻¹
          (z.down.1 (GeomPt.map p (GeomPt.map c φ))) :=
        h₂.comp ((continuous_inv.comp hγc).prodMk hzc)
      exact h₁.comp (hγc.prodMk (hs.comp h3))
  refine ⟨⟨⟨x, hx⟩⟩, repAbSheaf_section_eq_iff.2 fun ψ ↦ ?_⟩
  change a.hom (x ψ) = z.down.1 (GeomPt.map p ψ)
  have hb : b.hom (Y₂.ρ (γ ψ)⁻¹ (z.down.1 (GeomPt.map p ψ))) = 0 := by
    rw [b.hom.isIntertwining, hz', map_zero]
  simp only [x]
  rw [a.hom.isIntertwining, hsplit _ hb, TopRep_ρ_apply_inv_apply]

end RepSheaf

/-! ### The standard resolution -/

section Resolution

variable {Λ : Type r} [Ring Λ] [TopologicalSpace Λ]

/-- The coinduced action is jointly continuous when the action is. -/
lemma continuous_coind₁_action {Y : TopRep.{w} Λ (galoisGroup K)}
    (hY : Continuous fun p : galoisGroup K × Y ↦ Y.ρ p.1 p.2) :
    Continuous fun p : galoisGroup K × C(galoisGroup K, Y) ↦ Y.ρ.coind₁ p.1 p.2 := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have h1 : Continuous fun q : (galoisGroup K × C(galoisGroup K, Y)) × galoisGroup K ↦
      q.1.2 (q.1.1⁻¹ * q.2) :=
    continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk
      ((continuous_inv.comp (continuous_fst.comp continuous_fst)).mul continuous_snd))
  exact hY.comp ((continuous_fst.comp continuous_fst).prodMk h1)

variable (X : TopRep.{max u w} Λ (galoisGroup K))

/-- The hypotheses on the coefficients that the standard resolution inherits: a jointly
continuous action, a nonarchimedean separated topology, and pro-discreteness. -/
structure GoodCoefficients (Y : TopRep.{max u w} Λ (galoisGroup K)) : Prop where
  /-- The action map `G × Y → Y` is jointly continuous. -/
  continuous_action : Continuous fun p : galoisGroup K × Y ↦ Y.ρ p.1 p.2
  /-- The additive group of `Y` is nonarchimedean. -/
  nonarchimedean : NonarchimedeanAddGroup Y
  /-- The topology of `Y` is separated. -/
  t2Space : T2Space Y
  /-- The topology of `Y` is pro-discrete. -/
  isProDiscrete : Stacks.ProfiniteCech.IsProDiscrete Y

/-- Good coefficients are inherited by the coinduced representation `C(G, Y)`. -/
lemma GoodCoefficients.coind₁ {Y : TopRep.{max u w} Λ (galoisGroup K)} (hY : GoodCoefficients Y) :
    GoodCoefficients Y.coind₁ := by
  have := hY.nonarchimedean
  have := hY.t2Space
  exact ⟨continuous_coind₁_action hY.continuous_action,
    inferInstanceAs (NonarchimedeanAddGroup C(galoisGroup K, Y)),
    inferInstanceAs (T2Space C(galoisGroup K, Y)), ContinuousMap.isProDiscrete hY.isProDiscrete⟩

/-- Every term of the standard resolution of a representation with good coefficients has good
coefficients. -/
lemma GoodCoefficients.resolutionX {X : TopRep.{max u w} Λ (galoisGroup K)}
    (hX : GoodCoefficients X) : ∀ n, GoodCoefficients (TopRep.resolutionX X n)
  | 0 => hX
  | n + 1 => (GoodCoefficients.resolutionX hX n).coind₁

/-- A cocycle of the standard resolution is the coboundary of its value at `1`. -/
lemma d_eval_one (n : ℕ) (f : TopRep.resolutionX X (n + 1))
    (hf : (TopRep.d X (n + 1)).hom f = 0) : (TopRep.d X n).hom (f 1) = f := by
  have := congrArg (fun F : C(galoisGroup K, C(galoisGroup K, TopRep.resolutionX X n)) ↦ F 1) hf
  rw [TopRep.hom_d_succ] at this
  exact (sub_eq_zero.1 (this : f - (TopRep.d X n).hom (f 1) = 0)).symm

end Resolution

/-! ### The resolution of the sheaf -/

section SheafResolution

variable (Λ : Type r) [Ring Λ] [TopologicalSpace Λ] (X : TopRep.{max u w} Λ (galoisGroup K))

/-- The functor `repAbSheaf Λ` preserves zero morphisms. -/
instance : (repAbSheaf.{u, r, max u w} (K := K) Λ).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- The sheaves attached to the standard resolution `C(G, X) → C(G, C(G, X)) → ⋯`. -/
abbrev sheafResolution :
    CochainComplex (Sheaf (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w}) ℕ :=
  ((repAbSheaf.{u, r, max u w} Λ).mapHomologicalComplex _).obj (TopRep.resolution' X)

/-- The differentials of `sheafResolution` are the images of those of the standard resolution. -/
lemma sheafResolution_d (n : ℕ) :
    (sheafResolution Λ X).d n (n + 1) = (repAbSheaf Λ).map (TopRep.d X (n + 1)) := by
  rw [Functor.mapHomologicalComplex_obj_d]
  exact congrArg _ (CochainComplex.of_d (TopRep.resolution'X X) (TopRep.resolution'd X) n)

variable [HasSheafify (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w}]

/-- The augmentation of the resolution, induced by the constant functions `X → C(G, X)`. -/
def sheafResolutionι :
    (CochainComplex.single₀ _).obj ((repAbSheaf.{u, r, max u w} Λ).obj X) ⟶ sheafResolution Λ X :=
  (CochainComplex.fromSingle₀Equiv _ _).symm ⟨(repAbSheaf Λ).map (TopRep.d X 0), by
    rw [sheafResolution_d, ← Functor.map_comp, TopRep.d_comp_d, Functor.map_zero]⟩

variable {Λ X}

omit [HasSheafify (Scheme.ProEt.topology (base K)) AddCommGrpCat] in
/-- The first map `X → C(G, X)` of the standard resolution induces a monomorphism of sheaves. -/
lemma mono_repAbSheaf_d_zero :
    Mono ((repAbSheaf.{u, r, max u w} Λ).map (TopRep.d X 0)) := by
  rw [Stacks.AbelianSheaves.mono_iff_injective.{max (u + 1) r w, u, u + 1}]
  intro V z z' h
  refine repAbSheaf_section_eq_iff.2 fun φ ↦ ?_
  exact congrArg (fun y : C(galoisGroup K, TopRep.resolutionX X 0) ↦ y 1)
    (repAbSheaf_section_eq_iff.1 h φ)

/-- **The standard resolution of a module with good coefficients is a resolution of its sheaf.** -/
theorem quasiIso_sheafResolutionι (hX : GoodCoefficients X) :
    QuasiIso (sheafResolutionι Λ X) := by
  have hexact : ∀ n, (ShortComplex.mk ((repAbSheaf.{u, r, max u w} Λ).map (TopRep.d X n))
      ((repAbSheaf Λ).map (TopRep.d X (n + 1)))
      (by rw [← Functor.map_comp, TopRep.d_comp_d, Functor.map_zero])).Exact := fun n ↦
    exact_repAbSheaf _ _ (TopRep.d_comp_d X n) (hX.resolutionX n).continuous_action
      (hX.resolutionX (n + 1)).continuous_action (fun f ↦ f 1) (continuous_eval_const 1)
      (fun f hf ↦ d_eval_one X n f hf)
  refine ⟨fun n ↦ ?_⟩
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · refine ⟨ShortComplex.exact_of_iso (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        ?_ ?_) (hexact 0), ?_⟩
      rotate_left 2
      · change Mono ((sheafResolutionι Λ X).f 0)
        rw [sheafResolutionι, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
        exact mono_repAbSheaf_d_zero
      all_goals rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt]
    · rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp)]
      refine ShortComplex.exact_of_iso ?_ (hexact (n + 1))
      refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ <;>
        exact (Category.id_comp _).trans ((sheafResolution_d Λ X _).trans (Category.comp_id _).symm)
    · exact CochainComplex.exactAt_succ_single_obj _ _

end SheafResolution

/-! ### Global sections -/

section GlobalSections

/-- The final object `Spec K` has exactly one geometric point. -/
instance : Unique (GeomPt K (finalObj K)) where
  default := Over.homMk (point K).hom (Category.comp_id _)
  uniq φ := Over.OverMorphism.ext ((Category.comp_id _).symm.trans (Over.w φ))

variable {Λ : Type r} [Ring Λ] [TopologicalSpace Λ]

/-- Sections over `Spec K` of the sheaf attached to a representation are its invariants. -/
def finalSectionsEquiv (Y : TopRep.{w} Λ (galoisGroup K)) :
    contSections Λ Y.ρ.toRepresentation (finalObj K) ≃+ Y.ρ.invariants where
  toFun s := ⟨s.1 default, fun g ↦ ((s.2.1 g default).symm.trans
    (congrArg s.1 (Subsingleton.elim _ _)) :)⟩
  invFun v := ⟨fun _ ↦ v.1, fun g _ ↦ (v.2 g).symm, fun _ _ _ ↦ continuous_const⟩
  left_inv s := Subtype.ext (funext fun _ ↦ congrArg s.1 (Subsingleton.elim _ _))
  right_inv _ := rfl
  map_add' _ _ := rfl

variable (Λ) in
/-- **Global sections of the sheaf attached to a representation are its invariants**,
naturally. -/
def sectionsFinalIso :
    repAbSheaf.{u, r, w} Λ ⋙ (sheafSections _ _).obj (op (finalObj K)) ≅
      TopRep.invariantsFunctor Λ (galoisGroup K) ⋙ forget₂ (TopModuleCat Λ) (ModuleCat Λ) ⋙
        forget₂ (ModuleCat Λ) AddCommGrpCat ⋙ AddCommGrpCat.uliftFunctor.{max (u + 1) r} :=
  NatIso.ofComponents (fun Y ↦ (AddEquiv.ulift.trans
    ((finalSectionsEquiv Y).trans AddEquiv.ulift.symm)).toAddCommGrpIso) (by
      intro Y Y' f
      ext z
      rfl)

end GlobalSections

/-! ### Cohomology -/

section Cohomology

variable (Λ : Type r) [Ring Λ] [TopologicalSpace Λ]

set_option linter.checkUnivs false in
/-- The underlying abelian group of a topological module, in the coefficient universe of the
sheaves on the pro-étale site of `Spec K`. -/
def underlyingAb : TopModuleCat.{max u w} Λ ⥤ AddCommGrpCat.{max (u + 1) r w} :=
  forget₂ (TopModuleCat Λ) (ModuleCat Λ) ⋙ forget₂ (ModuleCat Λ) AddCommGrpCat ⋙
    AddCommGrpCat.uliftFunctor.{max (u + 1) r}

universe v v'

/-- The forgetful functor from topological modules to modules is additive. -/
theorem additive_forget₂_topModuleCat (R : Type r) [Ring R] [TopologicalSpace R] :
    (forget₂ (TopModuleCat.{v} R) (ModuleCat.{v} R)).Additive where
  map_add := rfl

/-- The forgetful functor from modules to abelian groups is additive. -/
theorem additive_forget₂_moduleCat (R : Type r) [Ring R] :
    (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).Additive := inferInstance

/-- The universe lift of abelian groups is additive. -/
theorem additive_uliftFunctor : (AddCommGrpCat.uliftFunctor.{v', v}).Additive where
  map_add := rfl

/-- The forgetful functor from topological modules to modules preserves homology. -/
theorem preservesHomology_forget₂_topModuleCat (R : Type r) [Ring R]
    [TopologicalSpace R] : (forget₂ (TopModuleCat.{v} R) (ModuleCat.{v} R)).PreservesHomology :=
  inferInstance

/-- The forgetful functor from modules to abelian groups preserves homology. -/
theorem preservesHomology_forget₂_moduleCat (R : Type r) [Ring R] :
    (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).PreservesHomology := inferInstance

/-- The universe lift of abelian groups preserves homology. -/
theorem preservesHomology_uliftFunctor :
    (AddCommGrpCat.uliftFunctor.{v', v}).PreservesHomology := inferInstance

/-- The functor `underlyingAb Λ` is additive. -/
instance additive_underlyingAb : (underlyingAb.{u, r, w} Λ).Additive := by
  have := additive_forget₂_topModuleCat.{r, max u w} Λ
  have := additive_forget₂_moduleCat.{r, max u w} Λ
  have := additive_uliftFunctor.{max (u + 1) r, max u w}
  unfold underlyingAb
  infer_instance

/-- The functor `underlyingAb Λ` preserves zero morphisms. -/
instance preservesZeroMorphisms_underlyingAb :
    (underlyingAb.{u, r, w} Λ).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- Homology of complexes of topological modules is computed on underlying abelian groups. -/
def underlyingAbHomologyIso (C : CochainComplex (TopModuleCat.{max u w} Λ) ℕ) (n : ℕ) :
    (((underlyingAb.{u, r, w} Λ).mapHomologicalComplex _).obj C).homology n ≅
      (underlyingAb.{u, r, w} Λ).obj (C.homology n) :=
  haveI := preservesHomology_forget₂_topModuleCat.{r, max u w} Λ
  haveI := preservesHomology_forget₂_moduleCat.{r, max u w} Λ
  haveI := preservesHomology_uliftFunctor.{max (u + 1) r, max u w}
  haveI := additive_forget₂_moduleCat.{r, max u w} Λ
  haveI := additive_uliftFunctor.{max (u + 1) r, max u w}
  (((C.sc n).map (forget₂ (TopModuleCat Λ) (ModuleCat Λ))).map
      (forget₂ (ModuleCat Λ) AddCommGrpCat)).mapHomologyIso
        AddCommGrpCat.uliftFunctor.{max (u + 1) r} ≪≫
    AddCommGrpCat.uliftFunctor.mapIso
      (((C.sc n).map (forget₂ (TopModuleCat Λ) (ModuleCat Λ))).mapHomologyIso
        (forget₂ (ModuleCat Λ) AddCommGrpCat) ≪≫
      (forget₂ (ModuleCat Λ) AddCommGrpCat).mapIso
        ((C.sc n).mapHomologyIso (forget₂ (TopModuleCat Λ) (ModuleCat Λ))))

variable {Λ} (X : TopRep.{max u w} Λ (galoisGroup K))

variable (K) in
/-- Global sections of the sheaves attached to representations are their invariants. -/
def ΓRepAbSheafIso [HasSheafify (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w}] :
    repAbSheaf.{u, r, max u w} Λ ⋙ Sheaf.Γ (Scheme.ProEt.topology (base K))
      AddCommGrpCat.{max (u + 1) r w} ≅
      TopRep.invariantsFunctor Λ (galoisGroup K) ⋙ underlyingAb.{u, r, w} Λ :=
  Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections _ _ (isTerminal_finalObj K)) ≪≫
    sectionsFinalIso.{u, r, max u w} Λ

variable [HasSheafify (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w}]
  [EnoughInjectives (Sheaf (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w})]
  [(Sheaf.Γ (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w}).Additive]

/-- The global sections of the sheafified standard resolution are the homogeneous continuous
cochains. -/
def mapSheafResolutionIso :
    ((Sheaf.Γ (Scheme.ProEt.topology (base K))
      AddCommGrpCat.{max (u + 1) r w}).mapHomologicalComplex _).obj (sheafResolution Λ X) ≅
      ((underlyingAb.{u, r, w} Λ).mapHomologicalComplex _).obj (TopRep.homogeneousCochains X) :=
  (Functor.mapHomologicalComplexCompIso (ΓRepAbSheafIso.{u, r, w} K) _).app _ ≪≫
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (TopRep.invariantsFunctor Λ (galoisGroup K) ⋙
      underlyingAb.{u, r, w} Λ)) _).app _).symm

/-- **The pro-étale cohomology of the sheaf attached to a representation with good coefficients
is its continuous group cohomology.** -/
def rightDerivedRepAbSheafIso (hX : GoodCoefficients X) (n : ℕ) :
    ((Sheaf.Γ (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w}).rightDerived n).obj
      ((repAbSheaf.{u, r, max u w} Λ).obj X) ≅
      (underlyingAb.{u, r, w} Λ).obj (continuousCohomology n X) :=
  haveI := quasiIso_sheafResolutionι hX
  Stacks.RightDerivedComp.isoRightDerivedObjOfAcyclic _ (sheafResolutionι Λ X) (fun q m hm ↦ by
      have := (hX.resolutionX q).nonarchimedean
      have := (hX.resolutionX q).t2Space
      exact isZero_rightDerived_coindAbSheaf (TopRep.resolutionX X q)
        (hX.resolutionX q).continuous_action (hX.resolutionX q).isProDiscrete m hm) n ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso (mapSheafResolutionIso X) ≪≫
    underlyingAbHomologyIso.{u, r, w} Λ (TopRep.homogeneousCochains X) n

end Cohomology

end AlgebraicGeometry.GaloisSheaf
