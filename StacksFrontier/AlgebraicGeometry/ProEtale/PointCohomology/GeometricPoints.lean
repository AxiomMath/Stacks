module

public import Mathlib.FieldTheory.KrullTopology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointDirectSumCohomology
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Characterization
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.GeometricPointStalk
public import StacksFrontier.RingTheory.WeaklyEtale.Field
public import StacksFrontier.RingTheory.WeaklyEtale.MaximalSubalgebra
public import StacksFrontier.AlgebraicGeometry.ProEtale.CompletedGaloisSheaf

/-!
# Geometric points of objects of the pro-étale site of a field

Let `K` be a field with separable closure `Kˢᵉᵖ` and absolute Galois group `G`. For an object `V`
of the small pro-étale site of `Spec K`, the *geometric points* of `V` are the morphisms
`Spec Kˢᵉᵖ ⟶ V` over `Spec K`. The Galois group acts on them by precomposition, and they are
functorial in `V`.

Every global section `s` of `V` can be evaluated at a geometric point, giving an element of
`Kˢᵉᵖ`. The geometric points carry the coarsest topology for which all these evaluations are
locally constant. Morphisms of the site induce continuous maps, and the Galois action is
continuous.

## Main definitions

* `AlgebraicGeometry.GaloisSheaf.GeomPt`: the geometric points of an object of the site.
* `AlgebraicGeometry.GaloisSheaf.GeomPt.map`: the map induced by a morphism of the site.
* `AlgebraicGeometry.GaloisSheaf.GeomPt.eval`: evaluation of a global section.

## Main results

* `AlgebraicGeometry.GaloisSheaf.GeomPt.continuous_map`: induced maps are continuous.
* `AlgebraicGeometry.GaloisSheaf.GeomPt.continuous_smul`: the Galois action is continuous.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology

universe u

namespace AlgebraicGeometry.GaloisSheaf

variable (K : Type u) [Field K]

/-- The identity of the Galois group acts on `Spec Kˢᵉᵖ` as the identity. -/
lemma pointAction_one : pointAction K 1 = 𝟙 (point K) := by
  apply Over.OverMorphism.ext
  show Spec.map (CommRingCat.ofHom (RingHom.id _)) = 𝟙 _
  exact Spec.map_id _

/-- The action of a product `g * h` on `Spec Kˢᵉᵖ` is the composite of the action of `g` followed
by the action of `h`. -/
lemma pointAction_mul (g h : galoisGroup K) :
    pointAction K (g * h) = pointAction K g ≫ pointAction K h := by
  apply Over.OverMorphism.ext
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The geometric points of an object `V` of the small pro-étale site of `Spec K`: the morphisms
`Spec Kˢᵉᵖ ⟶ V` over `Spec K`. -/
abbrev GeomPt (V : (base K).ProEt) : Type u :=
  point K ⟶ (Scheme.ProEt.forget (base K)).obj V

namespace GeomPt

variable {K}

/-- The Galois group acts on the geometric points of `V` by precomposition with its action on
`Spec Kˢᵉᵖ`. -/
instance (V : (base K).ProEt) : MulAction (galoisGroup K) (GeomPt K V) where
  smul g φ := pointAction K g ≫ φ
  one_smul φ := by
    change pointAction K 1 ≫ φ = φ
    rw [pointAction_one, Category.id_comp]
  mul_smul g h φ := by
    change pointAction K (g * h) ≫ φ = pointAction K g ≫ (pointAction K h ≫ φ)
    rw [pointAction_mul, Category.assoc]

/-- The Galois action on a geometric point is precomposition with the action on `Spec Kˢᵉᵖ`. -/
lemma smul_def {V : (base K).ProEt} (g : galoisGroup K) (φ : GeomPt K V) :
    g • φ = pointAction K g ≫ φ := rfl

/-- The map on geometric points induced by a morphism of the site. -/
def map {V W : (base K).ProEt} (f : V ⟶ W) (φ : GeomPt K V) : GeomPt K W :=
  φ ≫ (Scheme.ProEt.forget (base K)).map f

/-- The identity morphism induces the identity on geometric points. -/
@[simp]
lemma map_id (V : (base K).ProEt) (φ : GeomPt K V) : map (𝟙 V) φ = φ := by
  simp [map]

/-- The map on geometric points induced by a composite is the composite of the induced maps. -/
lemma map_comp {U V W : (base K).ProEt} (f : U ⟶ V) (g : V ⟶ W) (φ : GeomPt K U) :
    map (f ≫ g) φ = map g (map f φ) := by
  simp [map]

/-- The map on geometric points induced by a morphism of the site is Galois-equivariant. -/
lemma map_smul {V W : (base K).ProEt} (f : V ⟶ W) (g : galoisGroup K) (φ : GeomPt K V) :
    map f (g • φ) = g • map f φ := by
  simp [map, smul_def]

/-- The underlying morphism of schemes `Spec Kˢᵉᵖ ⟶ V` of a geometric point. -/
def ptLeft {V : (base K).ProEt} (φ : GeomPt K V) :
    Spec (CommRingCat.of (SeparableClosure K)) ⟶ V.left :=
  φ.left

/-- The underlying morphism of `map f φ` is that of `φ` followed by the morphism underlying
`f`. -/
lemma ptLeft_map {V W : (base K).ProEt} (f : V ⟶ W) (φ : GeomPt K V) :
    ptLeft (map f φ) = ptLeft φ ≫ f.left := rfl

/-- The underlying morphism of `g • φ` is `Spec g` followed by that of `φ`. -/
lemma ptLeft_smul {V : (base K).ProEt} (g : galoisGroup K) (φ : GeomPt K V) :
    ptLeft (g • φ) = Spec.map (CommRingCat.ofHom g.toRingHom) ≫ ptLeft φ := rfl

/-- Evaluation of a global section of `V` at a geometric point. -/
def eval {V : (base K).ProEt} (s : Γ(V.left, ⊤)) (φ : GeomPt K V) : SeparableClosure K :=
  (Scheme.ΓSpecIso (CommRingCat.of (SeparableClosure K))).hom ((ptLeft φ).appTop s)

/-- Evaluating a global section of `W` at `map f φ` is evaluating its pullback along `f` at
`φ`. -/
lemma eval_map {V W : (base K).ProEt} (f : V ⟶ W) (s : Γ(W.left, ⊤)) (φ : GeomPt K V) :
    eval s (map f φ) = eval (f.left.appTop s) φ := by
  simp only [eval, ptLeft_map, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- Evaluation of a global section is Galois-equivariant: its value at `g • φ` is `g` applied to
its value at `φ`. -/
lemma eval_smul {V : (base K).ProEt} (s : Γ(V.left, ⊤)) (g : galoisGroup K)
    (φ : GeomPt K V) : eval s (g • φ) = g (eval s φ) := by
  simp only [eval, ptLeft_smul, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  show ((Spec.map (CommRingCat.ofHom g.toRingHom)).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of (SeparableClosure K))).hom) ((ptLeft φ).appTop s) = _
  rw [Scheme.ΓSpecIso_naturality]
  rfl

/-- The topology on geometric points: the coarsest one for which evaluation of every global
section is locally constant. -/
instance (V : (base K).ProEt) : TopologicalSpace (GeomPt K V) :=
  ⨅ s : Γ(V.left, ⊤), TopologicalSpace.induced (eval s) ⊥

/-- Evaluation of a global section is a locally constant function on geometric points. -/
lemma isLocallyConstant_eval {V : (base K).ProEt} (s : Γ(V.left, ⊤)) :
    IsLocallyConstant (eval (K := K) s) :=
  IsLocallyConstant.iff_isOpen_fiber.2 fun c ↦
    (iInf_le (fun s : Γ(V.left, ⊤) ↦ TopologicalSpace.induced (eval (K := K) s) ⊥) s) _
      ⟨{c}, trivial, rfl⟩

/-- A map into the geometric points is continuous if all its evaluations are locally constant. -/
private lemma continuous_of_isLocallyConstant_eval {V : (base K).ProEt} {X : Type*}
    [TopologicalSpace X] {f : X → GeomPt K V} (h : ∀ s, IsLocallyConstant (eval s ∘ f)) :
    Continuous f :=
  continuous_iInf_rng.2 fun s ↦ continuous_induced_rng.2 <|
    @IsLocallyConstant.continuous _ _ _ ⊥ _ (h s)

/-- The map on geometric points induced by a morphism of the site is continuous. -/
lemma continuous_map {V W : (base K).ProEt} (f : V ⟶ W) : Continuous (map (K := K) f) := by
  refine continuous_of_isLocallyConstant_eval fun s ↦ ?_
  rw [show eval s ∘ map (K := K) f = eval (f.left.appTop s) from funext (eval_map f s)]
  exact isLocallyConstant_eval _

/-- The set of Galois elements agreeing with a given one at an element of `Kˢᵉᵖ` is open. -/
lemma isOpen_setOf_apply_eq (c : SeparableClosure K) (g₀ : galoisGroup K) :
    IsOpen {g : galoisGroup K | g c = g₀ c} := by
  let E : IntermediateField K (SeparableClosure K) := IntermediateField.adjoin K {c}
  have : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral c)
  have hH : IsOpen ((MulAction.stabilizer (galoisGroup K) c : Subgroup (galoisGroup K)) :
      Set (galoisGroup K)) :=
    Subgroup.isOpen_mono (H₁ := E.fixingSubgroup)
      (fun g hg ↦ hg ⟨c, IntermediateField.subset_adjoin K {c} rfl⟩) E.fixingSubgroup_isOpen
  have : {g : galoisGroup K | g c = g₀ c} = (fun g ↦ g₀⁻¹ * g) ⁻¹'
      ((MulAction.stabilizer (galoisGroup K) c : Subgroup (galoisGroup K)) : Set _) := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    show g c = g₀ c ↔ (g₀⁻¹ * g) c = c
    rw [AlgEquiv.mul_apply]
    exact (AlgEquiv.symm_apply_eq g₀).symm
  rw [this]
  exact hH.preimage (continuous_const.mul continuous_id)

/-- The action of the Galois group on geometric points is jointly continuous. -/
lemma continuous_smul (V : (base K).ProEt) :
    Continuous fun p : galoisGroup K × GeomPt K V ↦ p.1 • p.2 := by
  refine continuous_of_isLocallyConstant_eval fun s ↦ ?_
  rw [IsLocallyConstant.iff_exists_open]
  rintro ⟨g₀, φ₀⟩
  refine ⟨{g : galoisGroup K | g (eval s φ₀) = g₀ (eval s φ₀)} ×ˢ (eval s ⁻¹' {eval s φ₀}),
    (isOpen_setOf_apply_eq _ g₀).prod ((isLocallyConstant_eval s).isOpen_fiber _),
    ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨g, φ⟩ ⟨hg, hφ⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hφ
  simp only [Function.comp_apply, eval_smul, hφ]
  exact hg

/-- The Galois action on geometric points is continuous in both variables, along continuous
maps. -/
lemma continuous_smul_comp (V : (base K).ProEt) {Z : Type*} [TopologicalSpace Z]
    {f : Z → galoisGroup K} {g : Z → GeomPt K V} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun z ↦ f z • g z := by
  have := (continuous_smul V).comp' (hf.prodMk hg)
  beta_reduce at this
  exact this

/-! ### Geometric points of affine objects -/

section Affine

/-- The structure morphism `V ⟶ Spec K` of an object of the site. -/
def strHom (V : (base K).ProEt) : V.left ⟶ Spec (CommRingCat.of K) := V.hom

/-- A geometric point lies over the geometric point `Spec Kˢᵉᵖ ⟶ Spec K`. -/
lemma ptLeft_comp_strHom {V : (base K).ProEt} (φ : GeomPt K V) :
    ptLeft φ ≫ strHom V = Spec.map (CommRingCat.ofHom (algebraMap K (SeparableClosure K))) :=
  Over.w φ

/-- The structure map `K → Γ(V, ⊤)` of an object of the site. -/
def structureMap (V : (base K).ProEt) : CommRingCat.of K ⟶ Γ(V.left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (strHom V).appTop

/-- Evaluation at a geometric point, as a ring homomorphism on global sections. -/
def evalRingHom {V : (base K).ProEt} (φ : GeomPt K V) : Γ(V.left, ⊤) →+* SeparableClosure K :=
  ((ptLeft φ).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (SeparableClosure K))).hom).hom

/-- The ring homomorphism `evalRingHom φ` sends a global section `s` to `eval s φ`. -/
lemma evalRingHom_apply {V : (base K).ProEt} (φ : GeomPt K V) (s : Γ(V.left, ⊤)) :
    evalRingHom φ s = eval s φ := rfl

/-- Evaluation at a geometric point is a `K`-algebra map: precomposed with the structure map it
is the inclusion `K → Kˢᵉᵖ`. -/
lemma evalRingHom_comp_structureMap {V : (base K).ProEt} (φ : GeomPt K V) :
    (evalRingHom φ).comp (structureMap V).hom = algebraMap K (SeparableClosure K) := by
  have h : (strHom V).appTop ≫ (ptLeft φ).appTop =
      (Spec.map (CommRingCat.ofHom (algebraMap K (SeparableClosure K)))).appTop :=
    congrArg Scheme.Hom.appTop (ptLeft_comp_strHom φ)
  have h' : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (strHom V).appTop ≫ (ptLeft φ).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (SeparableClosure K))).hom =
      CommRingCat.ofHom (algebraMap K (SeparableClosure K)) := by
    rw [reassoc_of% h, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact congrArg CommRingCat.Hom.hom h'

/-- For an affine scheme `X`, the map on global sections induced by `X.isoSpec.inv` is the inverse
of `Scheme.ΓSpecIso Γ(X, ⊤)`. -/
lemma isoSpec_inv_appTop' (X : Scheme.{u}) [IsAffine X] :
    X.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).inv := by
  have h := congrArg Scheme.Hom.appTop X.isoSpec.inv_hom_id
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at h
  have e : X.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).hom := Scheme.toSpecΓ_appTop X
  rw [e] at h
  rw [← Category.id_comp X.isoSpec.inv.appTop, ← (Scheme.ΓSpecIso Γ(X, ⊤)).inv_hom_id,
    Category.assoc, h, Category.comp_id]

variable {V : (base K).ProEt} [IsAffine V.left]

/-- On an affine object, a geometric point is determined by its evaluation ring homomorphism. -/
lemma evalRingHom_injective : Function.Injective (evalRingHom (K := K) (V := V)) := by
  intro φ ψ h
  apply Over.OverMorphism.ext
  show ptLeft φ = ptLeft ψ
  apply ext_of_isAffine
  have h' : (ptLeft φ).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (SeparableClosure K))).hom =
      (ptLeft ψ).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (SeparableClosure K))).hom :=
    CommRingCat.hom_ext h
  simpa using h'

/-- On an affine object, every `K`-algebra map from the global sections to `Kˢᵉᵖ` is the
evaluation at some geometric point. -/
lemma exists_evalRingHom_eq (f : Γ(V.left, ⊤) →+* SeparableClosure K)
    (hf : f.comp (structureMap V).hom = algebraMap K (SeparableClosure K)) :
    ∃ φ : GeomPt K V, evalRingHom φ = f := by
  let ψ : Spec (CommRingCat.of (SeparableClosure K)) ⟶ V.left :=
    Spec.map (CommRingCat.ofHom f) ≫ V.left.isoSpec.inv
  have happ : ψ.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (SeparableClosure K))).hom =
      CommRingCat.ofHom f := by
    simp only [ψ, Scheme.Hom.comp_appTop, isoSpec_inv_appTop', Category.assoc,
      Scheme.ΓSpecIso_naturality]
    exact Iso.inv_hom_id_assoc (Scheme.ΓSpecIso Γ(V.left, ⊤)) _
  have hw : ψ ≫ strHom V =
      Spec.map (CommRingCat.ofHom (algebraMap K (SeparableClosure K))) := by
    apply ext_of_isAffine
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of K)).inv,
      ← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of (SeparableClosure K))).hom]
    simp only [Scheme.Hom.comp_appTop, Category.assoc, happ, Scheme.ΓSpecIso_naturality,
      Iso.inv_hom_id_assoc]
    rw [← hf]
    rfl
  exact ⟨Over.homMk ψ hw, CommRingCat.hom_ext_iff.1 happ⟩

/-- The global sections of an affine object of the site form a weakly étale algebra over
`K`. -/
lemma weaklyEtale_structureMap (V : (base K).ProEt) [IsAffine V.left] :
    @Algebra.WeaklyEtale K Γ(V.left, ⊤) _ _ (structureMap V).hom.toAlgebra := by
  have h1 : WeaklyEtale (Spec.map (strHom V).appTop) :=
    (MorphismProperty.arrow_mk_iso_iff (P := @WeaklyEtale)
      (arrowIsoSpecΓOfIsAffine (strHom V))).1 V.prop
  have h2 : WeaklyEtale (Spec.map (structureMap V)) := by
    rw [structureMap, Spec.map_comp]
    infer_instance
  exact (weaklyEtale_specMap_iff (structureMap V)).1 h2

/-- The global sections of an affine object of the site are integral over `K`. -/
lemma isIntegral_structureMap (V : (base K).ProEt) [IsAffine V.left] :
    @Algebra.IsIntegral K Γ(V.left, ⊤) _ _ (structureMap V).hom.toAlgebra := by
  let := (structureMap V).hom.toAlgebra
  exact (structure_of_weaklyEtale_over_field.{u, u, u} K Γ(V.left, ⊤)
    (weaklyEtale_structureMap V)).2.1

/-- The evaluation of all global sections at a geometric point. -/
def evalAll (V : (base K).ProEt) (φ : GeomPt K V) : Γ(V.left, ⊤) → SeparableClosure K :=
  fun s ↦ eval s φ

/-- With `Kˢᵉᵖ` discrete, the topology on geometric points is induced by `evalAll V` from the
product topology. -/
lemma isInducing_evalAll (V : (base K).ProEt) :
    letI : TopologicalSpace (SeparableClosure K) := ⊥
    Topology.IsInducing (evalAll V) := by
  let : TopologicalSpace (SeparableClosure K) := ⊥
  rw [Topology.isInducing_iff, Pi.topologicalSpace, induced_iInf]
  simp only [induced_compose]
  rfl

variable {V : (base K).ProEt} [IsAffine V.left]

/-- On an affine object, the range of `evalAll V` consists of the functions from global sections
to `Kˢᵉᵖ` that are additive, multiplicative, unital and compatible with the structure maps from
`K`. -/
lemma range_evalAll :
    Set.range (evalAll (K := K) V) = {f | (∀ s t, f (s + t) = f s + f t) ∧
      (∀ s t, f (s * t) = f s * f t) ∧ f 1 = 1 ∧
        ∀ k : K, f (structureMap V k) = algebraMap K (SeparableClosure K) k} := by
  ext f
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨map_add (evalRingHom φ), map_mul (evalRingHom φ), map_one (evalRingHom φ),
      RingHom.congr_fun (evalRingHom_comp_structureMap φ)⟩
  · rintro ⟨hadd, hmul, hone, halg⟩
    let F : Γ(V.left, ⊤) →+* SeparableClosure K :=
      { toFun := f
        map_one' := hone
        map_mul' := hmul
        map_zero' := by simpa using hadd 0 0
        map_add' := hadd }
    obtain ⟨φ, hφ⟩ := exists_evalRingHom_eq F (RingHom.ext halg)
    exact ⟨φ, funext fun s ↦ RingHom.congr_fun hφ s⟩

/-- On an affine object, the value of a global section `s` at a geometric point is a root in
`Kˢᵉᵖ` of the minimal polynomial of `s` over `K`. -/
lemma evalAll_mem_rootSet (φ : GeomPt K V) (s : Γ(V.left, ⊤)) :
    letI := (structureMap V).hom.toAlgebra
    evalAll V φ s ∈ (minpoly K s).rootSet (SeparableClosure K) := by
  let := (structureMap V).hom.toAlgebra
  have hint : _root_.IsIntegral K s := (isIntegral_structureMap V).isIntegral s
  let F : Γ(V.left, ⊤) →ₐ[K] SeparableClosure K :=
    { evalRingHom φ with commutes' := fun k ↦
        RingHom.congr_fun (evalRingHom_comp_structureMap φ) k }
  rw [Polynomial.mem_rootSet]
  refine ⟨minpoly.ne_zero hint, ?_⟩
  show Polynomial.aeval (F s) (minpoly K s) = 0
  rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]

/-- The geometric points of an affine object of the site form a Hausdorff space. -/
instance : T2Space (GeomPt K V) := by
  let : TopologicalSpace (SeparableClosure K) := ⊥
  have : DiscreteTopology (SeparableClosure K) := ⟨rfl⟩
  exact (Topology.IsEmbedding.mk (isInducing_evalAll V) fun φ ψ h ↦
    evalRingHom_injective (RingHom.ext fun s ↦ congrFun h s)).t2Space

/-- The geometric points of an affine object of the site form a totally disconnected space. -/
instance : TotallyDisconnectedSpace (GeomPt K V) := by
  let : TopologicalSpace (SeparableClosure K) := ⊥
  have : DiscreteTopology (SeparableClosure K) := ⟨rfl⟩
  have he : Topology.IsEmbedding (evalAll V) := Topology.IsEmbedding.mk (isInducing_evalAll V)
    fun φ ψ h ↦ evalRingHom_injective (RingHom.ext fun s ↦ congrFun h s)
  exact he.isTotallyDisconnected_range.1 (isTotallyDisconnected_of_totallyDisconnectedSpace _)

/-- The geometric points of an affine object of the site form a compact space. -/
instance : CompactSpace (GeomPt K V) := by
  let : TopologicalSpace (SeparableClosure K) := ⊥
  have : DiscreteTopology (SeparableClosure K) := ⟨rfl⟩
  have : ContinuousAdd (SeparableClosure K) := ⟨continuous_of_discreteTopology⟩
  have : ContinuousMul (SeparableClosure K) := ⟨continuous_of_discreteTopology⟩
  let := (structureMap V).hom.toAlgebra
  have hclosed : IsClosed (Set.range (evalAll (K := K) V)) := by
    rw [range_evalAll]
    simp only [Set.ofPred_and]
    refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun s ↦ isClosed_iInter fun t ↦ isClosed_eq (continuous_apply _)
        ((continuous_apply s).add (continuous_apply t))
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun s ↦ isClosed_iInter fun t ↦ isClosed_eq (continuous_apply _)
        ((continuous_apply s).mul (continuous_apply t))
    · exact isClosed_eq (continuous_apply _) continuous_const
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun k ↦ isClosed_eq (continuous_apply _) continuous_const
  have hsub : Set.range (evalAll (K := K) V) ⊆
      Set.univ.pi fun s ↦ (minpoly K s).rootSet (SeparableClosure K) := by
    rintro _ ⟨φ, rfl⟩ s -
    exact evalAll_mem_rootSet φ s
  have hcpt : IsCompact (Set.univ.pi fun s : Γ(V.left, ⊤) ↦
      (minpoly K s).rootSet (SeparableClosure K)) :=
    isCompact_univ_pi fun s ↦ (Polynomial.rootSet_finite _ _).isCompact
  have : IsCompact (Set.range (evalAll (K := K) V)) := hcpt.of_isClosed_subset hclosed hsub
  rw [← Set.image_univ, ← (isInducing_evalAll V).isCompact_iff] at this
  exact ⟨this⟩

end Affine

/-! ### Lifting geometric points along coverings -/

section Lifting

/-- A geometric point lifts along a morphism of the site whose image contains the point of `V`
underlying the geometric point. -/
lemma exists_map_eq_of_mem_range {V W : (base K).ProEt} (f : W ⟶ V) (φ : GeomPt K V)
    (w : W.left)
    (hw : f.left w = (ptLeft φ) (IsLocalRing.closedPoint (SeparableClosure K))) :
    ∃ ψ : GeomPt K W, map f ψ = φ := by
  let := StrictlyHenselianLocalRing.of_isSepClosed (SeparableClosure K)
  have hW : WeaklyEtale (strHom W) := W.prop
  have hV : WeaklyEtale (strHom V) := V.prop
  have hfw : f.left ≫ strHom V = strHom W := MorphismProperty.Over.w f
  have : WeaklyEtale (f.left ≫ strHom V) := by rwa [hfw]
  have : WeaklyEtale f.left := WeaklyEtale.of_comp f.left (strHom V)
  let g := ptLeft φ
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := f.left) (g := g) w
    (IsLocalRing.closedPoint (SeparableClosure K)) hw
  let Z := pullback f.left g
  let k := Z.residueField z
  let t : Spec (CommRingCat.of k) ⟶ W.left := Z.fromSpecResidueField z ≫ pullback.fst f.left g
  let pr : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (SeparableClosure K)) :=
    Z.fromSpecResidueField z ≫ pullback.snd f.left g
  have hp : pr (IsLocalRing.closedPoint k) =
      IsLocalRing.closedPoint (CommRingCat.of (SeparableClosure K)) := Subsingleton.elim _ _
  have ht : t ≫ f.left = pr ≫ g := by
    simp only [t, pr, Category.assoc, pullback.condition]
  obtain ⟨q, ⟨hq, -⟩, -⟩ := exists_lift_of_strictlyHenselian_of_weaklyEtale f.left g pr hp t ht
  have hqw : q ≫ strHom W = Spec.map (CommRingCat.ofHom (algebraMap K (SeparableClosure K))) := by
    rw [← hfw, ← Category.assoc, hq]
    exact ptLeft_comp_strHom φ
  exact ⟨Over.homMk q hqw, Over.OverMorphism.ext hq⟩

/-- **Geometric points lift along coverings.** Every geometric point of an object of the site
factors through some member of any covering sieve. -/
lemma exists_map_eq_of_mem_topology {V : (base K).ProEt} (S : Sieve V)
    (hS : S ∈ Scheme.ProEt.topology (base K) V) (φ : GeomPt K V) :
    ∃ (W : (base K).ProEt) (f : W ⟶ V), S f ∧ ∃ ψ : GeomPt K W, map f ψ = φ := by
  have : (Scheme.ProEt.precoverage (base K)).IsStableUnderComposition := by
    dsimp [Scheme.ProEt.precoverage]
    infer_instance
  have : (Scheme.ProEt.precoverage (base K)).IsStableUnderBaseChange := by
    dsimp [Scheme.ProEt.precoverage]
    infer_instance
  have : (Scheme.ProEt.precoverage (base K)).HasIsos := by
    dsimp [Scheme.ProEt.precoverage]
    infer_instance
  obtain ⟨R, hR, hRS⟩ :=
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hS
  obtain ⟨E, hER⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hR
  have hE : (E.toPreZeroHypercover.map
      (Scheme.ProEt.forget (base K) ⋙ Over.forget (base K))).presieve₀ ∈
      Scheme.proetalePrecoverage V.left := by
    rw [PreZeroHypercover.presieve₀_map]
    exact E.mem₀
  obtain ⟨hjs, -⟩ := hE.2
  obtain ⟨i, y, hy⟩ := (Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff
    Scheme.forget).1 hjs ((ptLeft φ) (IsLocalRing.closedPoint (SeparableClosure K)))
  obtain ⟨ψ, hψ⟩ := exists_map_eq_of_mem_range (E.f i) φ y hy
  refine ⟨_, E.f i, hRS _ (E.f i) ?_, ψ, hψ⟩
  rw [hER]
  exact Presieve.ofArrows.mk _

end Lifting

end GeomPt

/-! ### The geometric point as an object of the site -/

/-- The separable closure `Kˢᵉᵖ` is a weakly étale `K`-algebra: it is the union of finite
separable subextensions, each étale, so its greatest weakly étale subalgebra is everything. -/
theorem weaklyEtale_separableClosure : Algebra.WeaklyEtale K (SeparableClosure K) := by
  obtain ⟨B, hB, hmax⟩ := exists_greatest_weaklyEtale_subalgebra K (SeparableClosure K)
  obtain rfl : B = ⊤ := by
    rw [eq_top_iff]
    intro c _
    let E : IntermediateField K (SeparableClosure K) := IntermediateField.adjoin K {c}
    have : FiniteDimensional K E :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral c)
    have : Algebra.FormallyEtale K E := Algebra.FormallyEtale.of_isSeparable K E
    have : Algebra.Etale K E :=
      ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
    exact hmax _ (inferInstanceAs (Algebra.WeaklyEtale K E))
      (IntermediateField.subset_adjoin K {c} rfl)
  rcases structure_of_weaklyEtale_over_field.{u, u, u} K (⊤ : Subalgebra K (SeparableClosure K))
    hB with ⟨_, _, _, _, ⟨_, hq⟩, _⟩
  exact hq (SeparableClosure K) ⟨(Subalgebra.topEquiv : _ ≃ₐ[K] _).toAlgHom,
    Subalgebra.topEquiv.surjective⟩

/-- The structure morphism `Spec Kˢᵉᵖ ⟶ Spec K` is weakly étale. -/
instance weaklyEtale_point_hom : WeaklyEtale (point K).hom :=
  (weaklyEtale_specMap_iff (CommRingCat.ofHom (algebraMap K (SeparableClosure K)))).2 (by
    convert weaklyEtale_separableClosure K <;>
      first | rfl | exact Algebra.algebra_ext _ _ fun _ ↦ rfl)

/-- The geometric point `Spec Kˢᵉᵖ` as an object of the small pro-étale site of `Spec K`. -/
def pointObj : (base K).ProEt := Scheme.ProEt.mk (point K).hom

namespace GeomPt

variable {K}

/-- The tautological geometric point of `Spec Kˢᵉᵖ`. -/
def unitPt : GeomPt K (pointObj K) := Over.homMk (𝟙 _) (Category.id_comp _)

/-- A geometric point of `V` as a morphism of the site out of `Spec Kˢᵉᵖ`. -/
def toHom {V : (base K).ProEt} (φ : GeomPt K V) : pointObj K ⟶ V :=
  MorphismProperty.Over.homMk φ.left (Over.w φ)

/-- Every geometric point `φ` is the image of the tautological geometric point under the morphism
`toHom φ`. -/
@[simp]
lemma map_toHom_unitPt {V : (base K).ProEt} (φ : GeomPt K V) : map (toHom φ) unitPt = φ :=
  Over.OverMorphism.ext (Category.id_comp _)

end GeomPt

end AlgebraicGeometry.GaloisSheaf
