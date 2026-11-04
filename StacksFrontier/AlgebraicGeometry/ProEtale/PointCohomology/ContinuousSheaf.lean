module

public import StacksFrontier.AlgebraicGeometry.ProEtale.FilteredColimitsOfProetaleCohomology
public import StacksFrontier.AlgebraicGeometry.ProEtale.PointCohomology.GeometricPoints

/-!
# The sheaf of continuous equivariant functions on geometric points

Let `K` be a field with absolute Galois group `G` and let `Y` be a topological module with a
`G`-action. For an object `V` of the small pro-étale site of `Spec K` consider the
`G`-equivariant functions `f` from the geometric points of `V` to `Y` which are continuous on
the geometric points of every affine object over `V`. These form a sheaf of modules on the site.

On an affine object the sections are exactly the continuous equivariant functions, the
geometric points of an affine object being a profinite space. The sheaf condition comes from two
facts: geometric points lift along coverings, and a function on the geometric points of an
affine object is continuous as soon as it is continuous on the geometric points of a finite
affine covering, which is a quotient map of compact Hausdorff spaces.

## Main definitions

* `AlgebraicGeometry.GaloisSheaf.contSections`: the module of sections over an object.
* `AlgebraicGeometry.GaloisSheaf.contSheaf`: the sheaf of continuous equivariant functions.

## Main results

* `AlgebraicGeometry.GaloisSheaf.mem_contSections_iff_of_isAffine`: on an affine object the
  sections are the continuous equivariant functions.
* `AlgebraicGeometry.GaloisSheaf.GeomPt.continuous_of_finite_cover`: continuity descends along a
  finite affine covering.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology

universe u r w

namespace AlgebraicGeometry.GaloisSheaf

variable {K : Type u} [Field K]

namespace GeomPt

/-- **Continuity descends along a finite affine covering.** If the geometric points of the
members of a finite family of affine objects over an affine object `A` cover those of `A`, a
function on the geometric points of `A` whose pullbacks to the members are continuous is
continuous. -/
lemma continuous_of_finite_cover {A : (base K).ProEt} [IsAffine A.left] {ι : Type*} [Finite ι]
    (B : ι → (base K).ProEt) [∀ i, IsAffine (B i).left] (b : ∀ i, B i ⟶ A)
    (hsurj : ∀ φ : GeomPt K A, ∃ i ψ, map (b i) ψ = φ) {Z : Type*} [TopologicalSpace Z]
    (F : GeomPt K A → Z) (hF : ∀ i, Continuous (F ∘ map (b i))) : Continuous F := by
  let σ : (Σ i, GeomPt K (B i)) → GeomPt K A := fun p ↦ map (b p.1) p.2
  have hσ : Continuous σ := continuous_sigma fun i ↦ continuous_map (b i)
  exact (hσ.isClosedMap.isQuotientMap hσ fun φ ↦
    let ⟨i, ψ, h⟩ := hsurj φ; ⟨⟨i, ψ⟩, h⟩).continuous_iff.2 (continuous_sigma hF)

/-- Geometric points lift along a finite affine refinement of a covering of an affine object. -/
lemma exists_finite_affine_cover {A : (base K).ProEt} [IsAffine A.left] (S : Sieve A)
    (hS : S ∈ Scheme.ProEt.topology (base K) A) :
    ∃ E : PreZeroHypercover.{u + 1} A, Finite E.I₀ ∧ (∀ i, IsAffine (E.X i).left) ∧
      E.sieve₀ ≤ S ∧ ∀ φ : GeomPt K A, ∃ i ψ, map (E.f i) ψ = φ := by
  obtain ⟨E, hfin, hcov, hle, haff⟩ := ProEtale.exists_finite_affine_covering_le A S hS
  refine ⟨E, hfin, haff, hle, fun φ ↦ ?_⟩
  obtain ⟨W, g, hg, ψ, hψ⟩ := exists_map_eq_of_mem_topology E.sieve₀
    (Precoverage.generate_mem_toGrothendieck hcov) φ
  obtain ⟨Y, h, f, ⟨i⟩, rfl⟩ := hg
  exact ⟨i, map h ψ, by rwa [← map_comp]⟩

end GeomPt

variable (Λ : Type r) [Ring Λ] {Y : Type w} [AddCommGroup Y] [Module Λ Y] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y] [ContinuousConstSMul Λ Y]
  (ρ : Representation Λ (galoisGroup K) Y)

/-- The sections over `V` of the sheaf of continuous equivariant functions: the equivariant
functions on the geometric points of `V` which are continuous on the geometric points of every
affine object over `V`. -/
def contSections (V : (base K).ProEt) : Submodule Λ (GeomPt K V → Y) where
  carrier := {f | (∀ (g : galoisGroup K) φ, f (g • φ) = ρ g (f φ)) ∧
    ∀ (A : (base K).ProEt) (a : A ⟶ V), IsAffine A.left → Continuous (f ∘ GeomPt.map a)}
  zero_mem' := ⟨fun g φ ↦ by simp, fun A a _ ↦ continuous_const⟩
  add_mem' {f f'} hf hf' := ⟨fun g φ ↦ by simp [hf.1 g φ, hf'.1 g φ],
    fun A a hA ↦ (hf.2 A a hA).add (hf'.2 A a hA)⟩
  smul_mem' c f hf := ⟨fun g φ ↦ by simp [hf.1 g φ],
    fun A a hA ↦ (hf.2 A a hA).const_smul c⟩

variable {Λ ρ} in
/-- Sections are stable under composition with the map of geometric points induced by a morphism
`W ⟶ V`. -/
lemma mem_contSections_comp {V W : (base K).ProEt} (h : W ⟶ V) {f : GeomPt K V → Y}
    (hf : f ∈ contSections Λ ρ V) : f ∘ GeomPt.map h ∈ contSections Λ ρ W :=
  ⟨fun g φ ↦ by simp [GeomPt.map_smul, hf.1 g],
    fun A a hA ↦ by
      convert hf.2 A (a ≫ h) hA using 1
      funext φ
      simp [GeomPt.map_comp]⟩

variable {Λ ρ} in
/-- On an affine object the sections are the continuous equivariant functions. -/
lemma mem_contSections_iff_of_isAffine {V : (base K).ProEt} [IsAffine V.left]
    (f : GeomPt K V → Y) :
    f ∈ contSections Λ ρ V ↔ (∀ (g : galoisGroup K) φ, f (g • φ) = ρ g (f φ)) ∧ Continuous f :=
  ⟨fun hf ↦ ⟨hf.1, by
      have := hf.2 V (𝟙 V) ‹_›
      rwa [show f ∘ GeomPt.map (𝟙 V) = f from funext fun φ ↦ by simp] at this⟩,
    fun hf ↦ ⟨hf.1, fun A a _ ↦ hf.2.comp (GeomPt.continuous_map a)⟩⟩

/-- The presheaf of continuous equivariant functions on geometric points. -/
def contPresheaf : (base K).ProEtᵒᵖ ⥤ ModuleCat.{max (u + 1) r w} Λ where
  obj V := ModuleCat.of Λ (ULift.{max (u + 1) r} (contSections Λ ρ V.unop))
  map {V W} h := ModuleCat.ofHom
    { toFun a := ⟨⟨a.down.1 ∘ GeomPt.map h.unop, mem_contSections_comp h.unop a.down.2⟩⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_id V := by
    ext a φ
    simp
  map_comp f g := by
    ext a φ
    simp [GeomPt.map_comp]

/-- The restriction map of `contPresheaf` along `h` is composition with the induced map of
geometric points. -/
lemma contPresheaf_map_apply {V W : (base K).ProEtᵒᵖ} (h : V ⟶ W)
    (a : (contPresheaf Λ ρ).obj V) (φ : GeomPt K W.unop) :
    ((contPresheaf Λ ρ).map h a).down.1 φ = a.down.1 (GeomPt.map h.unop φ) := rfl

/-- **The presheaf of continuous equivariant functions is a sheaf.** -/
theorem isSheaf_contPresheaf :
    Presheaf.IsSheaf (Scheme.ProEt.topology (base K)) (contPresheaf Λ ρ) := by
  refine Presheaf.isSheaf_of_isSheaf_comp (Scheme.ProEt.topology (base K)) (contPresheaf Λ ρ)
    (forget₂ (ModuleCat.{max (u + 1) r w} Λ) AddCommGrpCat.{max (u + 1) r w}) ?_
  refine Presheaf.isSheaf_of_isSheaf_comp (Scheme.ProEt.topology (base K)) _
    (forget AddCommGrpCat.{max (u + 1) r w}) ?_
  rw [isSheaf_iff_isSheaf_of_type]
  intro V S hS x hx
  -- values of the family at geometric points do not depend on the chosen lift
  have key : ∀ {W₁ W₂ : (base K).ProEt} (f₁ : W₁ ⟶ V) (f₂ : W₂ ⟶ V) (h₁ : S f₁) (h₂ : S f₂)
      (ψ₁ : GeomPt K W₁) (ψ₂ : GeomPt K W₂), GeomPt.map f₁ ψ₁ = GeomPt.map f₂ ψ₂ →
        (x f₁ h₁).down.1 ψ₁ = (x f₂ h₂).down.1 ψ₂ := by
    intro W₁ W₂ f₁ f₂ h₁ h₂ ψ₁ ψ₂ heq
    simpa [contPresheaf_map_apply] using
      congrArg (fun a : (contPresheaf Λ ρ).obj (op (pointObj K)) ↦ a.down.1 GeomPt.unitPt)
        (hx (GeomPt.toHom ψ₁) (GeomPt.toHom ψ₂) h₁ h₂
          (MorphismProperty.Over.Hom.ext (congrArg CommaMorphism.left heq)))
  choose W f hf ψ hψ using fun φ ↦ GeomPt.exists_map_eq_of_mem_topology S hS φ
  let t : GeomPt K V → Y := fun φ ↦ (x (f φ) (hf φ)).down.1 (ψ φ)
  have ht : ∀ {W' : (base K).ProEt} (f' : W' ⟶ V) (h' : S f') (ψ' : GeomPt K W'),
      t (GeomPt.map f' ψ') = (x f' h').down.1 ψ' := fun f' h' ψ' ↦
    key _ _ _ _ _ _ (hψ _)
  have htmem : t ∈ contSections Λ ρ V := by
    refine ⟨fun g φ ↦ ?_, fun A a _ ↦ ?_⟩
    · have h1 : t (g • φ) = (x (f φ) (hf φ)).down.1 (g • ψ φ) := by
        rw [← ht (f φ) (hf φ) (g • ψ φ), GeomPt.map_smul, hψ]
      rw [h1, (x (f φ) (hf φ)).down.2.1 g (ψ φ)]
    · obtain ⟨E, hfin, haff, hle, hsurj⟩ :=
        GeomPt.exists_finite_affine_cover (S.pullback a)
          (GrothendieckTopology.pullback_stable _ a hS)
      refine GeomPt.continuous_of_finite_cover E.X E.f hsurj _ fun i ↦ ?_
      have hi : S (E.f i ≫ a) := hle _ ⟨_, 𝟙 _, E.f i, ⟨i⟩, Category.id_comp _⟩
      have heq : (t ∘ GeomPt.map a) ∘ GeomPt.map (E.f i) = (x _ hi).down.1 :=
        funext fun ψ' ↦ by simpa only [Function.comp_apply, ← GeomPt.map_comp] using ht _ hi ψ'
      rw [heq]
      exact ((mem_contSections_iff_of_isAffine _).1 (x _ hi).down.2).2
  refine ⟨⟨⟨t, htmem⟩⟩, fun W' f' h' ↦ ?_, fun t' ht' ↦ ?_⟩
  · exact ULift.ext _ _ (Subtype.ext (funext (ht f' h')))
  · refine ULift.ext _ _ (Subtype.ext (funext fun φ ↦ ?_))
    simpa [contPresheaf_map_apply, hψ] using
      congrArg (fun a : (contPresheaf Λ ρ).obj (op (W φ)) ↦ a.down.1 (ψ φ)) (ht' (f φ) (hf φ))

/-- **The sheaf of continuous equivariant functions on geometric points.** -/
def contSheaf : Sheaf (Scheme.ProEt.topology (base K)) (ModuleCat.{max (u + 1) r w} Λ) :=
  ⟨contPresheaf Λ ρ, isSheaf_contPresheaf Λ ρ⟩

section Functoriality

variable {Λ ρ} {Y' : Type w} [AddCommGroup Y'] [Module Λ Y'] [TopologicalSpace Y']
  [IsTopologicalAddGroup Y'] [ContinuousConstSMul Λ Y']
  {ρ' : Representation Λ (galoisGroup K) Y'}

/-- The map of presheaves induced by a continuous equivariant linear map of coefficients. -/
def contPresheafMap (φ : Y →ₗ[Λ] Y') (hφ : Continuous φ)
    (heq : ∀ (g : galoisGroup K) y, φ (ρ g y) = ρ' g (φ y)) :
    contPresheaf Λ ρ ⟶ contPresheaf Λ ρ' where
  app V := ModuleCat.ofHom
    { toFun a := ⟨⟨φ ∘ a.down.1, fun g ψ ↦ by simp [a.down.2.1 g ψ, heq],
        fun A f hA ↦ hφ.comp (a.down.2.2 A f hA)⟩⟩
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
  naturality _ _ _ := rfl

variable (ρ) in
/-- The identity map of coefficients induces the identity map of presheaves. -/
lemma contPresheafMap_id :
    contPresheafMap (ρ := ρ) LinearMap.id continuous_id (fun _ _ ↦ rfl) = 𝟙 _ := rfl

/-- The map of presheaves induced by a composite of coefficient maps is the composite of the
induced maps. -/
lemma contPresheafMap_comp {Y'' : Type w} [AddCommGroup Y''] [Module Λ Y'']
    [TopologicalSpace Y''] [IsTopologicalAddGroup Y''] [ContinuousConstSMul Λ Y'']
    {ρ'' : Representation Λ (galoisGroup K) Y''} (φ : Y →ₗ[Λ] Y') (hφ : Continuous φ)
    (heq : ∀ (g : galoisGroup K) y, φ (ρ g y) = ρ' g (φ y)) (φ' : Y' →ₗ[Λ] Y'')
    (hφ' : Continuous φ') (heq' : ∀ (g : galoisGroup K) y, φ' (ρ' g y) = ρ'' g (φ' y)) :
    contPresheafMap (φ' ∘ₗ φ) (hφ'.comp hφ) (fun g y ↦ by simp [heq, heq']) =
      contPresheafMap φ hφ heq ≫ contPresheafMap φ' hφ' heq' := rfl

/-- The map of sheaves induced by a continuous equivariant linear map of coefficients. -/
def contSheafMap (φ : Y →ₗ[Λ] Y') (hφ : Continuous φ)
    (heq : ∀ (g : galoisGroup K) y, φ (ρ g y) = ρ' g (φ y)) :
    contSheaf Λ ρ ⟶ contSheaf Λ ρ' :=
  ⟨contPresheafMap φ hφ heq⟩

end Functoriality

end AlgebraicGeometry.GaloisSheaf
