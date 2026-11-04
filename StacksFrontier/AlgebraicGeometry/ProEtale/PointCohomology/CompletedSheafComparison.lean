module

public import StacksFrontier.AlgebraicGeometry.ProEtale.PointCohomology.EtaleComparison

/-!
# The completed sheaf is the sheaf of continuous equivariant functions

Let `M` be a topological module with an action of the absolute Galois group `G` of a field `K`,
and let `(Nⱼ)` be a system of open `G`-stable submodules forming a basis of neighbourhoods of
zero, with respect to which `M` is separated and complete. The completed sheaf
`M^∧ = limⱼ ε⁻¹(M/Nⱼ)` on the pro-étale site of `Spec K` is then the sheaf of continuous
equivariant functions on geometric points with values in `M`.

## Main results

* `AlgebraicGeometry.GaloisSheaf.isLimitContCone`: the sheaf of continuous equivariant
  functions is the limit of the discrete sheaves of the quotients `M/Nⱼ`.
* `AlgebraicGeometry.GaloisSheaf.completionIsoContSheaf`: the completed sheaf is the sheaf of
  continuous equivariant functions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology

universe t t' u r w

namespace AlgebraicGeometry.GaloisSheaf

variable {K : Type u} [Field K] {Λ : Type r} [Ring Λ] {M : Type w} [AddCommGroup M] [Module Λ M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul Λ M]
  (ρ : Representation Λ (galoisGroup K) M)

omit [ContinuousConstSMul Λ M] in
/-- Reduction modulo an open submodule is continuous for the discrete topology on the
quotient. -/
lemma continuous_mkQ_of_isOpen (N : Submodule Λ M) (hN : IsOpen (N : Set M)) :
    letI : TopologicalSpace (M ⧸ N) := ⊥
    Continuous N.mkQ := by
  let : TopologicalSpace (M ⧸ N) := ⊥
  have : DiscreteTopology (M ⧸ N) := ⟨rfl⟩
  refine (IsLocallyConstant.iff_continuous _).1 ?_
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro z
  obtain ⟨y, rfl⟩ := N.mkQ_surjective z
  have : (N.mkQ : M → M ⧸ N) ⁻¹' {N.mkQ y} = (fun x ↦ -y + x) ⁻¹' (N : Set M) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq, sub_eq_neg_add]
  rw [this]
  exact hN.preimage (continuous_const.add continuous_id)

variable {J : Type t} [Category.{t'} J] (D : J ⥤ Subrepresentation ρ)
  (hopen : ∀ j, IsOpen ((D.obj j).toSubmodule : Set M))

/-- The reduction of the sheaf of continuous functions to the discrete sheaf of a quotient. -/
def contToDisc (j : J) : contSheaf Λ ρ ⟶ discSheaf (quotientRep ρ (D.obj j)) :=
  letI : TopologicalSpace (M ⧸ (D.obj j).toSubmodule) := ⊥
  haveI : DiscreteTopology (M ⧸ (D.obj j).toSubmodule) := ⟨rfl⟩
  haveI : ContinuousConstSMul Λ (M ⧸ (D.obj j).toSubmodule) :=
    ⟨fun _ ↦ continuous_of_discreteTopology⟩
  contSheafMap (D.obj j).toSubmodule.mkQ (continuous_mkQ_of_isOpen _ (hopen j)) (fun _ _ ↦ rfl)

/-- The cone of reductions of the sheaf of continuous functions. -/
def contCone : Cone (D ⋙ quotientDiagram ρ ⋙ discSheafFunctor.{u, r, w} Λ) where
  pt := contSheaf Λ ρ
  π :=
    { app j := contToDisc ρ D hopen j
      naturality j j' f := by
        ext V a
        rfl }

variable (hbasis : ∀ U ∈ 𝓝 (0 : M), ∃ j, ((D.obj j).toSubmodule : Set M) ⊆ U)
  (hsep : ∀ m : M, (∀ j, m ∈ (D.obj j).toSubmodule) → m = 0)
  (hcomp : ∀ x : ∀ j, M ⧸ (D.obj j).toSubmodule,
    (∀ j j' (f : j ⟶ j'), (D.obj j).toSubmodule.mapQ (D.obj j').toSubmodule LinearMap.id
      (leOfHom (D.map f)) (x j) = x j') →
    ∃ m : M, ∀ j, (D.obj j).toSubmodule.mkQ m = x j)

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul Λ M] in
include hsep in
/-- Elements of `M` with the same reductions modulo all the `Nⱼ` are equal. -/
lemma eq_of_mkQ_eq {m m' : M}
    (h : ∀ j, (D.obj j).toSubmodule.mkQ m = (D.obj j).toSubmodule.mkQ m') :
    m = m' := by
  rw [← sub_eq_zero]
  exact hsep _ fun j ↦ (Submodule.Quotient.eq _).1 (h j)

omit [ContinuousConstSMul Λ M] in
include hbasis in
/-- A function into `M` whose reductions modulo all the `Nⱼ` are locally constant is
continuous. -/
lemma continuous_of_isLocallyConstant_mkQ {X : Type*} [TopologicalSpace X] (g : X → M)
    (hg : ∀ j, IsLocallyConstant ((D.obj j).toSubmodule.mkQ ∘ g)) : Continuous g := by
  rw [continuous_iff_continuousAt]
  intro x U hU
  have h0 : (fun y ↦ y + g x) ⁻¹' U ∈ 𝓝 (0 : M) :=
    (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨j, hj⟩ := hbasis _ h0
  have hV : {x' | (D.obj j).toSubmodule.mkQ (g x') = (D.obj j).toSubmodule.mkQ (g x)} ∈ 𝓝 x :=
    ((hg j).isOpen_fiber _).mem_nhds rfl
  refine Filter.mem_map.2 (Filter.mem_of_superset hV fun x' hx' ↦ ?_)
  have hx'' : g x' - g x ∈ (D.obj j).toSubmodule := (Submodule.Quotient.eq _).1 hx'
  simpa using hj hx''

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul Λ M] in
variable {ρ D hopen} in
include hcomp in
/-- A family of functions into the quotients `M/Nⱼ`, compatible under the transition maps, is the
family of reductions of a single function into `M`. -/
lemma exists_glue {X : Type*} (y : ∀ j, X → M ⧸ (D.obj j).toSubmodule)
    (hy : ∀ j j' (f : j ⟶ j') x, (D.obj j).toSubmodule.mapQ (D.obj j').toSubmodule
      LinearMap.id (leOfHom (D.map f)) (y j x) = y j' x) :
    ∃ g : X → M, ∀ j x, (D.obj j).toSubmodule.mkQ (g x) = y j x := by
  choose g hg using fun x ↦ hcomp (fun j ↦ y j x) fun j j' f ↦ hy j j' f x
  exact ⟨g, fun j x ↦ hg x j⟩

include hbasis hsep hcomp in
/-- **The sheaf of continuous equivariant functions is the limit of the discrete sheaves of the
quotients `M/Nⱼ`.** -/
def isLimitContCone : IsLimit (contCone ρ D hopen) := by
  apply isLimitOfReflects (sheafToPresheaf (Scheme.ProEt.topology (base K))
    (ModuleCat.{max (u + 1) r w} Λ))
  apply evaluationJointlyReflectsLimits
  intro V
  let F : J ⥤ ModuleCat.{max (u + 1) r w} Λ := ((D ⋙ quotientDiagram ρ ⋙ discSheafFunctor Λ) ⋙
      sheafToPresheaf (Scheme.ProEt.topology (base K)) (ModuleCat.{max (u + 1) r w} Λ)) ⋙
        (evaluation (base K).ProEtᵒᵖ (ModuleCat.{max (u + 1) r w} Λ)).obj V
  let y : ∀ (s : Cone F) (x : s.pt) (j : J), GeomPt K V.unop → M ⧸ (D.obj j).toSubmodule :=
    fun s x j ↦ ((s.π.app j).hom x).down.1
  have hy : ∀ (s : Cone F) x j j'
      (f : j ⟶ j') φ, (D.obj j).toSubmodule.mapQ (D.obj j').toSubmodule LinearMap.id
        (leOfHom (D.map f)) (y s x j φ) = y s x j' φ := by
    intro s x j j' f φ
    exact congrArg (fun a ↦ a.down.1 φ) (congrArg (fun g ↦ g.hom x) (s.w f))
  have key : ∀ (s : Cone F) (x : s.pt),
      ∃ g : GeomPt K V.unop → M, ∀ j φ, (D.obj j).toSubmodule.mkQ (g φ) = y s x j φ :=
    fun s x ↦ exists_glue hcomp (y s x) (hy s x)
  choose G hG using key
  have hGmem : ∀ s x, G s x ∈ contSections Λ ρ V.unop := by
    intro s x
    refine ⟨fun g φ ↦ eq_of_mkQ_eq ρ D hsep fun j ↦ ?_, fun A a hA ↦ ?_⟩
    · rw [hG]
      have heqv : y s x j (g • φ) = ((quotientDiagram ρ).obj (D.obj j)).ρ g (y s x j φ) :=
        ((s.π.app j).hom x).down.2.1 g φ
      rw [heqv, ← hG s x j φ]
      rfl
    · refine continuous_of_isLocallyConstant_mkQ ρ D hbasis _ fun j ↦ ?_
      have h1 : (D.obj j).toSubmodule.mkQ ∘ (G s x ∘ GeomPt.map a) =
          y s x j ∘ GeomPt.map a := funext fun φ ↦ hG s x j _
      rw [h1]
      let : TopologicalSpace (M ⧸ (D.obj j).toSubmodule) := ⊥
      have : DiscreteTopology (M ⧸ (D.obj j).toSubmodule) := ⟨rfl⟩
      exact (IsLocallyConstant.iff_continuous _).2 (((s.π.app j).hom x).down.2.2 A a hA)
  let lift : ∀ s : Cone F, s.pt ⟶ (contSheaf Λ ρ).val.obj V := fun s ↦ ModuleCat.ofHom
    { toFun x := ⟨⟨G s x, hGmem s x⟩⟩
      map_add' x x' := by
        apply ULift.ext
        apply Subtype.ext
        funext φ
        refine eq_of_mkQ_eq ρ D hsep fun j ↦ ?_
        change _ = (D.obj j).toSubmodule.mkQ (G s x φ + G s x' φ)
        rw [map_add, hG, hG, hG]
        simp only [y, map_add]
        rfl
      map_smul' c x := by
        apply ULift.ext
        apply Subtype.ext
        funext φ
        refine eq_of_mkQ_eq ρ D hsep fun j ↦ ?_
        change _ = (D.obj j).toSubmodule.mkQ (c • G s x φ)
        rw [map_smul, hG, hG]
        change y s (c • x) j φ = c • y s x j φ
        simp only [y, map_smul]
        rfl }
  refine { lift := lift, fac := ?_, uniq := ?_ }
  · intro s j
    ext x
    apply ULift.ext
    apply Subtype.ext
    funext φ
    exact hG s x j φ
  · intro s m hm
    ext x
    apply ULift.ext
    apply Subtype.ext
    funext φ
    refine eq_of_mkQ_eq ρ D hsep fun j ↦ ?_
    change _ = (D.obj j).toSubmodule.mkQ (G s x φ)
    rw [hG]
    exact congrArg (fun a ↦ a.down.1 φ) (congrArg (fun g ↦ g.hom x) (hm j))

include hbasis hsep hcomp in
/-- **The completed sheaf `limⱼ ε⁻¹(M/Nⱼ)` is the sheaf of continuous equivariant functions on
geometric points with values in `M`.** -/
def completionIsoContSheaf [Small.{max (u + 1) r w} J] :
    completion.{t, t', u, r, w} ρ D ≅ contSheaf Λ ρ :=
  IsLimit.conePointUniqueUpToIso (completionIsLimit ρ D)
    ((IsLimit.postcomposeInvEquiv (Functor.isoWhiskerLeft (D ⋙ quotientDiagram ρ)
      (proetaleSheafIsoDisc Λ)) (contCone ρ D hopen)).symm
      (isLimitContCone ρ D hopen hbasis hsep hcomp))

end AlgebraicGeometry.GaloisSheaf
