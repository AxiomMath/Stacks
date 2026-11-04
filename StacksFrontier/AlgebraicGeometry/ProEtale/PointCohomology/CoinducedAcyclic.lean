module

public import StacksFrontier.AlgebraicGeometry.ProEtale.PointCohomology.CoinducedSections
public import StacksFrontier.AlgebraicGeometry.ProEtale.PointCohomology.FibreProductPoints
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingAlongAFunctorEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import StacksFrontier.Topology.Profinite.CechExactness

/-!
# The sheaf of a coinduced module is acyclic

Let `X` be a topological representation of the absolute Galois group `G` of a field `K`, with
jointly continuous action, which is complete and separated with respect to a basis of open
subgroups. The sheaf on the pro-étale site of `Spec K` of continuous equivariant functions with
values in the coinduced module `C(G, X)` has no higher cohomology.

The proof is Cartan's criterion (Stacks 03F9) for the affine objects and their finite affine
coverings. By Frobenius reciprocity the sections of the sheaf over an affine object are the
continuous `X`-valued functions on its geometric points, the action being used up; the
geometric points of the fibre products of a covering are the compatible families of geometric
points; so the Čech complex of a finite affine covering `{Vₖ ⟶ U}` is the complex of continuous
`X`-valued functions on the Čech nerve of the continuous surjection `∐ₖ Vₖ(Kˢᵉᵖ) ⟶ U(Kˢᵉᵖ)` of
profinite spaces, which is exact in positive degrees.

## Main results

* `AlgebraicGeometry.GaloisSheaf.cechCosimplicialIso`: the Čech complex of a finite affine
  covering is the Čech complex of continuous functions on geometric points.
* `AlgebraicGeometry.GaloisSheaf.isZero_cechCohomology_coind`: its positive-degree Čech
  cohomology vanishes.
* `AlgebraicGeometry.GaloisSheaf.isZero_rightDerived_coindAbSheaf`: the sheaf of a coinduced
  module has no higher cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology ContinuousMap
open Stacks.ProfiniteCech

universe u r w

namespace AlgebraicGeometry.GaloisSheaf

variable {K : Type u} [Field K]

section Nerve

variable {U : (base K).ProEt} (E : PreZeroHypercover.{u} U)

/-- The geometric points of the members of a covering family, mapped to those of the base. -/
def coverPointMap : C((Σ k : E.I₀, GeomPt K (E.X k)), GeomPt K U) :=
  ⟨fun x ↦ GeomPt.map (E.f x.1) x.2, continuous_sigma fun k ↦
    show Continuous (GeomPt.map (E.f k)) from GeomPt.continuous_map _⟩

/-- The map on geometric points sends a point of a member to its image in the base. -/
lemma coverPointMap_apply (x : Σ k : E.I₀, GeomPt K (E.X k)) :
    coverPointMap E x = GeomPt.map (E.f x.1) x.2 := rfl

/-- The geometric points of a covering family map onto those of the base. -/
lemma coverPointMap_surjective (hE : E.sieve₀ ∈ Scheme.ProEt.topology (base K) U) :
    Function.Surjective (coverPointMap E) := by
  intro φ
  obtain ⟨W, g, ⟨Y, h, f, ⟨k⟩, rfl⟩, ψ, hψ⟩ := GeomPt.exists_map_eq_of_mem_topology _ hE φ
  exact ⟨⟨k, GeomPt.map h ψ⟩, by rw [← hψ, coverPointMap, ContinuousMap.coe_mk,
    ← GeomPt.map_comp]⟩

/-- A point of the Čech nerve as a tuple of indices together with a compatible family. -/
def nervePointEquiv (n : ℕ) : FibrePower (coverPointMap E) n ≃
    Σ i : Fin (n + 1) → E.I₀, GeomPt.Compatible (fun a ↦ E.f (i a)) where
  toFun x := ⟨fun a ↦ (x.1 a).1, ⟨fun a ↦ (x.1 a).2, fun a b ↦ by
    simpa only [coverPointMap_apply] using x.2 a b⟩⟩
  invFun y := ⟨fun a ↦ ⟨y.1 a, y.2.1 a⟩, fun a b ↦ by
    simpa only [coverPointMap_apply] using y.2.2 a b⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Nerve

section Topology

variable {U : (base K).ProEt} [IsAffine U.left] {ι : Type*} {A : ι → (base K).ProEt}
  [∀ a, IsAffine (A a).left] (f : ∀ a, A a ⟶ U)

/-- The space of compatible families of geometric points over affine objects is compact. -/
instance : CompactSpace (GeomPt.Compatible f) := by
  refine isCompact_iff_compactSpace.mp (IsClosed.isCompact (s := {ψ : ∀ a, GeomPt K (A a) |
    ∀ a b, GeomPt.map (f a) (ψ a) = GeomPt.map (f b) (ψ b)}) ?_)
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun a ↦ isClosed_iInter fun b ↦ isClosed_eq
    ((GeomPt.continuous_map _).comp (continuous_apply a))
    ((GeomPt.continuous_map _).comp (continuous_apply b))

end Topology

section NerveHomeo

variable {U : (base K).ProEt} [IsAffine U.left] (E : PreZeroHypercover.{u} U)
  [Finite E.I₀] [∀ k, IsAffine (E.X k).left]

/-- The disjoint union of the geometric points of a finite affine covering is compact. -/
instance : CompactSpace (Σ k : E.I₀, GeomPt K (E.X k)) := inferInstance

/-- The Čech nerve of a finite affine covering, as a disjoint union of spaces of compatible
families. -/
def nervePointHomeo (n : ℕ) : FibrePower (coverPointMap E) n ≃ₜ
    Σ i : Fin (n + 1) → E.I₀, GeomPt.Compatible (fun a ↦ E.f (i a)) :=
  (Continuous.homeoOfEquivCompactToT2 (f := (nervePointEquiv E n).symm) (by
    refine continuous_sigma fun i ↦ ?_
    refine Continuous.subtype_mk (continuous_pi fun a ↦ ?_) _
    exact continuous_sigmaMk.comp ((continuous_apply a).comp continuous_subtype_val))).symm

/-- The homeomorphism `nervePointHomeo` is given by `nervePointEquiv`. -/
lemma nervePointHomeo_apply (n : ℕ) (x : FibrePower (coverPointMap E) n) :
    nervePointHomeo E n x = nervePointEquiv E n x := rfl

end NerveHomeo

/-! ### The Čech complex of the coinduced sheaf -/

section Cech

variable {Λ : Type r} [Ring Λ] [TopologicalSpace Λ] (X : TopRep.{max u w} Λ (galoisGroup K))
  (hX : Continuous fun p : galoisGroup K × X ↦ X.ρ p.1 p.2)

/-- The abelian presheaf underlying the sheaf of the coinduced module. -/
abbrev coindPresheaf : (base K).ProEtᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) r w} :=
  contPresheaf.{u, r, max u w} Λ (coindRep X) ⋙
    forget₂ (ModuleCat.{max (u + 1) r w} Λ) AddCommGrpCat.{max (u + 1) r w}

variable {U : (base K).ProEt} [IsAffine U.left] (E : PreZeroHypercover.{u} U)
  [Finite E.I₀] [∀ k, IsAffine (E.X k).left]
  [hprod : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct fun a ↦ Over.mk (E.f (i a))]

/-- The fibre products of the members of a finite affine covering are affine. -/
instance (n : ℕ) (i : Fin (n + 1) → E.I₀) :
    IsAffine (∏ᶜ fun a ↦ Over.mk (E.f (i a))).left.left :=
  isAffine_left_piObj ‹_› E (fun k ↦ ‹∀ k, IsAffine (E.X k).left› k) n i

/-- The factor of the Čech cochains of the coinduced sheaf at a tuple of indices. -/
abbrev cechFactor {n : ℕ} (i : Fin (n + 1) → E.I₀) : AddCommGrpCat.{max (u + 1) r w} :=
  (coindPresheaf X).obj (op (∏ᶜ fun a ↦ Over.mk (E.f (i a))).left)

/-- The Čech cochains of the coinduced sheaf in degree `n`. -/
abbrev cechTerm (n : ℕ) : AddCommGrpCat.{max (u + 1) r w} :=
  ∏ᶜ fun i : Fin (n + 1) → E.I₀ ↦ cechFactor X E i

/-- Frobenius reciprocity at a factor of the Čech cochains. -/
def cechFactorEquiv {n : ℕ} (i : Fin (n + 1) → E.I₀) :
    ToType (cechFactor X E i) ≃+ C(GeomPt K (∏ᶜ fun a ↦ Over.mk (E.f (i a))).left, X) :=
  AddEquiv.ulift.trans (coindSectionsEquiv hX _)

/-- A Čech cochain of the coinduced sheaf, read as a function on the Čech nerve of geometric
points. -/
def cechCochainFun {n : ℕ} (x : ToType (cechTerm X E n))
    (z : Σ i : Fin (n + 1) → E.I₀, GeomPt.Compatible (fun a ↦ E.f (i a))) : X :=
  cechFactorEquiv X hX E z.1 ((Pi.π (cechFactor X E) z.1).hom x)
    ((GeomPt.prodHomeomorph (fun a ↦ E.f (z.1 a))).symm z.2)

omit [Finite E.I₀] in
/-- A Čech cochain, read as a function on the Čech nerve of geometric points, is continuous. -/
lemma continuous_cechCochainFun {n : ℕ} (x : ToType (cechTerm X E n)) :
    Continuous (cechCochainFun X hX E x) :=
  continuous_sigma fun i ↦
    (cechFactorEquiv X hX E i ((Pi.π (cechFactor X E) i).hom x)).continuous.comp
      (GeomPt.prodHomeomorph (fun a ↦ E.f (i a))).symm.continuous

/-- **The Čech cochains of the coinduced sheaf** in degree `n` are the continuous functions on the
Čech nerve of the geometric points of the covering. -/
def cechCochainsEquiv (n : ℕ) :
    ToType (cechTerm X E n) ≃+ ULift.{max (u + 1) r} C(FibrePower (coverPointMap E) n, X) where
  toFun x := ⟨⟨cechCochainFun X hX E x ∘ nervePointHomeo E n,
    (continuous_cechCochainFun X hX E x).comp (nervePointHomeo E n).continuous⟩⟩
  invFun c := (Concrete.productEquiv (cechFactor X E (n := n))).symm fun i ↦
    (cechFactorEquiv X hX E i).symm ⟨fun ψ ↦ c.down ((nervePointHomeo E n).symm
      ⟨i, GeomPt.prodHomeomorph (fun a ↦ E.f (i a)) ψ⟩),
      c.down.continuous.comp ((nervePointHomeo E n).symm.continuous.comp
        (continuous_sigmaMk.comp (GeomPt.prodHomeomorph (fun a ↦ E.f (i a))).continuous))⟩
  left_inv x := by
    apply (Concrete.productEquiv (cechFactor X E (n := n))).injective
    funext i
    dsimp only
    rw [Concrete.productEquiv_apply_apply, Concrete.productEquiv_apply_apply,
      Concrete.productEquiv_symm_apply_π]
    apply (cechFactorEquiv X hX E i).injective
    rw [AddEquiv.apply_symm_apply]
    ext ψ
    change cechCochainFun X hX E x (nervePointHomeo E n ((nervePointHomeo E n).symm
      ⟨i, GeomPt.prodHomeomorph (fun a ↦ E.f (i a)) ψ⟩)) = _
    rw [Homeomorph.apply_symm_apply, cechCochainFun, Homeomorph.symm_apply_apply]
  right_inv c := by
    apply ULift.ext
    ext z
    simp only [ContinuousMap.coe_mk, Function.comp_apply, cechCochainFun,
      Concrete.productEquiv_symm_apply_π, AddEquiv.apply_symm_apply, Homeomorph.apply_symm_apply]
    exact congrArg c.down ((nervePointHomeo E n).symm_apply_apply z)
  map_add' x y := by
    apply ULift.ext
    ext z
    simp [cechCochainFun]

omit [Finite E.I₀] in
/-- Frobenius reciprocity at the factors is compatible with the maps between fibre products. -/
lemma cechFactorEquiv_map {m n : ℕ} (i : Fin (n + 1) → E.I₀) (θ : Fin (m + 1) → Fin (n + 1))
    (x : ToType (cechFactor X E (i ∘ θ))) (ψ : GeomPt K (∏ᶜ fun a ↦ Over.mk (E.f (i a))).left) :
    cechFactorEquiv X hX E i (((coindPresheaf X).map
        (Pi.lift fun a ↦ Pi.π (fun b ↦ Over.mk (E.f (i b))) (θ a)).left.op).hom x) ψ =
      cechFactorEquiv X hX E (i ∘ θ) x (GeomPt.map (Pi.lift fun a ↦
        Pi.π (fun b ↦ Over.mk (E.f (i b))) (θ a)).left ψ) := rfl

omit [Finite E.I₀] in
/-- The map of geometric points induced by a reindexing of a fibre product, in terms of
compatible families. -/
lemma map_prodHomeomorph_symm {m n : ℕ} (i : Fin (n + 1) → E.I₀) (θ : Fin (m + 1) → Fin (n + 1))
    (c : GeomPt.Compatible fun a ↦ E.f (i a)) :
    GeomPt.map (Pi.lift fun a ↦ Pi.π (fun b ↦ Over.mk (E.f (i b))) (θ a)).left
        ((GeomPt.prodHomeomorph fun a ↦ E.f (i a)).symm c) =
      (GeomPt.prodHomeomorph fun a ↦ E.f (i (θ a))).symm
        ⟨fun a ↦ c.1 (θ a), fun _ _ ↦ c.2 _ _⟩ := by
  apply (GeomPt.prodHomeomorph fun a ↦ E.f (i (θ a))).injective
  rw [Homeomorph.apply_symm_apply]
  apply Subtype.ext
  funext a
  refine (GeomPt.prodComponents_reindex (fun b ↦ E.f (i b)) θ
    ((GeomPt.prodHomeomorph fun a ↦ E.f (i a)).symm c) a).trans ?_
  change ((GeomPt.prodHomeomorph fun a ↦ E.f (i a))
    ((GeomPt.prodHomeomorph fun a ↦ E.f (i a)).symm c)).1 (θ a) = _
  rw [Homeomorph.apply_symm_apply]

/-- The Čech cosimplicial abelian group of the coinduced sheaf along a finite affine covering. -/
abbrev cechCosimplicial : CosimplicialObject AddCommGrpCat.{max (u + 1) r w} :=
  (Stacks.CechSite.cechSimplicialObject E).rightOp ⋙
    (FormalCoproduct.evalOp _ _).obj ((Over.forget U).op ⋙ coindPresheaf X)

omit [IsAffine U.left] [Finite E.I₀] [∀ (k : E.I₀), IsAffine (E.X k).left] in
/-- A map of the Čech cosimplicial object followed by a projection to a factor is a projection
followed by a restriction map. -/
lemma cechCosimplicial_map_comp_π {m n : SimplexCategory} (θ : m ⟶ n)
    (i : Fin (n.len + 1) → E.I₀) :
    (cechCosimplicial X E).map θ ≫ Pi.π (cechFactor X E (n := n.len)) i =
      Pi.π (cechFactor X E (n := m.len)) (i ∘ θ.toOrderHom) ≫ (coindPresheaf X).map (Pi.lift
        fun a ↦ Pi.π (fun b ↦ Over.mk (E.f (i b))) (θ.toOrderHom a)).left.op :=
  Pi.lift_π _ _

omit [IsAffine U.left] [Finite E.I₀] [∀ (k : E.I₀), IsAffine (E.X k).left] in
/-- Elementwise form of `cechCosimplicial_map_comp_π`. -/
lemma cechCosimplicial_map_π {m n : SimplexCategory} (θ : m ⟶ n)
    (x : ToType ((cechCosimplicial X E).obj m)) (i : Fin (n.len + 1) → E.I₀) :
    (Pi.π (cechFactor X E) i).hom (((cechCosimplicial X E).map θ).hom x) =
      ((coindPresheaf X).map (Pi.lift fun a ↦
        Pi.π (fun b ↦ Over.mk (E.f (i b))) (θ.toOrderHom a)).left.op).hom
        ((Pi.π (cechFactor X E) (i ∘ θ.toOrderHom)).hom x) :=
  congrArg (fun f ↦ AddCommGrpCat.Hom.hom f x) (cechCosimplicial_map_comp_π X E θ i)

/-- **The Čech cosimplicial group of the coinduced sheaf** along a finite affine covering is the
cosimplicial group of continuous functions on the Čech nerve of the geometric points. -/
def cechCosimplicialIso :
    cechCosimplicial X E ≅ contCosimplicial.{u, max u w, max (u + 1) r} (coverPointMap E) X :=
  NatIso.ofComponents (fun n ↦ (cechCochainsEquiv X hX E n.len).toAddCommGrpIso) (by
    intro m n θ
    ext x : 2
    apply ULift.ext
    ext z
    change cechCochainFun X hX E ((cechCosimplicial X E).map θ x) (nervePointHomeo E _ z) =
      cechCochainFun X hX E x (nervePointHomeo E _ (nerveMap _ θ z))
    simp only [cechCochainFun]
    refine (congrArg (fun y ↦ cechFactorEquiv X hX E _ y _)
      (cechCosimplicial_map_π X E θ x (nervePointHomeo E _ z).1)).trans ?_
    rw [cechFactorEquiv_map, map_prodHomeomorph_symm]
    rfl)

include hX in
/-- **The positive-degree Čech cohomology of the coinduced sheaf along a finite affine covering
vanishes**, for a pro-discrete module. -/
theorem isZero_cechCohomology_coind [NonarchimedeanAddGroup X] [T2Space X]
    (hXd : IsProDiscrete X) (hE : E.sieve₀ ∈ Scheme.ProEt.topology (base K) U) (p : ℕ)
    (hp : 0 < p) : IsZero (Stacks.CechSite.cechCohomology E (coindPresheaf X) p) :=
  (isZero_homology_contCosimplicial.{u, max u w, max (u + 1) r} (coverPointMap E) X
    (coverPointMap_surjective E hE) hXd p hp).of_iso
    (HomologicalComplex.homologyMapIso
      ((AlgebraicTopology.alternatingCofaceMapComplex _).mapIso (cechCosimplicialIso X hX E)) p)

end Cech

/-! ### Acyclicity -/

section Acyclic

variable {Λ : Type r} [Ring Λ] [TopologicalSpace Λ] (X : TopRep.{max u w} Λ (galoisGroup K))
  (hX : Continuous fun p : galoisGroup K × X ↦ X.ρ p.1 p.2)

/-- The abelian sheaf of continuous equivariant functions with values in the coinduced module. -/
abbrev coindAbSheaf : Sheaf (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w} :=
  (sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) r w} Λ) AddCommGrpCat.{max (u + 1) r w})).obj
    (contSheaf.{u, r, max u w} Λ (coindRep X))

variable (K) in
/-- The final object of the pro-étale site of `Spec K`. -/
abbrev finalObj : (base K).ProEt := Scheme.ProEt.mk (𝟙 (base K))

variable (K) in
/-- The final object of the pro-étale site of `Spec K` is terminal. -/
def isTerminal_finalObj : IsTerminal (finalObj K) :=
  let : MorphismProperty.ContainsIdentities @WeaklyEtale := ⟨fun _ ↦ inferInstance⟩
  MorphismProperty.Over.mkIdTerminal _ _

/-- The finite coverings of an affine object by affine objects. -/
def finiteAffineCoverings (U : (base K).ProEt) :
    Set {E : PreZeroHypercover.{u} U // E.sieve₀ ∈ Scheme.ProEt.topology (base K) U} :=
  {E | IsAffine U.left ∧ Finite E.1.I₀ ∧ ∀ i, IsAffine (E.1.X i).left}

/-- Every covering sieve of an affine object contains the sieve of a finite affine covering. -/
lemma exists_finiteAffineCoverings_le (U : (base K).ProEt) (hU : IsAffine U.left) (R : Sieve U)
    (hR : R ∈ Scheme.ProEt.topology (base K) U) :
    ∃ E ∈ finiteAffineCoverings U, E.1.sieve₀ ≤ R := by
  obtain ⟨E, hfin, hcov, hle, haff⟩ := ProEtale.exists_finite_affine_covering_le U R hR
  let e : ULift.{u} (Fin (Nat.card E.I₀)) ≃ E.I₀ :=
    Equiv.ulift.trans (Finite.equivFin E.I₀).symm
  have hs : (E.reindex e).sieve₀ = E.sieve₀ := congrArg Sieve.generate (E.presieve₀_reindex e)
  refine ⟨⟨E.reindex e, ?_⟩,
    ⟨hU, (inferInstance : Finite (ULift.{u} (Fin (Nat.card E.I₀)))), fun i ↦ haff (e i)⟩, ?_⟩
  · rw [hs]
    exact Precoverage.generate_mem_toGrothendieck hcov
  · rw [hs]
    exact hle

variable (K) in
/-- Abelian presheaves on the pro-étale site of `Spec K` admit sheafification, in the
coefficient universe of the completed sheaves. -/
theorem hasSheafify_galois :
    HasSheafify (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w} :=
  ProEtale.hasSheafify_proetale.{u, max r w} _

variable (K) in
/-- Abelian sheaves on the pro-étale site of `Spec K` have enough injectives. -/
theorem enoughInjectives_galois :
    EnoughInjectives (Sheaf (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w}) :=
  ProEtale.enoughInjectives_sheaf_proetale.{max r w} _

variable [HasSheafify (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w}]
  [EnoughInjectives (Sheaf (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w})]
  [(Sheaf.Γ (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w}).Additive]

include hX in
/-- **The sheaf of continuous equivariant functions with values in a coinduced module has no
higher cohomology**, for a pro-discrete module with jointly continuous action. -/
theorem isZero_rightDerived_coindAbSheaf [NonarchimedeanAddGroup X] [T2Space X]
    (hXd : IsProDiscrete X) (p : ℕ) (hp : 0 < p) :
    IsZero (((Sheaf.Γ (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w}).rightDerived
      p).obj (coindAbSheaf X)) := by
  have : HasExt.{max (u + 1) r w}
      (Sheaf (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w}) :=
    hasExt_of_enoughInjectives _
  refine (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{max r w, u,
      u + 1}
    _ _ p).1 ?_
  refine Stacks.CechSite.subsingleton_sheafH_of_cechCohomology_isZero.{max (u + 1) r w, max r w,
      u, u, u + 1}
    (Scheme.ProEt.topology (base K)) {V | IsAffine V.left} finiteAffineCoverings
    (fun _ _ _ ↦ inferInstance) ?_ exists_finiteAffineCoverings_le (coindAbSheaf X) ?_
    (isTerminal_finalObj K) (inferInstanceAs (IsAffine (base K))) p hp
  · rintro U E ⟨hU, _, haff⟩
    exact ⟨hU, haff, fun p i ↦ isAffine_left_piObj hU E.1 haff p i⟩
  · rintro U E ⟨hU, _, haff⟩ q hq
    exact isZero_cechCohomology_coind X hX E.1 hXd E.2 q hq

end Acyclic

end AlgebraicGeometry.GaloisSheaf
