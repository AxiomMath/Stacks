module

public import StacksFrontier.Deformation.Examples.Linear.ContinuousRepresentationsInfinitesimalAutomorphisms
public import StacksFrontier.Deformation.Examples.Linear.ContinuousRepresentationsTangentSpace
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.TangentAtPoint

/-!
# The infinitesimal automorphisms of a continuous representation as a vector space

Let `Γ` be a topological group and `ρ₀ : Γ → GL_k(V)` a finite-dimensional continuous
representation, with deformation category `Def_{V,ρ₀}` of Stacks 0D3K. Stacks 0DVW says that
`Inf(Def_{V,ρ₀}) = H⁰(Γ, End_k(V))` and that `Inf(Def_{V,ρ₀})` is always finite dimensional, for
the natural `k`-vector space structure of Stacks 06JX on `Inf`. This file proves both, and
bundles them with the tangent clauses of the same tag.

The `k`-vector space structure the `Inf` clauses of Stacks 0DVW speak of is that of Stacks 06JX:
`Inf_x` is the tangent space `T_{id_x} Aut(x)` of the automorphism functor at the identity
(`Deformation.localizedAutomorphismFunctorTangent`), with addition composition of automorphisms
and scalar multiplication transport along `ε ↦ cε`. That this structure matches the one of
`H⁰(Γ, End_k(V))` comes down to the base map of the arrow over `ε ↦ cε` multiplying `ε` by an
element of residue `c` (`exists_isFirstOrderReduction_tangentScaling`).

## Main results

All in the namespace `Deformation.Examples.FiniteProjectiveRepresentation`.

* `localizedAutomorphismTangentLinearEquivH0`: **Stacks 0DVW**, the `Inf` clause, as a
  `k`-linear equivalence for the structure of Stacks 06JX.
* `finiteDimensional_continuousLocalizedAutomorphismTangent`: **Stacks 0DVW**, `Inf` is always
  finite dimensional for that structure.
* `continuousRepresentation_tangentSpace_and_infinitesimalAutomorphisms`: **Stacks 0DVW**, all
  four clauses together.

## References

* [Stacks Project, Tag 0DVW](https://stacks.math.columbia.edu/tag/0DVW)
* [Stacks Project, Tag 06JX](https://stacks.math.columbia.edu/tag/06JX)
* [Stacks Project, Tag 0DVT](https://stacks.math.columbia.edu/tag/0DVT)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Deformation.Examples.FiniteProjectiveRepresentation

open Deformation Stacks.ContinuousCohomology

universe d u w

variable {Λ : Type u} {k Γ : Type w} [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
  [TopologicalSpace Γ]

/-! ### The `k`-vector space structure of Stacks 06JX -/

section NaturalStructure

/-- In the dual numbers `k[ε]`, the element `ε` generates the kernel of the residue map and
annihilates exactly its own multiples; this is read here on any ring `R` identified with `k[ε]`
by a ring isomorphism `e`, for a map `π` to `k` that is the first coordinate through `e`. -/
theorem dvd_iff_of_ringEquiv_dualNumber {R : Type*} [CommRing R] (e : R ≃+* DualNumber k)
    (π : R →+* k) (hπ : ∀ a, π a = TrivSqZeroExt.fst (e a)) :
    (∀ a, π a = 0 ↔ e.symm DualNumber.eps ∣ a) ∧
      (∀ a, e.symm DualNumber.eps * a = 0 ↔ e.symm DualNumber.eps ∣ a) := by
  have hdvd : ∀ a : R, e.symm DualNumber.eps ∣ a ↔ DualNumber.eps ∣ e a := by
    intro a
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨e c, by rw [map_mul, RingEquiv.apply_symm_apply]⟩
    · rintro ⟨z, hz⟩
      refine ⟨e.symm z, ?_⟩
      rw [← map_mul, ← hz, RingEquiv.symm_apply_apply]
  refine ⟨fun a ↦ ?_, fun a ↦ ?_⟩
  · rw [hπ, hdvd, DualNumber.fst_eq_zero_iff_eps_dvd]
  · rw [hdvd, ← DualNumber.fst_eq_zero_iff_eps_dvd, ← DualNumber.eps_mul_eq_zero_iff,
      ← map_eq_zero_iff e e.injective, map_mul, RingEquiv.apply_symm_apply]

/-- An equality of objects of `𝒞_Λ` gives a ring isomorphism of their carriers, acting by the
`eqToHom` of the equality and its inverse. -/
theorem exists_ringEquiv_of_eq {A B : ArtinianLocalAlgCat.{u, w, w} Λ k} (h : A = B) :
    ∃ f : A ≃+* B, (∀ a, f a = (eqToHom h).hom a) ∧ ∀ b, f.symm b = (eqToHom h.symm).hom b := by
  subst h
  exact ⟨RingEquiv.refl _, fun _ ↦ rfl, fun _ ↦ rfl⟩

variable (V : Type w) [AddCommGroup V] [Module k V] [Module.Finite k V]
  (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀)
  {x : continuousDeformationCategory (Λ := Λ) V ρ₀ hρ₀}
  (P : ChosenPushforwardsAt (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀) x)

/-- The pushforward of a continuous deformation to the canonical dual numbers under its base
exhibits `V` as a first-order reduction of its module along the element `ε`, and the scaling
`ε ↦ cε` of the dual numbers acts on the base of that pushforward by multiplying `ε` by an
element of residue `c`. -/
theorem exists_isFirstOrderReduction_tangentScaling :
    let xε := P.obj (dualNumbersUnder (p := continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀)
      (x := x))
    ∃ eps : xε.1.left.obj.base,
      IsFirstOrderReduction (κ := k) (V := V) eps
        xε.1.hom.hom.base.hom.toRingHom xε.1.hom.hom.map ∧
      ∀ c : k, ∃ c₀ : xε.1.left.obj.base, xε.1.hom.hom.base.hom c₀ = c ∧
        (P.map (tangentScaling (p := continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀)
          (x := x) c)).left.hom.base.hom eps = c₀ * eps := by
  intro xε
  let p := continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀
  let D := dualNumbersUnder (p := p) (x := x)
  let := residueAlgebra (p.obj x)
  have hR : xε.1.left.obj.base = D.right := xε.2
  obtain ⟨f, hf, hfs⟩ := exists_ringEquiv_of_eq hR
  let e : D.right ≃+* DualNumber k :=
    (Deformation.dualNumbersEquiv (Λ := (p.obj x : Type w)) (k := k)).toRingEquiv
  let eR : xε.1.left.obj.base ≃+* DualNumber k := f.trans e
  have hfst : ∀ z, TrivSqZeroExt.fst (e z) = TrivSqZeroExt.fst z := fun z ↦
    Deformation.dualNumbersEquiv_fst (Λ := (p.obj x : Type w)) (k := k) z
  have hsnd : ∀ z, TrivSqZeroExt.snd (e z) = ULift.down (TrivSqZeroExt.snd z) := fun z ↦
    congrArg (fun y : D.right ↦ ULift.down (TrivSqZeroExt.snd y))
      ((AlgEquiv.ofBijective (Deformation.dualNumbersUp (Λ := (p.obj x : Type w)) (k := k))
        Deformation.dualNumbersUp_bijective).apply_symm_apply z)
  let π := xε.1.hom.hom.base
  -- the reduction to the residue field is the first coordinate of the dual numbers
  have hresD : ∀ z : D.right, π.hom ((eqToHom hR.symm).hom z) = TrivSqZeroExt.fst z := by
    intro z
    exact (Examples.residueFieldBase_residueEquiv_residue (Λ := Λ) (k := k) _).symm.trans
      ((eqToHom hR.symm ≫ π).residue_comm z)
  have hπ : ∀ a, π.hom a = TrivSqZeroExt.fst (eR a) := by
    intro a
    have h1 : a = (eqToHom hR.symm).hom (f a) := by rw [← hfs, RingEquiv.symm_apply_apply]
    rw [h1, hresD, ← hfs, RingEquiv.symm_apply_apply]
    exact (hfst (f a)).symm
  obtain ⟨hpi, hmul⟩ := dvd_iff_of_ringEquiv_dualNumber eR π.hom.toRingHom hπ
  refine ⟨eR.symm DualNumber.eps,
    isFirstOrderReduction_continuousDeformation_of_eps V ρ₀ hρ₀ xε _ hpi hmul, fun c ↦ ?_⟩
  refine ⟨eR.symm (TrivSqZeroExt.inl c), ?_, ?_⟩
  · rw [hπ, RingEquiv.apply_symm_apply, TrivSqZeroExt.fst_inl]
  · let s := tangentScaling (p := p) (x := x) c
    have hbase : (P.map s).left.hom.base = eqToHom hR ≫ s.right ≫ eqToHom hR.symm :=
      CategoryTheory.IsHomLift.fac' (p := p) (f := s.right) (φ := P.map s)
    -- the scaling multiplies `ε` by `c` in the dual numbers under the base of `x`
    have hs : s.right.hom (e.symm DualNumber.eps) =
        e.symm (TrivSqZeroExt.inl c) * e.symm DualNumber.eps := by
      refine e.injective ?_
      rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, DualNumber.fst_eps, mul_zero]
        rw [hfst, tangentScaling_right_hom_fst]
        rw [← hfst (e.symm DualNumber.eps), RingEquiv.apply_symm_apply, DualNumber.fst_eps]
      · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
          DualNumber.fst_eps, DualNumber.snd_eps, smul_eq_mul, mul_one, MulOpposite.op_zero,
          zero_smul, add_zero]
        rw [hsnd, tangentScaling_right_hom_snd]
        change c * ULift.down (TrivSqZeroExt.snd (e.symm DualNumber.eps)) = c
        rw [← hsnd, RingEquiv.apply_symm_apply, DualNumber.snd_eps, mul_one]
    rw [hbase]
    change (eqToHom hR.symm).hom (s.right.hom ((eqToHom hR).hom (eR.symm DualNumber.eps))) = _
    rw [← hf, ← hfs]
    change f.symm (s.right.hom (f (f.symm (e.symm DualNumber.eps)))) =
      f.symm (e.symm (TrivSqZeroExt.inl c)) * f.symm (e.symm DualNumber.eps)
    rw [RingEquiv.apply_symm_apply, hs, map_mul]

/-- **Stacks 0DVW**, the clause `Inf(Def_{V,ρ₀}) = H⁰(Γ, End_k(V))`, as `k`-vector spaces. For a
finite-dimensional continuous representation `ρ₀` of a topological group, the infinitesimal
automorphisms of the deformation category of Stacks 0D3K at a point `x`, in their natural
`k`-vector space structure of Stacks 06JX — the tangent space `T_{id_x} Aut(x)` of the
automorphism functor at the identity, whose addition is composition of automorphisms and whose
scalar multiplication is transport along `ε ↦ cε` — are `k`-linearly isomorphic to the
degree-zero cohomology `H⁰(Γ, End_k(V))` of the conjugation action.

The proof is that of Stacks 0DVT: an infinitesimal automorphism is an automorphism `id + εφ` of
the module of the pushforward of `x` to the dual numbers, for a unique `Γ`-equivariant `φ`, and
composing automorphisms adds the `φ`'s (`continuousAutEquivInvariants`). The pushforward along
`ε ↦ cε` is semilinear along a base map sending `ε` to an element of residue `c` times `ε`, so
transport along it turns `id + εφ` into `id + ε(cφ)`. -/
@[stacks 0DVW "`Inf(Def_{V,ρ₀}) = H⁰(Γ, End_k(V))` as `k`-vector spaces, for the natural \
`k`-vector space structure of Stacks 06JX on `Inf`"]
def localizedAutomorphismTangentLinearEquivH0 :
    letI := naturalLocalizedTangentAddCommGroup P
      (isDeformationCategory_continuousDeformationCategory (Λ := Λ) V ρ₀ hρ₀).satisfiesRS
    letI := naturalLocalizedTangentModule P
      (isDeformationCategory_continuousDeformationCategory (Λ := Λ) V ρ₀ hρ₀).satisfiesRS
    localizedAutomorphismFunctorTangent P ≃ₗ[k]
      groupCohomology (Rep.of (Representation.linHom ρ₀ ρ₀)) 0 := by
  let p := continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀
  let hD := isDeformationCategory_continuousDeformationCategory (Λ := Λ) V ρ₀ hρ₀
  letI := naturalLocalizedTangentAddCommGroup P hD.satisfiesRS
  letI := naturalLocalizedTangentModule P hD.satisfiesRS
  let D := dualNumbersUnder (p := p) (x := x)
  let xε := P.obj D
  let hex := exists_isFirstOrderReduction_tangentScaling V ρ₀ hρ₀ P
  let eps := Classical.choose hex
  have hfo := (Classical.choose_spec hex).1
  have hsc := (Classical.choose_spec hex).2
  let W := ↥((Representation.linHom ρ₀ ρ₀).invariants)
  let F : Aut xε ≃* Multiplicative W := continuousAutEquivInvariants V ρ₀ hρ₀ xε eps hfo
  let K := localizedTangentEquivAut P hD.predeformation
  let L : groupCohomology (Rep.of (Representation.linHom ρ₀ ρ₀)) 0 ≃ₗ[k] W :=
    Iso.toLinearEquiv (groupCohomology.H0Iso (Rep.of (Representation.linHom ρ₀ ρ₀)))
  -- transport along `ε ↦ cε` multiplies the endomorphism attached to an automorphism by `c`
  have htr : ∀ (c : k) (w : W), P.transportAutHom (tangentScaling (p := p) (x := x) c)
      (F.symm (Multiplicative.ofAdd w)) = F.symm (Multiplicative.ofAdd (c • w)) := by
    intro c w
    obtain ⟨c₀, hc₀, hb⟩ := hsc c
    let s := tangentScaling (p := p) (x := x) c
    let T := (P.map s).left.hom
    have hψT : ∀ mm, xε.1.hom.hom.map (T.map mm) = xε.1.hom.hom.map mm := fun mm ↦
      congrArg
        (fun q : FiniteProjectiveRepresentation.Hom xε.1.left.obj
          (continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀).obj ↦ q.map mm)
        (congrArg (fun q : xε.1.left ⟶ (continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀) ↦ q.hom)
          (Over.w (P.map s)))
    have hc₀' : xε.1.hom.hom.base.hom.toRingHom c₀ = c := hc₀
    have hTlift : ∀ v : V, T.map (epsLift hfo v) = epsLift hfo (c • v) := by
      intro v
      obtain ⟨n, hn⟩ := hfo.surjective v
      calc T.map (epsLift hfo v)
          = T.map (epsLift hfo (xε.1.hom.hom.map n)) :=
            congrArg (fun m ↦ T.map (epsLift hfo m)) hn.symm
        _ = T.map (eps • n) := congrArg T.map (epsLift_apply_map hfo n)
        _ = T.base.hom eps • T.map n := T.map_smul eps n
        _ = (c₀ * eps) • T.map n := congrArg (· • T.map n) hb
        _ = c₀ • (eps • T.map n) := mul_smul c₀ eps (T.map n)
        _ = c₀ • epsLift hfo (xε.1.hom.hom.map (T.map n)) :=
          congrArg (c₀ • ·) (epsLift_apply_map hfo (T.map n)).symm
        _ = c₀ • epsLift hfo v :=
          congrArg (fun m ↦ c₀ • epsLift hfo m) ((hψT n).trans hn)
        _ = epsLift hfo (c • v) := by
          rw [← hc₀']
          exact (epsLift_smul hfo c₀ v).symm
    have hcomm : (F.symm (Multiplicative.ofAdd w)).asIso.hom.val ≫ P.map s =
        P.map s ≫ (F.symm (Multiplicative.ofAdd (c • w))).asIso.hom.val := by
      refine Over.OverMorphism.ext (ObjectProperty.hom_ext _
        (FiniteProjectiveRepresentation.Hom.ext ?_ (AddMonoidHom.ext fun mm ↦ ?_)))
      · change 𝟙 _ ≫ T.base = T.base ≫ 𝟙 _
        rw [Category.id_comp, Category.comp_id]
      · change T.map (epsEndo hfo w.1 mm) = epsEndo hfo (c • w).1 (T.map mm)
        calc T.map (epsEndo hfo w.1 mm)
            = T.map (mm + epsLift hfo (w.1 (xε.1.hom.hom.map mm))) := rfl
          _ = T.map mm + T.map (epsLift hfo (w.1 (xε.1.hom.hom.map mm))) := T.map.map_add _ _
          _ = T.map mm + epsLift hfo (c • w.1 (xε.1.hom.hom.map mm)) :=
            congrArg (T.map mm + ·) (hTlift _)
          _ = T.map mm + epsLift hfo ((c • w).1 (xε.1.hom.hom.map (T.map mm))) :=
            congrArg (fun m ↦ T.map mm + epsLift hfo ((c • w).1 m)) (hψT mm).symm
          _ = epsEndo hfo (c • w).1 (T.map mm) := rfl
    exact (transportAut_eq_iff P s _ _).2 hcomm
  let E₀ : localizedAutomorphismFunctorTangent P ≃
      groupCohomology (Rep.of (Representation.linHom ρ₀ ρ₀)) 0 :=
    K.trans (F.toEquiv.trans (Multiplicative.toAdd.trans L.symm.toEquiv))
  have hE₀ : ∀ a, E₀ a = L.symm (Multiplicative.toAdd (F (K a))) := fun _ ↦ rfl
  refine { E₀ with map_add' := fun a b ↦ ?_, map_smul' := fun c a ↦ ?_ }
  · change E₀ (a + b) = E₀ a + E₀ b
    rw [hE₀, hE₀, hE₀, localizedTangentEquivAut_add P hD.predeformation hD.satisfiesRS,
      map_mul, toAdd_mul, map_add]
  · change E₀ (c • a) = c • E₀ a
    obtain ⟨w, hw⟩ : ∃ w : W, K a = F.symm (Multiplicative.ofAdd w) :=
      ⟨Multiplicative.toAdd (F (K a)), (F.symm_apply_apply (K a)).symm⟩
    rw [hE₀, hE₀, localizedTangentEquivAut_smul P hD.predeformation hD.satisfiesRS]
    change L.symm (Multiplicative.toAdd (F (P.transportAutHom
      (tangentScaling (p := p) (x := x) c) (K a)))) = c • L.symm (Multiplicative.toAdd (F (K a)))
    rw [hw, htr, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, toAdd_ofAdd, toAdd_ofAdd,
      map_smul]

/-- **Stacks 0DVW**, the clause that `Inf(Def_{V,ρ₀})` is *always* finite dimensional, for its
natural `k`-vector space structure of Stacks 06JX: no hypothesis on `Γ` is needed, because
`Inf(Def_{V,ρ₀})` is `H⁰(Γ, End_k(V))` (`localizedAutomorphismTangentLinearEquivH0`), the
subspace of `Γ`-invariants of the finite-dimensional space `End_k(V)`. -/
@[stacks 0DVW "`Inf(Def_{V,ρ₀})` is always finite dimensional, for the natural `k`-vector space \
structure of Stacks 06JX"]
theorem finiteDimensional_continuousLocalizedAutomorphismTangent :
    letI := naturalLocalizedTangentAddCommGroup P
      (isDeformationCategory_continuousDeformationCategory (Λ := Λ) V ρ₀ hρ₀).satisfiesRS
    letI := naturalLocalizedTangentModule P
      (isDeformationCategory_continuousDeformationCategory (Λ := Λ) V ρ₀ hρ₀).satisfiesRS
    FiniteDimensional k (localizedAutomorphismFunctorTangent P) := by
  let := naturalLocalizedTangentAddCommGroup P
    (isDeformationCategory_continuousDeformationCategory (Λ := Λ) V ρ₀ hρ₀).satisfiesRS
  let := naturalLocalizedTangentModule P
    (isDeformationCategory_continuousDeformationCategory (Λ := Λ) V ρ₀ hρ₀).satisfiesRS
  have := finiteDimensional_groupCohomology_zero_linHom (Γ := Γ) V ρ₀
  exact (localizedAutomorphismTangentLinearEquivH0 V ρ₀ hρ₀ P).symm.finiteDimensional

end NaturalStructure

/-- **Stacks 0DVW.** Let `ρ₀ : Γ → GL_k(V)` be a finite-dimensional continuous representation of
a topological group, and `Def_{V,ρ₀}` the deformation category of Stacks 0D3K. Then

* `T Def_{V,ρ₀} = H¹(Γ, End_k(V))`: the tangent space, in its natural `k`-vector space structure
  of Stacks 06IH, is `k`-linearly isomorphic to the first continuous cohomology of the dual
  tensor module `Vᵛ ⊗_k V`, whose representation is the conjugation action on `End_k(V)`;
* `Inf(Def_{V,ρ₀}) = H⁰(Γ, End_k(V))`: the infinitesimal automorphisms at any point `x`, in
  their natural `k`-vector space structure of Stacks 06JX (addition is composition, `c` acts by
  transport along `ε ↦ cε`), are `k`-linearly isomorphic to the degree-zero cohomology of the
  conjugation action;
* `Inf(Def_{V,ρ₀})` is always finite dimensional, for that structure;
* `T Def_{V,ρ₀}` is finite dimensional if `Γ` is topologically finitely generated, that is, has
  a dense finitely generated subgroup.

The four clauses are `tangentSpaceEquivContinuousCohomology`,
`localizedAutomorphismTangentLinearEquivH0`,
`finiteDimensional_continuousLocalizedAutomorphismTangent` and
`finiteDimensional_continuousTangentSpace`. -/
@[stacks 0DVW "all four clauses: `T Def = H¹(Γ, End_k(V))`, `Inf(Def) = H⁰(Γ, End_k(V))` for the \
natural `k`-vector space structure of Stacks 06JX on `Inf`, `Inf(Def)` always finite \
dimensional, `T Def` finite dimensional for topologically finitely generated `Γ`"]
theorem continuousRepresentation_tangentSpace_and_infinitesimalAutomorphisms
    [IsTopologicalGroup Γ]
    [HasDerivedCategory.{d} (Stacks.Injectives.ContinuousModule.{w, w, w} k Γ)]
    [HasDerivedCategory.{d} (ModuleCat.{w} k)]
    (V : Type w) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀)
    {x : continuousDeformationCategory (Λ := Λ) V ρ₀ hρ₀}
    (P : ChosenPushforwardsAt (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀) x) :
    let 𝓕 := BasedCategory.ofFunctor (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀)
    let hD := isDeformationCategory_continuousDeformationCategory (Λ := Λ) V ρ₀ hρ₀
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
    letI : Fact (SchlessingerConditionS2
        (Functor.Elements.π
          (isomorphismClasses 𝓕 hD.predeformation.cofibered))) :=
      ⟨Deformation.Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
        𝓕 hD⟩
    letI := Stacks.ContinuousCohomology.hasExt_continuousModule.{w, w, w} k Γ
    let M := continuousModuleOfContinuousRepresentation V ρ₀ hρ₀
    letI : Module.Finite k (M.obj.obj.V : Type w) := inferInstanceAs (Module.Finite k V)
    letI : Module.Projective k (M.obj.obj.V : Type w) :=
      inferInstanceAs (Module.Projective k V)
    letI := naturalLocalizedTangentAddCommGroup P hD.satisfiesRS
    letI := naturalLocalizedTangentModule P hD.satisfiesRS
    Nonempty (Σ' _ : artinianTangentSpace Λ k
          (isomorphismClasses 𝓕 hD.predeformation.cofibered) ≃ₗ[k]
        (Stacks.ContinuousCohomology.cohomologyFunctor.{d, w, w, w} k Γ 1).obj
          (Stacks.ContinuousCohomology.dualTensorContinuousModule k Γ M M),
      (Stacks.ContinuousCohomology.rep k Γ
        (Stacks.ContinuousCohomology.dualTensorContinuousModule k Γ M M)).Equiv
          (Representation.linHom ρ₀ ρ₀)) ∧
      Nonempty (localizedAutomorphismFunctorTangent P ≃ₗ[k]
        groupCohomology (Rep.of (Representation.linHom ρ₀ ρ₀)) 0) ∧
      FiniteDimensional k (localizedAutomorphismFunctorTangent P) ∧
      ((∃ H : Subgroup Γ, Group.FG ↥H ∧ Dense (H : Set Γ)) →
        FiniteDimensional k (artinianTangentSpace Λ k
          (isomorphismClasses 𝓕 hD.predeformation.cofibered))) :=
  ⟨⟨tangentSpaceEquivContinuousCohomology (Λ := Λ) V ρ₀ hρ₀⟩,
    ⟨localizedAutomorphismTangentLinearEquivH0 V ρ₀ hρ₀ P⟩,
    finiteDimensional_continuousLocalizedAutomorphismTangent V ρ₀ hρ₀ P,
    fun hΓ ↦ finiteDimensional_continuousTangentSpace (Λ := Λ) V ρ₀ hρ₀ hΓ⟩

end Deformation.Examples.FiniteProjectiveRepresentation

end
