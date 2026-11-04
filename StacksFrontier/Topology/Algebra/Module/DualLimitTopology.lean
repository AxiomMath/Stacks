module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import StacksFrontier.Topology.Algebra.DiscreteLimitTopology
import Mathlib.LinearAlgebra.Quotient.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The limit topology on the dual of a vector space

Let `k` be a field and `V` a `k`-vector space. [Stacks, Section 0G59] topologises
`Hom_k(V, k)` as follows: write `V = ⋃ V_i` as the filtered union of its finite dimensional
subspaces and give `Hom_k(V, k) = lim Hom_k(V_i, k)` the limit topology of the discrete spaces
`Hom_k(V_i, k)` ([Stacks, Section 07E7]). The source then observes that this topology is discrete
when `dim_k V < ∞`, and that if `V = colim_n V_n` is a directed colimit of finite dimensional
spaces then `Hom_k(V, k) = lim Hom_k(V_n, k)` as topological vector spaces.

This file formalises the three statements, over an arbitrary commutative semiring `R` in place of
`k` and with "finitely generated" in place of "finite dimensional" wherever that is all the
argument uses. The topology is defined as the topology of pointwise convergence for the discrete
topology on `R` (`Module.Dual.limitTopology`); that this is the topology of the source is
`Module.Dual.limitTopology_eq_iInf_finiteDimensional`. The colimit statement holds for any family
of finitely generated modules `V_i → V` whose images span `V` (no directedness is needed), and in
particular for every colimit cocone of finitely generated modules in `ModuleCat R`.

## Main definitions

* `Module.Dual.limitTopology`: the topology of [Stacks, Section 0G59] on `Hom_R(V, R)`.
* `ModuleCat.dual`: the functor `X ↦ Hom_R(X, R)` on `ModuleCat R`.
* `ModuleCat.isLimitMapConeDual`: it turns colimit cocones into limit cones, that is
  `Hom_R(colim V_j, R) = lim Hom_R(V_j, R)`.

## Main results

* `Module.Dual.limitTopology_eq_iInf_finiteDimensional`: the topology is the limit topology of
  `lim Hom_k(V_i, k)` over the finite dimensional subspaces `V_i ⊆ V`, as in the source
  (`Module.Dual.limitTopology_eq_iInf_fg` over a semiring).
* `Module.Dual.limitTopology_eq_bot`: it is discrete when `V` is finitely generated.
* `Module.Dual.isHomeomorph_of_iSup_range_eq_top`: if finitely generated modules `V_i → V` span
  `V`, then any bijection `Hom_R(V, R) ≃ L` onto a space `L` with the limit topology of maps
  `L → W_i`, compatible with the restrictions `Hom_R(V, R) → Hom_R(V_i, R)` followed by
  injections `Hom_R(V_i, R) → W_i`, is a homeomorphism.
* `ModuleCat.isHomeomorph_conePointsIsoOfNatIso_dual`: for a colimit cocone of finitely generated
  modules `V_j → V` and isomorphisms `Hom_R(V_j, R) ≅ W_j` natural in `j`, the induced isomorphism
  `Hom_R(V, R) ≅ lim W_j` is a homeomorphism; `ModuleCat.isHomeomorph_conePointUniqueUpToIso_dual`
  is the case `W_j = Hom_R(V_j, R)`.

## References

* [Stacks Project, Section 0G59](https://stacks.math.columbia.edu/tag/0G59)
* [Stacks Project, Section 07E7](https://stacks.math.columbia.edu/tag/07E7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology

universe w w' u


namespace Module.Dual

section Semiring

variable (R V : Type*) [CommSemiring R] [AddCommMonoid V] [Module R V]

/-- The topology of [Stacks, Section 0G59] on `Hom_R(V, R)`: the coarsest topology for which
evaluation at every `v : V` is continuous with `R` discrete, i.e. pointwise convergence. It is the
limit topology of `lim Hom_R(V_i, R)` over the finitely generated submodules `V_i ⊆ V`
(`Module.Dual.limitTopology_eq_iInf_fg`, and `Module.Dual.limitTopology_eq_iInf_finiteDimensional`
over a field). -/
@[instance_reducible, sga "3 VIIB 0.2.2" "special case", sga "3 VIIB 1.2.3.A" "special case"]
def limitTopology : TopologicalSpace (Module.Dual R V) :=
  ⨅ v : V, TopologicalSpace.induced (fun f : Module.Dual R V => f v) ⊥

/-- The limit topology agrees with the limit topology of the restrictions to a family `P` of
finitely generated submodules containing every cyclic submodule. -/
private theorem limitTopology_eq_iInf_of (P : Submodule R V → Prop)
    (hP : ∀ W, P W → W.FG) (hP' : ∀ v, P (R ∙ v)) :
    limitTopology R V = ⨅ W : {W : Submodule R V // P W},
      TopologicalSpace.induced (fun f : Module.Dual R V => f.domRestrict W.1) ⊥ := by
  refine le_antisymm (continuous_id_iff_le.1 ?_) (continuous_id_iff_le.1 ?_)
  · refine continuous_iInf_induced_bot_of_finite _ _ id fun W => ?_
    obtain ⟨S, hSfin, hS⟩ := Submodule.fg_def.1 (hP W.1 W.2)
    refine ⟨S, hSfin, fun f g hfg => ?_⟩
    ext ⟨w, hw⟩
    rw [← hS] at hw
    exact LinearMap.eqOn_span' hfg hw
  · exact continuous_iInf_induced_bot_of_forall_exists _ _ id fun v =>
      ⟨⟨R ∙ v, hP' v⟩, fun f => f ⟨v, Submodule.mem_span_singleton_self v⟩, fun f => rfl⟩

/-- **The topology of [Stacks, Section 0G59] on `Hom_R(V, R)`**: the limit topology of
`Hom_R(V, R) = lim Hom_R(V_i, R)` over the finitely generated submodules `V_i ⊆ V`, each
`Hom_R(V_i, R)` discrete. -/
theorem limitTopology_eq_iInf_fg :
    limitTopology R V = ⨅ W : {W : Submodule R V // W.FG},
      TopologicalSpace.induced (fun f : Module.Dual R V => f.domRestrict W.1) ⊥ :=
  limitTopology_eq_iInf_of R V _ (fun _ => id) fun v => Submodule.fg_span_singleton v

/-- **The limit topology on `Hom_R(V, R)` is discrete when `V` is finitely generated**
([Stacks, Section 0G59], for `dim_k V < ∞`). -/
theorem limitTopology_eq_bot [Module.Finite R V] : limitTopology R V = ⊥ := by
  obtain ⟨S, hSfin, hS⟩ := Submodule.fg_def.1 (Module.Finite.fg_top (R := R) (M := V))
  exact iInf_induced_bot_eq_bot_of_finite _ hSfin fun f g hfg => LinearMap.ext_on hS hfg

/-- `Hom_R(V, R)` with the limit topology is a discrete space when `V` is finitely generated. -/
theorem discreteTopology_limitTopology [Module.Finite R V] :
    @DiscreteTopology (Module.Dual R V) (limitTopology R V) :=
  @DiscreteTopology.mk _ (limitTopology R V) (limitTopology_eq_bot R V)

variable {R V}

/-- **The dual of a colimit is the limit of the duals, as topological modules**
([Stacks, Section 0G59]). Let `j i : V_i → V` be linear maps from finitely generated modules
whose images span `V`, for instance the maps of a colimit cocone. Let `L` carry the limit topology
of maps `π i : L → W_i` into discrete spaces, and let `e : Hom_R(V, R) ≃ L` be a bijection such
that `π i ∘ e` is the restriction `f ↦ f ∘ j i` followed by an injection
`φ i : Hom_R(V_i, R) → W_i`. Then `e` is a homeomorphism.

With `W_i = Hom_R(V_i, R)` and `φ i = id` this says that `Hom_R(V, R) → lim Hom_R(V_i, R)` is a
homeomorphism; general `φ i` allow composing with isomorphisms `Hom_R(V_i, R) ≅ W_i` compatible
with the transition maps. -/
theorem isHomeomorph_of_iSup_range_eq_top {ι : Type*} {V' : ι → Type*}
    [∀ i, AddCommMonoid (V' i)] [∀ i, Module R (V' i)] [∀ i, Module.Finite R (V' i)]
    (j : ∀ i, V' i →ₗ[R] V) (hj : ⨆ i, LinearMap.range (j i) = ⊤)
    {L : Type*} {W : ι → Type*} (π : ∀ i, L → W i) (φ : ∀ i, Module.Dual R (V' i) → W i)
    (hφ : ∀ i, Function.Injective (φ i)) (e : Module.Dual R V ≃ L)
    (he : ∀ f i, π i (e f) = φ i (f ∘ₗ j i)) :
    letI := limitTopology R V
    letI := ⨅ i, TopologicalSpace.induced (π i) ⊥
    IsHomeomorph e := by
  refine isHomeomorph_iInf_induced_bot_of_finite (fun (v : V) (f : Module.Dual R V) => f v) π e
    (fun i => ?_) (fun v => ?_)
  · obtain ⟨S, hSfin, hS⟩ := Submodule.fg_def.1 (Module.Finite.fg_top (R := R) (M := V' i))
    refine ⟨j i '' S, hSfin.image _, fun f g hfg => ?_⟩
    rw [he, he]
    exact congrArg (φ i) (LinearMap.ext_on hS fun x hx => hfg _ ⟨x, hx, rfl⟩)
  · let N : Submodule R V :=
      { carrier := {v | ∃ s : Set ι, s.Finite ∧
          ∀ x y, (∀ i ∈ s, π i x = π i y) → e.symm x v = e.symm y v}
        add_mem' := by
          rintro v w ⟨s, hs, hsv⟩ ⟨t, ht, htw⟩
          refine ⟨s ∪ t, hs.union ht, fun x y hxy => ?_⟩
          rw [map_add, map_add, hsv x y fun i hi => hxy i (Or.inl hi),
            htw x y fun i hi => hxy i (Or.inr hi)]
        zero_mem' := ⟨∅, Set.finite_empty, fun x y _ => by rw [map_zero, map_zero]⟩
        smul_mem' := by
          rintro a v ⟨s, hs, hsv⟩
          exact ⟨s, hs, fun x y hxy => by rw [map_smul, map_smul, hsv x y hxy]⟩ }
    have hN : ⊤ ≤ N := by
      rw [← hj]
      refine iSup_le fun i => ?_
      rintro _ ⟨w, rfl⟩
      refine ⟨{i}, Set.finite_singleton i, fun x y hxy => ?_⟩
      have h : φ i (e.symm x ∘ₗ j i) = φ i (e.symm y ∘ₗ j i) := by
        rw [← he, ← he, e.apply_symm_apply, e.apply_symm_apply]
        exact hxy i rfl
      exact LinearMap.congr_fun (hφ i h) w
    exact hN (Submodule.mem_top (x := v))

end Semiring

section Field

variable (k V : Type*) [Field k] [AddCommGroup V] [Module k V]

/-- **The topology of [Stacks, Section 0G59] on `Hom_k(V, k)`**, as the source defines it: write
`V = ⋃ V_i` as the filtered union of its finite dimensional subspaces; then the topology is the
limit topology of `Hom_k(V, k) = lim Hom_k(V_i, k)`, each `Hom_k(V_i, k)` discrete. -/
theorem limitTopology_eq_iInf_finiteDimensional :
    limitTopology k V = ⨅ W : {W : Submodule k V // FiniteDimensional k W},
      TopologicalSpace.induced (fun f : Module.Dual k V => f.domRestrict W.1) ⊥ :=
  limitTopology_eq_iInf_of k V _ (fun W => (Submodule.fg_iff_finiteDimensional W).2)
    fun v => (Submodule.fg_iff_finiteDimensional _).1 (Submodule.fg_span_singleton v)

end Field

end Module.Dual

namespace ModuleCat

variable (R : Type u) [CommRing R]

/-- The functor `X ↦ Hom_R(X, R)` on `R`-modules, sending `f` to its transpose
`LinearMap.dualMap`. -/
@[simps,
  sga "2 IV 5.2" "Case A = k = k₀",
  sga "3 VIIA 3.1.1" "affine dual object",
  sga "3 VIIA 4.3.3" "special case",
  sga "3 VIIB 1.3.5.C" "more general",
  sga "3 VIII 6.8"]
def dual : (ModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} R where
  obj X := ModuleCat.of R (Module.Dual R X.unop)
  map f := ModuleCat.ofHom f.unop.hom.dualMap

variable {R} {J : Type w} [Category.{w'} J] {G : J ⥤ ModuleCat.{u} R}

/-- The maps of a colimit cocone of modules jointly span its point. -/
theorem iSup_range_ι_eq_top {d : Cocone G} (hd : IsColimit d) :
    ⨆ j, LinearMap.range (Hom.hom (A := G.obj j) (B := d.pt) (d.ι.app j)) = ⊤ := by
  set N := ⨆ j, LinearMap.range (Hom.hom (A := G.obj j) (B := d.pt) (d.ι.app j))
  have h : ModuleCat.ofHom N.mkQ = 0 := hd.hom_ext fun j => by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    simp only [hom_comp, hom_ofHom, LinearMap.coe_comp, Function.comp_apply, Limits.comp_zero,
      hom_zero, LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_iSup_of_mem j ⟨x, rfl⟩
  rw [← Submodule.ker_mkQ N, ← ModuleCat.hom_ofHom N.mkQ, h, hom_zero, LinearMap.ker_zero]

/-- The component at `j` of a cone over the duals `Hom_R(G j, R)`, as a linear map into
`Module.Dual R (G.obj j)`. -/
def coneDualHom (s : Cone (G.op ⋙ dual R)) (j : J) : s.pt →ₗ[R] Module.Dual R (G.obj j) :=
  (s.π.app (op j)).hom

/-- The components of a cone over the duals are compatible: `π_{j'}(x) ∘ G(f) = π_j(x)`. -/
theorem coneDualHom_apply_map (s : Cone (G.op ⋙ dual R)) {j j' : J} (f : j ⟶ j')
    (x : s.pt) (w : G.obj j) :
    coneDualHom s j' x (G.map f w) = coneDualHom s j x w := by
  rw [coneDualHom, coneDualHom, ← s.w f.op]
  rfl

/-- The cocone over `G` with point `Hom_R(s.pt, R)` attached to a cone `s` over the duals. -/
def coconeOfDualCone (s : Cone (G.op ⋙ dual R)) : Cocone G where
  pt := ModuleCat.of R (Module.Dual R s.pt)
  ι :=
    { app j := ModuleCat.ofHom (coneDualHom s j).flip
      naturality _ _ f := ModuleCat.hom_ext (LinearMap.ext fun w => LinearMap.ext fun x =>
        coneDualHom_apply_map s f x w) }

/-- The linear map `V → Hom_R(s.pt, R)` out of the colimit, induced by a cone `s` over the
duals. -/
def descDual {d : Cocone G} (hd : IsColimit d) (s : Cone (G.op ⋙ dual R)) :
    d.pt →ₗ[R] Module.Dual R s.pt :=
  (hd.desc (coconeOfDualCone s)).hom

/-- `descDual hd s` sends the image of `w : G.obj j` under the cocone map at `j` to the functional
`x ↦ π_j(x)(w)`. -/
theorem descDual_ι {d : Cocone G} (hd : IsColimit d) (s : Cone (G.op ⋙ dual R)) (j : J)
    (w : G.obj j) (x : s.pt) :
    descDual hd s ((d.ι.app j).hom w) x = coneDualHom s j x w :=
  LinearMap.congr_fun (LinearMap.congr_fun (congrArg Hom.hom (hd.fac (coconeOfDualCone s) j)) w) x

/-- **The dual of a colimit is the limit of the duals**: for a colimit cocone `V_j → V` of
`R`-modules, the restrictions `Hom_R(V, R) → Hom_R(V_j, R)` form a limit cone. -/
def isLimitMapConeDual {d : Cocone G} (hd : IsColimit d) : IsLimit ((dual R).mapCone d.op) where
  lift s := ModuleCat.ofHom (descDual hd s).flip
  fac s j := ModuleCat.hom_ext (LinearMap.ext fun x => LinearMap.ext fun w =>
    descDual_ι hd s j.unop w x)
  uniq s m hm := by
    have h : ModuleCat.ofHom (LinearMap.flip (M := s.pt) (N := d.pt) (P := R) m.hom) =
        hd.desc (coconeOfDualCone s) := hd.hom_ext fun j =>
      ModuleCat.hom_ext (LinearMap.ext fun w => LinearMap.ext fun y =>
        (LinearMap.congr_fun (LinearMap.congr_fun (congrArg Hom.hom (hm (op j))) y) w).trans
          (descDual_ι hd s j w y).symm)
    exact ModuleCat.hom_ext (LinearMap.ext fun x => LinearMap.ext fun v =>
      LinearMap.congr_fun (LinearMap.congr_fun (congrArg Hom.hom h) v) x)

/-- The maps of a colimit cocone jointly span its point, indexed by `Jᵒᵖ`. -/
theorem iSup_range_ι_unop_eq_top {d : Cocone G} (hd : IsColimit d) :
    ⨆ j : Jᵒᵖ, LinearMap.range (Hom.hom (A := G.obj j.unop) (B := d.pt) (d.ι.app j.unop)) = ⊤ :=
  eq_top_iff.2 ((iSup_range_ι_eq_top hd).ge.trans (iSup_le fun j => le_iSup_of_le (op j) le_rfl))

/-- **`Hom_R(colim V_j, R) ≅ lim W_j` is a homeomorphism** ([Stacks, Section 0G59]). Let
`V_j → V` be a colimit cocone of finitely generated `R`-modules and `α : Hom_R(V_j, R) ≅ W_j`
isomorphisms natural in `j`. Then the induced isomorphism `Hom_R(V, R) ≅ lim W_j`, for any limit
cone `c` of `W`, is a homeomorphism from `Module.Dual.limitTopology` to the limit topology, each
`W_j` discrete. -/
theorem isHomeomorph_conePointsIsoOfNatIso_dual {d : Cocone G} (hd : IsColimit d)
    [∀ j, Module.Finite R (G.obj j)] {W : Jᵒᵖ ⥤ ModuleCat.{u} R} {c : Cone W}
    (hc : IsLimit c) (α : G.op ⋙ dual R ≅ W) :
    letI := Module.Dual.limitTopology R d.pt
    letI := ⨅ j, TopologicalSpace.induced (fun x : c.pt => (c.π.app j).hom x) ⊥
    IsHomeomorph (X := Module.Dual R d.pt) (Y := c.pt)
      ((isLimitMapConeDual hd).conePointsIsoOfNatIso hc α).hom.hom := by
  let e : Module.Dual R d.pt ≃ₗ[R] c.pt :=
    ((isLimitMapConeDual hd).conePointsIsoOfNatIso hc α).toLinearEquiv
  let ι' : ∀ j : Jᵒᵖ, G.obj j.unop →ₗ[R] d.pt := fun j => (d.ι.app j.unop).hom
  let φ : ∀ j : Jᵒᵖ, Module.Dual R (G.obj j.unop) ≃ₗ[R] W.obj j := fun j =>
    (α.app j).toLinearEquiv
  have he : ∀ f j, (c.π.app j).hom (e f) = φ j (f ∘ₗ ι' j) := fun f j =>
    LinearMap.congr_fun (congrArg Hom.hom
      (IsLimit.conePointsIsoOfNatIso_hom_comp (isLimitMapConeDual hd) hc α j)) f
  exact Module.Dual.isHomeomorph_of_iSup_range_eq_top ι' (iSup_range_ι_unop_eq_top hd)
    (fun j (x : c.pt) => (c.π.app j).hom x) (fun j => φ j) (fun j => (φ j).injective)
    e.toEquiv he

/-- **`Hom_R(colim V_j, R) ≅ lim Hom_R(V_j, R)` is a homeomorphism** ([Stacks, Section 0G59]).
For a colimit cocone `V_j → V` of finitely generated `R`-modules and any limit cone `c` of the
duals, the comparison isomorphism `Hom_R(V, R) ≅ c.pt` is a homeomorphism from
`Module.Dual.limitTopology` to the limit topology. -/
theorem isHomeomorph_conePointUniqueUpToIso_dual {d : Cocone G} (hd : IsColimit d)
    [∀ j, Module.Finite R (G.obj j)] {c : Cone (G.op ⋙ dual R)} (hc : IsLimit c) :
    letI := Module.Dual.limitTopology R d.pt
    letI := ⨅ j, TopologicalSpace.induced (fun x : c.pt => (c.π.app j).hom x) ⊥
    IsHomeomorph (X := Module.Dual R d.pt) (Y := c.pt)
      ((isLimitMapConeDual hd).conePointUniqueUpToIso hc).hom.hom := by
  have h : ((isLimitMapConeDual hd).conePointsIsoOfNatIso hc (Iso.refl (G.op ⋙ dual R))).hom =
      ((isLimitMapConeDual hd).conePointUniqueUpToIso hc).hom :=
    hc.hom_ext fun j => by simp; rfl
  rw [← h]
  exact isHomeomorph_conePointsIsoOfNatIso_dual hd hc (Iso.refl _)

end ModuleCat

end
