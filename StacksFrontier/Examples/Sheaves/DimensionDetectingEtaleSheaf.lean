module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.LargeColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.CategoryTheory.Sites.CompatibleSheafification
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.RingTheory.Unramified.LocalStructure
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceThickening
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.Topology.Dimension.SpecializingSurjection

/-!
# An étale sheaf detecting the dimension of a scheme

For every natural number `n` there is a sheaf of abelian groups on a big étale site of schemes
whose group of sections over `X` is zero exactly when `\dim(X) < n`, and which does not change
along a thickening `X \subset X'`. It is the sheafification of the presheaf whose sections over
`X` are the `\mathbf{Z}/2`-valued functions on the strict specialization chains
`x_n \leadsto \cdots \leadsto x_0` of length `n` in `X`, with restriction along `f` given by
composing a chain with `f` and discarding the chains that `f` does not preserve.

Vanishing below dimension `n` holds because a scheme étale over `X` has dimension at most that
of `X`, so no chain of length `n` exists on any member of an étale covering. Nonvanishing in
dimension at least `n` holds because the generic points of a maximal chain of irreducible
closed subsets form a chain of length `n`, and the indicator function of the chains is a
section that stays nonzero in the sheafification, since the presheaf is separated: a chain
lifts along any étale covering because generalizations lift along a flat morphism, while an
étale morphism admits no specializations inside a fibre. Invariance along a thickening holds
because the chain presheaf only sees the underlying topological space, which a thickening does
not change, and because base change along a thickening is an equivalence on étale schemes, so
an étale covering of `X` is the restriction of one of `X'`.

## Main definitions

* `Stacks.Examples.DimensionSheaf.dimensionDetectingSheaf` is the sheaf.

## Main results

* `Stacks.Examples.DimensionSheaf.exists_sheaf_detecting_dimension` is the existence statement:
  for every big étale site and every `n` some sheaf of abelian groups has all three properties.
* `Stacks.Examples.DimensionSheaf.dimensionDetectingSheaf_subsingleton_of_dim_lt`,
  `Stacks.Examples.DimensionSheaf.dimensionDetectingSheaf_nontrivial_of_dim_ge` and
  `Stacks.Examples.DimensionSheaf.dimensionDetectingSheaf_map_isIso_of_isThickening` are the
  three properties for the construction above.

## Implementation notes

The site is `AlgebraicGeometry.BigEtaleSite`, so `\mathit{Sch}_{\acute{e}tale}` is a
size-bounded full subcategory of schemes together with a chosen class of étale coverings, and
`n` is universally quantified as in the source. A group being zero is stated as `Subsingleton`
and being nonzero as `Nontrivial` on its type of elements, and the equality `G(X) = G(X')`
along a thickening is stated as the canonical restriction map being an isomorphism. The chain
functions take values in `ZMod 2` as in the source, although any nonzero abelian group would
do. Sections of the chain presheaf over a scheme in universe `u` form a type in universe `u`,
and sheafification of an `AddCommGrpCat.{u}`-valued presheaf on a category whose homs live in
`Type (u + 1)` need not exist, so the presheaf is composed with
`AddCommGrpCat.uliftFunctor` and the sheaf takes values in `AddCommGrpCat.{u + 1}`.

## References

* [Stacks Project, Tag 05LE](https://stacks.math.columbia.edu/tag/05LE)
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open TopologicalSpace Order

universe u

namespace Stacks.Examples.DimensionSheaf

/-- A strict specialization chain of length `n` is a family `c 0, …, c n` of points, pairwise
distinct in consecutive positions, with each `c (i + 1)` specializing to `c i`. -/
private def IsStrictSpecializationChain {X : Type u} [TopologicalSpace X] (n : ℕ)
    (c : Fin (n + 1) → X) : Prop :=
  ∀ i : Fin n, c i.castSucc ≠ c i.succ ∧ c i.succ ⤳ c i.castSucc

/-- Specializations are preserved by a continuous map. -/
private theorem specializes_map_of_continuous {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X → Y) (hf : Continuous f) {x y : X} (h : x ⤳ y) :
    f x ⤳ f y :=
  h.map hf

/-- The group of `ZMod 2`-valued functions on the chains of length `n` in `X` which vanish on
every family that is not a strict specialization chain. -/
private def chainFunctionGroup (X : Scheme.{u}) (n : ℕ) :
    AddSubgroup ((Fin (n + 1) → X) → ZMod 2) where
  carrier := {a | ∀ c, ¬ IsStrictSpecializationChain n c → a c = 0}
  zero_mem' := by
    intro c hc
    simp
  add_mem' := by
    intro a b ha hb c hc
    simp [ha c hc, hb c hc]
  neg_mem' := by
    intro a ha c hc
    simp [ha c hc]

/-- A strict specialization chain of length `n` gives a chain of length `n` of irreducible
closed subsets, so it bounds the dimension from below. -/
private theorem dimension_ge_of_strictSpecializationChain (X : Scheme.{u}) (n : ℕ)
    (c : Fin (n + 1) → X) (hc : IsStrictSpecializationChain n c) :
    (n : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  let p : LTSeries (IrreducibleCloseds X) := {
    length := n
    toFun := fun i => IrreducibleCloseds.closureSingleton (c i)
    step := fun i => show
      IrreducibleCloseds.closureSingleton (c i.castSucc) <
        IrreducibleCloseds.closureSingleton (c i.succ) from by
      refine lt_of_le_of_ne ?_ ?_
      · rw [← SetLike.coe_subset_coe, IrreducibleCloseds.coe_closureSingleton,
          IrreducibleCloseds.coe_closureSingleton]
        exact closure_minimal
          (Set.singleton_subset_iff.mpr (hc i).2.mem_closure)
          isClosed_closure
      · intro heq
        have hclosure : closure ({c i.castSucc} : Set X) = closure {c i.succ} := by
          simpa only [IrreducibleCloseds.coe_closureSingleton] using
            congrArg (fun z : IrreducibleCloseds X => (z : Set X)) heq
        exact (hc i).1 (inseparable_iff_eq.mp (inseparable_iff_closure_eq.mpr hclosure))
  }
  simpa [topologicalKrullDim, p] using p.length_le_krullDim

/-- Below dimension `n` there are no strict specialization chains of length `n`, so the chain
group is zero. -/
private theorem chainFunctionGroup_subsingleton_of_dim_lt (X : Scheme.{u}) (n : ℕ)
    (hX : topologicalKrullDim X < (n : WithBot ℕ∞)) :
    Subsingleton (chainFunctionGroup X n) := by
  refine ⟨fun a b => Subtype.ext <| funext fun c => ?_⟩
  by_cases hc : IsStrictSpecializationChain n c
  · exact False.elim ((not_lt_of_ge (dimension_ge_of_strictSpecializationChain X n c hc)) hX)
  · rw [a.2 c hc, b.2 c hc]

/-- In dimension at least `n` the generic points of a chain of irreducible closed subsets form
a strict specialization chain of length `n`. -/
private theorem exists_strictSpecializationChain_of_dim_ge (X : Scheme.{u}) (n : ℕ)
    (hX : (n : WithBot ℕ∞) ≤ topologicalKrullDim X) :
    ∃ c : Fin (n + 1) → X, IsStrictSpecializationChain n c := by
  have hdim : (n : WithBot ℕ∞) ≤ krullDim (IrreducibleCloseds X) := by
    simpa [topologicalKrullDim] using hX
  obtain ⟨p, rfl⟩ := Order.le_krullDim_iff.mp hdim
  let c : Fin (p.length + 1) → X := fun i => (p.toFun i).isIrreducible'.genericPoint
  have hcgen : ∀ i, IsGenericPoint (c i) (p.toFun i).carrier := fun i =>
    (p.toFun i).isIrreducible'.isGenericPoint_genericPoint (p.toFun i).isClosed'
  refine ⟨c, fun i => ?_⟩
  have hne : c i.castSucc ≠ c i.succ := by
    intro heq
    have hcar : (p.toFun i.castSucc).carrier = (p.toFun i.succ).carrier := by
      rw [← (hcgen i.castSucc).def, ← (hcgen i.succ).def, heq]
    exact (ne_of_lt (p.step i)) (IrreducibleCloseds.ext hcar)
  exact ⟨hne, Topology.specializes_succ_castSucc_of_isGenericPoint p c hcgen i⟩

/-- The indicator function of the strict specialization chains of length `n`. -/
private noncomputable def chainFunctionIndicator {X : Scheme.{u}} (n : ℕ) :
    chainFunctionGroup X n := by
  classical
  exact ⟨fun d => if IsStrictSpecializationChain n d then 1 else 0, by
    intro d hd
    simp [hd]⟩

/-- The indicator function is nonzero as soon as one strict specialization chain exists. -/
private theorem chainFunctionIndicator_ne_zero {X : Scheme.{u}} (n : ℕ)
    (c : Fin (n + 1) → X) (hc : IsStrictSpecializationChain n c) :
    chainFunctionIndicator (X := X) n ≠ 0 := by
  classical
  intro h
  simpa [chainFunctionIndicator, hc] using congrFun (congrArg Subtype.val h) c

/-- A specialization chain lifts along a map along which generalizations lift, starting from a
prescribed point above its first member. -/
private alias exists_lift_chain_of_generalizingMap := Topology.exists_chain_of_generalizingMap

/-- An étale morphism of schemes is locally quasi-finite. -/
private theorem locallyQuasiFinite_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] :
    LocallyQuasiFinite f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  let g : Γ(Y, U) →+* Γ(X, V) := (f.appLE U V e).hom
  have hg : RingHom.Etale g := f.etale_appLE U.2 V.2 e
  let : Algebra Γ(Y, U) Γ(X, V) := g.toAlgebra
  let : Algebra.Etale Γ(Y, U) Γ(X, V) := RingHom.Etale.toAlgebra hg
  change @Algebra.QuasiFinite Γ(Y, U) Γ(X, V) _ _ g.toAlgebra
  exact inferInstance

/-- An étale morphism carries strict specialization chains to strict specialization chains: the
specializations are preserved by continuity, and the two consecutive points stay distinct
because an étale morphism has no specializations inside a fibre. -/
private theorem strictSpecializationChain_map_of_etale {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Etale f] (n : ℕ) (c : Fin (n + 1) → X)
    (hc : IsStrictSpecializationChain n c) :
    IsStrictSpecializationChain n (f.base.hom ∘ c) := by
  let : LocallyQuasiFinite f := locallyQuasiFinite_of_etale f
  intro i
  refine ⟨fun heq => ?_, specializes_map_of_continuous f.base.hom f.continuous (hc i).2⟩
  simp only [Function.comp_apply] at heq
  have hmem₁ : c i.castSucc ∈ f.base.hom ⁻¹' {f.base.hom (c i.castSucc)} := by simp
  have hmem₂ : c i.succ ∈ f.base.hom ⁻¹' {f.base.hom (c i.castSucc)} := by
    simp [heq]
  exact (hc i).1 ((f.isDiscrete_preimage_singleton (f.base.hom (c i.castSucc))).eq_of_specializes
    (hc i).2 hmem₂ hmem₁).symm

/-- A scheme étale over a scheme of dimension less than `n` has no strict specialization chain
of length `n`, so its chain group is zero. -/
private theorem chainFunctionGroup_subsingleton_of_etale_dim_lt
    (X Y : Scheme.{u}) (f : X ⟶ Y) [Etale f] (n : ℕ)
    (hY : topologicalKrullDim Y < (n : WithBot ℕ∞)) :
    Subsingleton (chainFunctionGroup X n) := by
  apply chainFunctionGroup_subsingleton_of_dim_lt
  by_contra hlt
  obtain ⟨c, hc⟩ := exists_strictSpecializationChain_of_dim_ge X n (le_of_not_gt hlt)
  exact (not_lt_of_ge (dimension_ge_of_strictSpecializationChain Y n (f.base.hom ∘ c)
    (strictSpecializationChain_map_of_etale f n c hc))) hY

/-- Every sieve in the topology of a big étale site is refined by one of the chosen covering
families. -/
private theorem exists_etale_cover_refinement (B : BigEtaleSite.{u})
    {X : B.Scheme} {S : Sieve X} (hS : S ∈ B.topology X) :
    ∃ E : PreZeroHypercover X, B.IsCovering ⟨X, E⟩ ∧ Sieve.generate E.presieve₀ ≤ S := by
  change B.precoverage.Saturate X S at hS
  induction hS with
  | of X R hR =>
      obtain ⟨E, hEq, hE⟩ := (B.mem_precoverage_iff (R := R)).mp hR
      exact ⟨E, hE, by rw [hEq]⟩
  | top X =>
      exact ⟨.singleton (𝟙 X), (B.coverings_isSite).1 (𝟙 X), le_top⟩
  | @pullback X S hS Y f ih =>
      obtain ⟨E, hE, hle⟩ := ih
      obtain ⟨P, π₁, π₂, hpb, hcov⟩ := (B.coverings_isSite).2.2 ⟨X, E⟩ hE Y f
      let E' : PreZeroHypercover Y := ⟨E.I₀, P, π₂⟩
      refine ⟨E', hcov, ?_⟩
      rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
      intro i
      change S (π₂ i ≫ f)
      rw [← (hpb i).w]
      exact Sieve.downward_closed S
        (hle _ (Sieve.le_generate E.presieve₀ _ _ (E.presieve₀_f i))) (π₁ i)
  | @transitive X S R hS hloc ihS ihloc =>
      obtain ⟨E, hE, hleE⟩ := ihS
      have hbase : ∀ i, S (E.f i) := fun i =>
        hleE _ (Sieve.le_generate E.presieve₀ _ _ (E.presieve₀_f i))
      choose F hF hleF using fun i => ihloc (hbase i)
      have hcomp := (B.coverings_isSite).2.1 ⟨X, E⟩ hE
        (fun i => ⟨E.X i, F i⟩) hF (fun _ => rfl)
      let E' := E.bind F
      have hE' : B.IsCovering ⟨X, E'⟩ := by
        simpa [E', PreZeroHypercover.bind, PreZeroHypercover.pushforward] using hcomp
      refine ⟨E', hE', ?_⟩
      rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
      rintro ⟨i, j⟩
      have hmem : R ((F i).f j ≫ E.f i) := hleF i _
        (Sieve.le_generate (F i).presieve₀ _ _ ((F i).presieve₀_f j))
      simpa [E', PreZeroHypercover.bind] using hmem

/-- A chosen covering family of a big étale site consists of étale morphisms and is jointly
surjective. -/
private theorem etaleCover_properties (B : BigEtaleSite.{u})
    {X : B.Scheme} (E : PreZeroHypercover X) (hE : B.IsCovering ⟨X, E⟩) :
    (∀ i, Etale ((B.inclusion).map (E.f i))) ∧
      (∀ x : (B.inclusion).obj X, ∃ i, ∃ y : (B.inclusion).obj (E.X i),
        ((B.inclusion).map (E.f i)).base y = x) := by
  have hEt : IsEtaleCovering ⟨X, E⟩ := BigEtaleSite.IsCovering.etale hE
  change (E.map B.inclusion).presieve₀ ∈ Scheme.etalePrecoverage _ at hEt
  have hprops := (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)
    (X := fun i => (B.inclusion).obj (E.X i))
    (f := fun i => (B.inclusion).map (E.f i))).mp hEt
  exact hprops.symm

/-- If a composite of two maps turns a chain into a strict specialization chain, then so does
the first of them. -/
private theorem chain_map_of_chain_comp {X Y Z : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (n : ℕ) (f : X → Y) (g : Y → Z)
    (hf : Continuous f) {c : Fin (n + 1) → X}
    (hc : IsStrictSpecializationChain n c)
    (hcomp : IsStrictSpecializationChain n (g ∘ f ∘ c)) :
    IsStrictSpecializationChain n (f ∘ c) := fun i =>
  ⟨fun hEq => (hcomp i).1 (congrArg g hEq), specializes_map_of_continuous f hf (hc i).2⟩

/-- Restriction of chain functions along a map of points: compose a chain with the map, and
discard the families which are not strict specialization chains. -/
private noncomputable def chainRestriction {X Y : Scheme.{u}} (n : ℕ) (f : X → Y) :
    chainFunctionGroup Y n →+ chainFunctionGroup X n where
  toFun := by
    classical
    exact fun a => ⟨fun c =>
      if IsStrictSpecializationChain n c then a.val (f ∘ c) else 0, by
        intro c hc
        simp [hc]⟩
  map_zero' := by
    classical
    ext c
    simp
  map_add' a b := by
    classical
    ext c
    by_cases hc : IsStrictSpecializationChain n c <;> simp [hc]

/-- The presheaf of chain functions of length `n` on a big étale site. -/
private noncomputable def dimensionChainPresheaf (B : BigEtaleSite.{u}) (n : ℕ) :
    B.Schemeᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj X := AddCommGrpCat.of (chainFunctionGroup ((B.inclusion).obj (unop X)) n)
  map f := AddCommGrpCat.ofHom
    (chainRestriction n ((B.inclusion).map f.unop))
  map_id X := by
    classical
    change AddCommGrpCat.ofHom (chainRestriction n (𝟙 ((B.inclusion).obj (unop X)))) = 𝟙 _
    ext a c
    by_cases hc : IsStrictSpecializationChain n c
    · simp [chainRestriction, hc]
    · simp [chainRestriction, hc, a.2 c hc]
  map_comp f g := by
    classical
    change AddCommGrpCat.ofHom
        (chainRestriction n ((B.inclusion).map (g.unop ≫ f.unop))) =
      AddCommGrpCat.ofHom (chainRestriction n ((B.inclusion).map f.unop)) ≫
        AddCommGrpCat.ofHom (chainRestriction n ((B.inclusion).map g.unop))
    ext a c
    by_cases hc : IsStrictSpecializationChain n c
    · by_cases hfc : IsStrictSpecializationChain n ((B.inclusion).map g.unop ∘ c)
      · have hfc' : IsStrictSpecializationChain n (⇑g.unop.hom ∘ c) := by
          simpa using hfc
        simp [chainRestriction, hc, hfc', Function.comp_assoc]
      · have hcomp : ¬ IsStrictSpecializationChain n
            ((B.inclusion).map (g.unop ≫ f.unop) ∘ c) := by
          intro hcomp
          have hmapped := chain_map_of_chain_comp n
            ((B.inclusion).map g.unop) ((B.inclusion).map f.unop)
            ((B.inclusion).map g.unop).continuous hc hcomp
          exact hfc (by simpa using hmapped)
        have hfc' : ¬ IsStrictSpecializationChain n (⇑g.unop.hom ∘ c) := by
          simpa using hfc
        have hcomp' : ¬ IsStrictSpecializationChain n
            (⇑f.unop.hom ∘ ⇑g.unop.hom ∘ c) := by
          simpa [Functor.map_comp, Function.comp_assoc] using hcomp
        have hz : a.1 ((⇑f.unop.hom ∘ ⇑g.unop.hom) ∘ c) = 0 :=
          a.2 _ (by simpa [Function.comp_assoc] using hcomp')
        have hz' : a.1
            ((⇑(TopCat.Hom.hom f.unop.hom.base) ∘
              ⇑(TopCat.Hom.hom g.unop.hom.base)) ∘ c) = 0 := by
          simpa [Function.comp_assoc] using hz
        simp [chainRestriction, hc, hfc', Function.comp_assoc]
        simpa [Function.comp_assoc] using hz'
    · simp [chainRestriction, hc]

/-- The chain presheaf is separated for a chosen covering family: a chain of the base lifts to
one of a member, because generalizations lift along the flat morphism and the lifted points
stay distinct. -/
private theorem chainFunctionGroup_eq_of_etale_cover (B : BigEtaleSite.{u}) (n : ℕ)
    {X : B.Scheme} (E : PreZeroHypercover X) (hE : B.IsCovering ⟨X, E⟩)
    (a b : chainFunctionGroup ((B.inclusion).obj X) n)
    (hab : ∀ i, chainRestriction n (E.f i).hom a = chainRestriction n (E.f i).hom b) :
    a = b := by
  classical
  obtain ⟨hetale, hsurj⟩ := etaleCover_properties B E hE
  apply Subtype.ext
  funext c
  by_cases hc : IsStrictSpecializationChain n c
  · obtain ⟨i, y, hy⟩ := hsurj (c 0)
    let f := (B.inclusion).map (E.f i)
    let : Etale f := hetale i
    obtain ⟨d, hd0, hd, hdspec⟩ := exists_lift_chain_of_generalizingMap
      f.base.hom (Flat.generalizingMap f) c (fun j => (hc j).2) y hy
    have hdc : IsStrictSpecializationChain n d := by
      intro j
      refine ⟨fun heq => ?_, hdspec j⟩
      have hmap := congrArg f.base.hom heq
      rw [hd j.castSucc, hd j.succ] at hmap
      exact (hc j).1 hmap
    have hval := congrFun (congrArg Subtype.val (hab i)) d
    have hcomp' : ⇑(E.f i).hom ∘ d = c := by
      simpa [f] using (funext hd : f.base.hom ∘ d = c)
    change (if IsStrictSpecializationChain n d then
      a.val ((E.f i).hom ∘ d) else 0) =
      (if IsStrictSpecializationChain n d then
        b.val ((E.f i).hom ∘ d) else 0) at hval
    simp only [hdc, ite_true] at hval
    rwa [hcomp'] at hval
  · rw [a.2 c hc, b.2 c hc]

/-- The chain presheaf is separated for the topology of a big étale site. -/
private theorem dimensionChainPresheaf_separated (B : BigEtaleSite.{u}) (n : ℕ)
    {X : B.Scheme} (S : Sieve X) (hS : S ∈ B.topology X)
    (a b : ToType ((dimensionChainPresheaf B n).obj (op X)))
    (hab : ∀ ⦃Y : B.Scheme⦄ (f : Y ⟶ X) (_hf : S f),
      (dimensionChainPresheaf B n).map f.op a =
        (dimensionChainPresheaf B n).map f.op b) :
    a = b := by
  obtain ⟨E, hE, hle⟩ := exists_etale_cover_refinement B hS
  exact chainFunctionGroup_eq_of_etale_cover B n E hE a b fun i =>
    hab (E.f i) (hle _ (Sieve.le_generate E.presieve₀ _ _ (E.presieve₀_f i)))

/-- Being a strict specialization chain is invariant under a homeomorphism. -/
private theorem isStrictSpecializationChain_homeomorph_iff {X Y : Scheme.{u}}
    (e : X ≃ₜ Y) (n : ℕ) (c : Fin (n + 1) → X) :
    IsStrictSpecializationChain n c ↔
      IsStrictSpecializationChain n (e ∘ c) := by
  refine ⟨fun hc i => ⟨fun h => (hc i).1 (e.injective (by simpa using h)),
    specializes_map_of_continuous e e.continuous (hc i).2⟩, fun hc i => ⟨fun h => ?_, ?_⟩⟩
  · exact (hc i).1 (by simpa using congrArg e h)
  · simpa using specializes_map_of_continuous e.symm e.symm.continuous (hc i).2

/-- Restriction of chain functions along a homeomorphism is inverted by restriction along the
inverse homeomorphism. -/
private theorem chainRestriction_homeomorph_left {X Y : Scheme.{u}} (n : ℕ)
    (e : X ≃ₜ Y) (a : chainFunctionGroup Y n) :
    chainRestriction n e.symm (chainRestriction n e a) = a := by
  classical
  apply Subtype.ext
  funext c
  by_cases hc : IsStrictSpecializationChain n c
  · have hc' : IsStrictSpecializationChain n (e.symm ∘ c) :=
      (isStrictSpecializationChain_homeomorph_iff e.symm n c).1 hc
    change (if IsStrictSpecializationChain n c then
      (chainRestriction n e a).val (e.symm ∘ c) else 0) = a.val c
    simp only [hc, ite_true]
    change (if IsStrictSpecializationChain n (e.symm ∘ c) then
      a.val (e ∘ (e.symm ∘ c)) else 0) = a.val c
    simp only [hc', ite_true]
    rw [show e ∘ (e.symm ∘ c) = c from funext fun i => by simp]
  · simp [chainRestriction, hc, a.2 c hc]

/-- Restriction of chain functions along the inverse of a homeomorphism is inverted by
restriction along the homeomorphism. -/
private theorem chainRestriction_homeomorph_right {X Y : Scheme.{u}} (n : ℕ)
    (e : X ≃ₜ Y) (a : chainFunctionGroup X n) :
    chainRestriction n e (chainRestriction n e.symm a) = a :=
  chainRestriction_homeomorph_left n e.symm a

/-- Restriction of chain functions along a homeomorphism is bijective. -/
private theorem chainRestriction_bijective_of_homeomorph {X Y : Scheme.{u}}
    (n : ℕ) (e : X ≃ₜ Y) : Function.Bijective (chainRestriction n e) :=
  ⟨Function.LeftInverse.injective (chainRestriction_homeomorph_left n e),
    Function.RightInverse.surjective (chainRestriction_homeomorph_right n e)⟩

/-- A thickening is a homeomorphism on points, so restriction of chain functions along it is an
isomorphism already at the level of presheaves. -/
private theorem dimensionChainPresheaf_map_isIso_of_isThickening
    (B : BigEtaleSite.{u}) (n : ℕ) {X X' : B.Scheme} (i : X ⟶ X')
    (hi : Stacks.Thickenings.IsThickening ((B.inclusion).map i)) :
    IsIso ((dimensionChainPresheaf B n).map i.op) := by
  let f := (B.inclusion).map i
  let : IsClosedImmersion f := hi.1
  have hf : IsHomeomorph f.base.hom := by
    rw [isHomeomorph_iff_isEmbedding_surjective]
    exact ⟨f.isClosedEmbedding.isEmbedding, hi.2⟩
  let e : ((B.inclusion).obj X) ≃ₜ ((B.inclusion).obj X') := hf.homeomorph f.base.hom
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (chainRestriction n e)
  exact chainRestriction_bijective_of_homeomorph n e

/-- The chain presheaf lifted to `AddCommGrpCat.{u + 1}`, its sheafification, and the
comparison map together with the properties of sheafification that are used below. -/
private structure DimensionSheafData (B : BigEtaleSite.{u}) (n : ℕ) where
  /-- The universe-lifted chain presheaf. -/
  presheaf : B.Schemeᵒᵖ ⥤ AddCommGrpCat.{u + 1}
  /-- Its sheafification. -/
  sheafification : B.Schemeᵒᵖ ⥤ AddCommGrpCat.{u + 1}
  /-- The comparison map to the sheafification. -/
  unit : presheaf ⟶ sheafification
  /-- The sheafification is a sheaf. -/
  isSheaf : Presheaf.IsSheaf B.topology sheafification
  /-- The comparison map is locally surjective. -/
  locallySurjective : Presheaf.IsLocallySurjective B.topology unit
  /-- The comparison map is locally injective. -/
  locallyInjective : Presheaf.IsLocallyInjective B.topology unit

/-- Sheafification of the universe-lifted chain presheaf, with its comparison map. -/
private noncomputable def dimensionSheafData (B : BigEtaleSite.{u}) (n : ℕ) :
    DimensionSheafData B n := by
  letI : HasWeakSheafify B.topology AddCommGrpCat.{u + 1} := inferInstance
  let P : B.Schemeᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    dimensionChainPresheaf B n ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}
  let T : (B.Schemeᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
      Sheaf B.topology AddCommGrpCat.{u + 1} := presheafToSheaf B.topology _
  let sh := T.obj P
  let F := sh.obj
  let adj := sheafificationAdjunction B.topology AddCommGrpCat.{u + 1}
  have hloc : Presheaf.IsLocallySurjective B.topology (adj.unit.app P) :=
    Presheaf.isLocallySurjective_toSheafify' (J := B.topology) P
  have hlinj : Presheaf.IsLocallyInjective B.topology (adj.unit.app P) :=
    Presheaf.isLocallyInjective_toSheafify' (J := B.topology) P
  exact ⟨P, F, adj.unit.app P, sh.property, hloc, hlinj⟩

/-- The comparison map to the sheafification is injective on sections, because the chain
presheaf is separated. -/
private theorem dimensionSheafData_unit_injective (B : BigEtaleSite.{u}) (n : ℕ)
    (X : B.Scheme) (a b : ToType ((dimensionSheafData B n).presheaf.obj (op X)))
    (h : (dimensionSheafData B n).unit.app (op X) a =
      (dimensionSheafData B n).unit.app (op X) b) :
    a = b := by
  let D := dimensionSheafData B n
  let : Presheaf.IsLocallyInjective B.topology D.unit := D.locallyInjective
  have hS : Presheaf.equalizerSieve a b ∈ B.topology X :=
    Presheaf.equalizerSieve_mem B.topology D.unit a b h
  have hraw : ULift.down a = ULift.down b :=
    dimensionChainPresheaf_separated B n (Presheaf.equalizerSieve a b) hS
      (ULift.down a) (ULift.down b) (by
        intro Y f hf
        dsimp [D, dimensionSheafData, DimensionSheafData.presheaf] at hf
        change ULift.up ((dimensionChainPresheaf B n).map f.op (ULift.down a)) =
          ULift.up ((dimensionChainPresheaf B n).map f.op (ULift.down b)) at hf
        exact ULift.up_injective hf)
  exact congrArg ULift.up hraw

/-- A sheaf of abelian groups on a big étale site detecting dimension `n`: the sheafification of
the presheaf of `ZMod 2`-valued functions on the strict specialization chains of length `n`. -/
public noncomputable def dimensionDetectingSheaf (B : BigEtaleSite.{u}) (n : ℕ) :
    Sheaf B.topology AddCommGrpCat.{u + 1} := by
  let D := dimensionSheafData B n
  exact ⟨D.sheafification, D.isSheaf⟩

/-- Two sections of a sheaf agree if they agree on every member of a chosen covering family. -/
private theorem eq_of_etale_cover_map_eq (B : BigEtaleSite.{u}) {X : B.Scheme}
    {E : PreZeroHypercover X} (hE : B.IsCovering ⟨X, E⟩) {F : B.Schemeᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    (hF : Presheaf.IsSheaf B.topology F) (s t : ToType (F.obj (op X)))
    (h : ∀ i, F.map (E.f i).op s = F.map (E.f i).op t) : s = t := by
  have hcover : Sieve.generate E.presieve₀ ∈ B.topology X :=
    B.precoverage.generate_mem_toGrothendieck ⟨E, rfl, hE⟩
  have hle : Sieve.generate E.presieve₀ ≤ Presheaf.equalizerSieve s t := by
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    exact h
  exact hF.isSeparated X _ (B.topology.superset_covering hle hcover) s t (fun Y f hf => hf)

/-- Sections of `dimensionDetectingSheaf B n` vanish on schemes of dimension less than `n`. -/
public theorem dimensionDetectingSheaf_subsingleton_of_dim_lt
    (B : BigEtaleSite.{u}) (n : ℕ) (X : B.Scheme)
    (hX : topologicalKrullDim ((B.inclusion).obj X) < (n : WithBot ℕ∞)) :
    Subsingleton ((dimensionDetectingSheaf B n).obj.obj (Opposite.op X)) := by
  let D := dimensionSheafData B n
  let P := D.presheaf
  let F := D.sheafification
  let : Presheaf.IsLocallySurjective B.topology D.unit := D.locallySurjective
  change Subsingleton (ToType (F.obj (op X)))
  have hvanish : ∀ s : ToType (F.obj (op X)), s = 0 := by
    intro s
    have himage : Presheaf.imageSieve D.unit (U := X) s ∈ B.topology X :=
      Presheaf.imageSieve_mem (J := B.topology) (f := D.unit) (U := op X) s
    obtain ⟨E, hE, hle⟩ := exists_etale_cover_refinement B himage
    obtain ⟨hetale, _hsurj⟩ := etaleCover_properties B E hE
    have hzero (i : E.I₀) : F.map (E.f i).op s = 0 := by
      have hleg : Presheaf.imageSieve D.unit (U := X) s (E.f i) :=
        hle _ (Sieve.le_generate E.presieve₀ _ _ (E.presieve₀_f i))
      obtain ⟨t, ht⟩ := hleg
      let : Etale ((B.inclusion).map (E.f i)) := hetale i
      have hsubBase : Subsingleton
          (chainFunctionGroup ((B.inclusion).obj (E.X i)) n) :=
        chainFunctionGroup_subsingleton_of_etale_dim_lt
          ((B.inclusion).obj (E.X i)) ((B.inclusion).obj X)
          ((B.inclusion).map (E.f i)) n hX
      have hsub : Subsingleton (ToType (P.obj (op (E.X i)))) := by
        change Subsingleton (ULift (chainFunctionGroup ((B.inclusion).obj (E.X i)) n))
        infer_instance
      rw [← ht, Subsingleton.elim t 0]
      simp
    exact eq_of_etale_cover_map_eq B hE D.isSheaf s 0 fun i => by rw [hzero i, map_zero]
  exact ⟨fun s t => by rw [hvanish s, hvanish t]⟩

/-- Sections of `dimensionDetectingSheaf B n` are nonzero on schemes of dimension at least
`n`. -/
public theorem dimensionDetectingSheaf_nontrivial_of_dim_ge
    (B : BigEtaleSite.{u}) (n : ℕ) (X : B.Scheme)
    (hX : (n : WithBot ℕ∞) ≤ topologicalKrullDim ((B.inclusion).obj X)) :
    Nontrivial ((dimensionDetectingSheaf B n).obj.obj (Opposite.op X)) := by
  let D := dimensionSheafData B n
  let P := D.presheaf
  let F := D.sheafification
  let : Presheaf.IsLocallyInjective B.topology D.unit := D.locallyInjective
  change Nontrivial (ToType (F.obj (op X)))
  obtain ⟨c, hc⟩ := exists_strictSpecializationChain_of_dim_ge
    ((B.inclusion).obj X) n hX
  let a : chainFunctionGroup ((B.inclusion).obj X) n := chainFunctionIndicator n
  have ha : a ≠ 0 := chainFunctionIndicator_ne_zero n c hc
  let aP : ToType (P.obj (op X)) := ULift.up a
  let s : ToType (F.obj (op X)) := D.unit.app (op X) aP
  have hs : s ≠ 0 := by
    intro hs
    have hunit : D.unit.app (op X) aP = D.unit.app (op X) 0 := by simpa [s] using hs
    exact ha (ULift.up_injective (dimensionSheafData_unit_injective B n X aP 0 hunit))
  exact ⟨⟨s, 0, hs⟩⟩

/-- Restriction along a thickening is an isomorphism on the universe-lifted chain presheaf. -/
private theorem dimensionSheafData_presheaf_map_isIso_of_isThickening
    (B : BigEtaleSite.{u}) (n : ℕ) {X X' : B.Scheme} (i : X ⟶ X')
    (hi : Stacks.Thickenings.IsThickening ((B.inclusion).map i)) :
    IsIso ((dimensionSheafData B n).presheaf.map i.op) := by
  dsimp [dimensionSheafData, DimensionSheafData.presheaf]
  let : IsIso ((dimensionChainPresheaf B n).map i.op) :=
    dimensionChainPresheaf_map_isIso_of_isThickening B n i hi
  infer_instance

/-- Thickenings are stable under base change. -/
private theorem dimensionSheafData_baseChange_isThickening
    (B : BigEtaleSite.{u}) {W X Y Z : B.Scheme} (p : W ⟶ X) (q : W ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (hpb : IsPullback p q f g)
    (hg : Stacks.Thickenings.IsThickening ((B.inclusion).map g)) :
    Stacks.Thickenings.IsThickening ((B.inclusion).map p) := by
  have hpb' : IsPullback ((B.inclusion).map p) ((B.inclusion).map q)
      ((B.inclusion).map f) ((B.inclusion).map g) := hpb.map B.inclusion
  have hc : IsClosedImmersion ((B.inclusion).map p) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsClosedImmersion) hpb'.flip hg.1
  have hs : AlgebraicGeometry.Surjective ((B.inclusion).map p) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.Surjective) hpb'.flip ⟨hg.2⟩
  exact ⟨hc, hs.surj⟩

/-- Restriction along a thickening is injective on sections of the sheafification: an étale
covering of the closed subscheme is refined by the base change of one of the ambient scheme,
and on each member the two sections agree because the presheaf restriction is an
isomorphism. -/
private theorem dimensionSheafData_map_injective_of_isThickening
    (B : BigEtaleSite.{u}) (n : ℕ) {X X' : B.Scheme} (i : X ⟶ X')
    (hi : Stacks.Thickenings.IsThickening ((B.inclusion).map i)) :
    Function.Injective ((dimensionSheafData B n).sheafification.map i.op) := by
  let D := dimensionSheafData B n
  let P := D.presheaf
  let F := D.sheafification
  let : Presheaf.IsLocallySurjective B.topology D.unit := D.locallySurjective
  intro s t hst
  let S := Presheaf.imageSieve D.unit s ⊓ Presheaf.imageSieve D.unit t
  have hS : S ∈ B.topology X' :=
    B.topology.intersection_covering
      (Presheaf.imageSieve_mem B.topology D.unit s)
      (Presheaf.imageSieve_mem B.topology D.unit t)
  obtain ⟨E, hE, hle⟩ := exists_etale_cover_refinement B hS
  obtain ⟨Q, π₁, π₂, hpb, hcov⟩ :=
    B.coverings_isSite.2.2 ⟨X', E⟩ hE X i
  have heq (k : E.I₀) : F.map (E.f k).op s = F.map (E.f k).op t := by
    let W := Q k
    let p := π₂ k
    let j := π₁ k
    have hp := congrArg (fun z => F.map p.op z) hst
    change F.map p.op (F.map i.op s) = F.map p.op (F.map i.op t) at hp
    have hcomm : p ≫ i = j ≫ E.f k := (hpb k).w.symm
    have htarget :
        F.map j.op (F.map (E.f k).op s) =
          F.map j.op (F.map (E.f k).op t) := by
      simpa only [← Functor.map_comp_apply, ← op_comp, hcomm] using hp
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hle _ (Sieve.le_generate E.presieve₀ _ _ (E.presieve₀_f k))
    have hthick : Stacks.Thickenings.IsThickening ((B.inclusion).map j) :=
      dimensionSheafData_baseChange_isThickening B j p (E.f k) i (hpb k) hi
    have hPiso := dimensionSheafData_presheaf_map_isIso_of_isThickening B n j hthick
    have hunit : D.unit.app (op W)
        (P.map j.op a) = D.unit.app (op W) (P.map j.op b) := by
      calc
        D.unit.app (op W) (P.map j.op a) =
          F.map j.op (D.unit.app (op (E.X k)) a) := by
            rw [← NatTrans.naturality_apply]
        _ = F.map j.op (F.map (E.f k).op s) := by rw [ha]
        _ = F.map j.op (F.map (E.f k).op t) := htarget
        _ = F.map j.op (D.unit.app (op (E.X k)) b) := by rw [← hb]
        _ = D.unit.app (op W) (P.map j.op b) := by rw [NatTrans.naturality_apply]
    have hab := dimensionSheafData_unit_injective B n W _ _ hunit
    rw [ConcreteCategory.isIso_iff_bijective] at hPiso
    rw [← ha, ← hb, hPiso.1 hab]
  exact eq_of_etale_cover_map_eq B hE D.isSheaf s t heq

/-- An étale covering family of a big étale site generates a covering sieve. -/
private theorem etaleFamily_mem_topology (B : BigEtaleSite.{u})
    {X : B.Scheme} (E : PreZeroHypercover X)
    (hE : IsEtaleCovering ⟨X, E⟩) :
    Sieve.ofArrows E.X E.f ∈ B.topology X := by
  obtain ⟨V, hV, hcomb⟩ := B.exists_covering_rep ⟨X, E⟩ hE
  rcases hcomb with ⟨hXV, hEq⟩
  cases hXV
  have hpres := PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hEq
  change Sieve.generate E.presieve₀ ∈ B.topology V.1
  rw [hpres]
  exact B.precoverage.generate_mem_toGrothendieck ⟨V.2, rfl, hV⟩

/-- **Topological invariance of the étale site** along a thickening: base change is an
equivalence from the schemes étale over the ambient scheme to the schemes étale over the closed
subscheme. -/
private noncomputable def thickeningEtaleEquivalence {X X' : Scheme.{u}}
    (i : X ⟶ X') (hi : Stacks.Thickenings.IsThickening i) : X'.Etale ≌ X.Etale := by
  letI : IsClosedImmersion i := hi.1
  letI : MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u}) i :=
    ⟨fun _ _ ↦ inferInstance⟩
  letI : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) i :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  let F : X'.Etale ⥤ X.Etale :=
    MorphismProperty.Over.pullback (@Etale : MorphismProperty Scheme.{u}) ⊤ i
  letI : F.IsEquivalence :=
    Stacks.Etale.etalePullback_isEquivalence_of_surjective_isClosedImmersion i hi.2
  exact F.asEquivalence

/-- The scheme étale over the ambient scheme whose base change along a thickening is a given
scheme étale over the closed subscheme. -/
private noncomputable def thickeningEtaleLift {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (hi : Stacks.Thickenings.IsThickening i) (f : Y ⟶ X) [Etale f] : X'.Etale :=
  (thickeningEtaleEquivalence i hi).inverse.obj (Scheme.Etale.mk f)

/-- The base change of `thickeningEtaleLift i hi f` is `f`. -/
private noncomputable def thickeningEtaleLift_pullbackIso {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (hi : Stacks.Thickenings.IsThickening i) (f : Y ⟶ X) [Etale f] :
    (thickeningEtaleEquivalence i hi).functor.obj (thickeningEtaleLift i hi f) ≅
      Scheme.Etale.mk f :=
  (thickeningEtaleEquivalence i hi).counitIso.app (Scheme.Etale.mk f)

/-- The family of lifts along a thickening of the members of a chosen covering family. -/
private noncomputable def affineEtaleLiftFamily (B : BigEtaleSite.{u})
    {X X' : B.Scheme} (i : X ⟶ X')
    (hi : Stacks.Thickenings.IsThickening ((B.inclusion).map i))
    (E : PreZeroHypercover X) (hE : B.IsCovering ⟨X, E⟩) :
    E.I₀ → ((B.inclusion).obj X').Etale := fun k => by
  letI : Etale ((B.inclusion).map (E.f k)) := (etaleCover_properties B E hE).1 k
  exact thickeningEtaleLift ((B.inclusion).map i) hi ((B.inclusion).map (E.f k))

/-- The family of affine opens of the lifts along a thickening of the members of a chosen
covering family, as a family in the big étale site: each affine open is of finite type over the
ambient scheme, hence below the size cutoff. -/
private noncomputable def affineEtaleLiftHypercover (B : BigEtaleSite.{u})
    {X X' : B.Scheme} (i : X ⟶ X')
    (hi : Stacks.Thickenings.IsThickening ((B.inclusion).map i))
    (E : PreZeroHypercover X) (hE : B.IsCovering ⟨X, E⟩) : PreZeroHypercover X' := by
  let V := affineEtaleLiftFamily B i hi E hE
  let T : ∀ k : E.I₀, Scheme.{u} := fun k => (V k).left
  let I := Σ k : E.I₀, (T k).affineOpens
  have hsize (j : I) : (↑j.2.1 : Scheme.{u}).size < B.cutoff :=
    (Scheme.size_le_of_locallyOfFiniteType
      (j.2.1.ι ≫ (V j.1).hom)).trans_lt X'.property
  exact ⟨I, fun j => ⟨(↑j.2.1 : Scheme.{u}), hsize j⟩,
    fun j => ObjectProperty.homMk (j.2.1.ι ≫ (V j.1).hom)⟩

/-- The lifted family is an étale covering of the ambient scheme: it is étale because the lifts
are and affine opens are, and jointly surjective because a thickening is surjective on points
and the original family covers the closed subscheme. -/
private theorem affineEtaleLiftHypercover_isEtaleCovering (B : BigEtaleSite.{u})
    {X X' : B.Scheme} (i : X ⟶ X')
    (hi : Stacks.Thickenings.IsThickening ((B.inclusion).map i))
    (E : PreZeroHypercover X) (hE : B.IsCovering ⟨X, E⟩) :
    IsEtaleCovering ⟨X', affineEtaleLiftHypercover B i hi E hE⟩ := by
  classical
  let V := affineEtaleLiftFamily B i hi E hE
  let T : ∀ k : E.I₀, Scheme.{u} := fun k => (V k).left
  let A := affineEtaleLiftHypercover B i hi E hE
  change (A.map B.inclusion).presieve₀ ∈ _
  rw [PreZeroHypercover.presieve₀_map]
  rw [Presieve.map_ofArrows]
  apply (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).mpr
  constructor
  · intro x'
    obtain ⟨x, hx⟩ := hi.2 x'
    obtain ⟨k, y, hy⟩ := (etaleCover_properties B E hE).2 x
    let : Etale ((B.inclusion).map (E.f k)) := (etaleCover_properties B E hE).1 k
    let e := thickeningEtaleLift_pullbackIso ((B.inclusion).map i) hi
      ((B.inclusion).map (E.f k))
    let Q := ((thickeningEtaleEquivalence ((B.inclusion).map i) hi).functor.obj
      (V k)).left
    let yP : Q := e.inv.left.base y
    let z := (pullback.fst (V k).hom i.hom).base yP
    obtain ⟨U, hzU⟩ : ∃ U : (T k).affineOpens, z ∈ (U : Opens (T k)) := by
      have hmem : z ∈ (⊤ : Opens (T k)) := Set.mem_univ _
      rw [← iSup_affineOpens_eq_top (T k)] at hmem
      exact Opens.mem_iSup.mp hmem
    refine ⟨⟨k, U⟩, ⟨⟨z, hzU⟩, ?_⟩⟩
    change (V k).hom.base (U.1.ι.base ⟨z, hzU⟩) = x'
    have hpoint : e.hom.left.base.hom (e.inv.left.base.hom y) = y := by
      have hcomp : e.inv.left ≫ e.hom.left = 𝟙 _ := congrArg (fun g => g.left) e.inv_hom_id
      have hcompBase : e.inv.left.base ≫ e.hom.left.base = 𝟙 _ := by
        simpa only [Scheme.Hom.comp_base, Scheme.Hom.id_base] using
          congrArg (fun f : Scheme.Hom _ _ => f.base) hcomp
      exact congrArg (fun f => f.hom y) hcompBase
    have hcomm : (V k).hom.base.hom
        ((pullback.fst (V k).hom ((B.inclusion).map i)).base.hom yP) =
        ((B.inclusion).map i).base.hom
          ((pullback.snd (V k).hom ((B.inclusion).map i)).base.hom yP) := by
      have hpull : pullback.fst (V k).hom ((B.inclusion).map i) ≫ (V k).hom =
          pullback.snd (V k).hom ((B.inclusion).map i) ≫ (B.inclusion).map i :=
        pullback.condition
      have hbase : (pullback.fst (V k).hom ((B.inclusion).map i)).base ≫
          (V k).hom.base = (pullback.snd (V k).hom ((B.inclusion).map i)).base ≫
            ((B.inclusion).map i).base := by
        simpa only [Scheme.Hom.comp_base] using
          congrArg (fun f : Scheme.Hom _ _ => f.base) hpull
      exact congrArg (fun f => f.hom yP) hbase
    rw [show U.1.ι.base ⟨z, hzU⟩ = z by rfl]
    change (V k).hom.base ((pullback.fst (V k).hom
      ((B.inclusion).map i)).base yP) = x'
    rw [hcomm]
    have he : (e.hom.left ≫ (B.inclusion).map (E.f k)).base yP =
        (pullback.snd (V k).hom ((B.inclusion).map i)).base yP :=
      congrArg (fun f : Scheme.Hom _ _ => f.base yP) e.hom.w
    calc
      _ = ((B.inclusion).map i) ((e.hom.left ≫ (B.inclusion).map (E.f k)) yP) := by
            simpa only [Scheme.Hom.comp_apply] using congrArg ((B.inclusion).map i) he.symm
      _ = ((B.inclusion).map i) (((B.inclusion).map (E.f k)) ((e.hom.left) yP)) :=
            congrArg ((B.inclusion).map i)
              (Scheme.Hom.comp_apply e.hom.left ((B.inclusion).map (E.f k)) yP)
      _ = ((B.inclusion).map i).base x := by
            have hpoint' : e.hom.left.base.hom yP = y := by simpa [yP] using hpoint
            rw [hpoint', hy]
      _ = x' := hx
  · intro j
    change Etale (j.2.1.ι ≫ (V j.1).hom)
    let : Etale j.2.1.ι := by infer_instance
    infer_instance

/-- Restriction along a thickening is surjective on sections of the sheafification: a section
over the closed subscheme is given on an étale covering, the covering lifts to the ambient
scheme, the local sections transport along the lifts because the presheaf restriction is an
isomorphism, and they glue because restriction along a thickening is injective. -/
private theorem dimensionSheafData_map_surjective_of_isThickening
    (B : BigEtaleSite.{u}) (n : ℕ) {X X' : B.Scheme} (i : X ⟶ X')
    (hi : Stacks.Thickenings.IsThickening ((B.inclusion).map i)) :
    Function.Surjective ((dimensionSheafData B n).sheafification.map i.op) := by
  classical
  let D := dimensionSheafData B n
  let P := D.presheaf
  let F := D.sheafification
  let η := D.unit
  let : Presheaf.IsLocallySurjective B.topology η := D.locallySurjective
  intro s
  have himage : Presheaf.imageSieve η s ∈ B.topology X :=
    Presheaf.imageSieve_mem (J := B.topology) (f := η) (U := op X) s
  obtain ⟨E, hE, hle⟩ := exists_etale_cover_refinement B himage
  have hlocal : ∀ k : E.I₀, ∃ a : ToType (P.obj (op (E.X k))),
      η.app (op (E.X k)) a = F.map (E.f k).op s := fun k =>
    hle _ (Sieve.le_generate E.presieve₀ _ _ (E.presieve₀_f k))
  choose a ha using hlocal
  let V := affineEtaleLiftFamily B i hi E hE
  let A := affineEtaleLiftHypercover B i hi E hE
  have hA : IsEtaleCovering ⟨X', A⟩ :=
    affineEtaleLiftHypercover_isEtaleCovering B i hi E hE
  have hcoverA : Sieve.ofArrows A.X A.f ∈ B.topology X' :=
    etaleFamily_mem_topology B A hA
  let : PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance
  let Q : A.I₀ → B.Scheme := fun j => pullback (A.f j) i
  let q₁ : ∀ j, Q j ⟶ A.X j := fun j => pullback.fst (A.f j) i
  let q₂ : ∀ j, Q j ⟶ X := fun j => pullback.snd (A.f j) i
  have hpb (j : A.I₀) : IsPullback (q₁ j) (q₂ j) (A.f j) i :=
    IsPullback.of_hasPullback _ _
  have hthick (j : A.I₀) : Stacks.Thickenings.IsThickening ((B.inclusion).map (q₁ j)) :=
    dimensionSheafData_baseChange_isThickening B (q₁ j) (q₂ j) (A.f j) i
      (hpb j) hi
  have hPiso (j : A.I₀) : IsIso (P.map (q₁ j).op) :=
    dimensionSheafData_presheaf_map_isIso_of_isThickening B n (q₁ j) (hthick j)
  let m : ∀ j : A.I₀, (B.inclusion).obj (A.X j) ⟶ (V j.1).left :=
    fun j => j.2.1.ι
  have hm (j : A.I₀) : (B.inclusion).map (A.f j) = m j ≫ (V j.1).hom := rfl
  let Qk : ∀ k : E.I₀, ((B.inclusion).obj X).Etale := fun k => by
    let : Etale ((B.inclusion).map (E.f k)) := (etaleCover_properties B E hE).1 k
    exact (thickeningEtaleEquivalence ((B.inclusion).map i) hi).functor.obj (V k)
  let u : ∀ j : A.I₀, (B.inclusion).obj (Q j) ⟶ (Qk j.1).left := fun j =>
    pullback.lift (((B.inclusion).map (q₁ j)) ≫ m j)
      ((B.inclusion).map (q₂ j)) (by
        calc
          (((B.inclusion).map (q₁ j)) ≫ m j) ≫ (V j.1).hom =
              ((B.inclusion).map (q₁ j)) ≫ ((B.inclusion).map (A.f j)) := by
                rw [Category.assoc, hm j]
          _ = ((B.inclusion).map (q₂ j)) ≫ ((B.inclusion).map i) := by
                simpa only [Functor.map_comp] using congrArg (B.inclusion).map (hpb j).w)
  let ρ : ∀ j : A.I₀, Q j ⟶ E.X j.1 := fun j => by
    let k := j.1
    let : Etale ((B.inclusion).map (E.f k)) := (etaleCover_properties B E hE).1 k
    let e := thickeningEtaleLift_pullbackIso ((B.inclusion).map i) hi
      ((B.inclusion).map (E.f k))
    exact ObjectProperty.homMk (u j ≫ e.hom.left)
  have hρ (j : A.I₀) : ρ j ≫ E.f j.1 = q₂ j := by
    apply (B.inclusion).map_injective
    let k := j.1
    let : Etale ((B.inclusion).map (E.f k)) := (etaleCover_properties B E hE).1 k
    let e := thickeningEtaleLift_pullbackIso ((B.inclusion).map i) hi
      ((B.inclusion).map (E.f k))
    have he : e.hom.left ≫ (B.inclusion).map (E.f k) =
        pullback.snd (V k).hom ((B.inclusion).map i) := by
      change e.hom.left ≫ (Scheme.Etale.mk ((B.inclusion).map (E.f k))).hom = _
      exact e.hom.w
    change (u j ≫ e.hom.left) ≫ (B.inclusion).map (E.f k) = (B.inclusion).map (q₂ j)
    calc
      (u j ≫ e.hom.left) ≫ (B.inclusion).map (E.f k) =
          u j ≫ (e.hom.left ≫ (B.inclusion).map (E.f k)) := Category.assoc _ _ _
      _ = u j ≫ pullback.snd (V k).hom ((B.inclusion).map i) :=
            congrArg (fun f => u j ≫ f) he
      _ = (B.inclusion).map (q₂ j) := pullback.lift_snd _ _ _
  let b : ∀ j : A.I₀, ToType (P.obj (op (A.X j))) := fun j => by
    let := hPiso j
    exact inv (P.map (q₁ j).op) (P.map (ρ j).op (a j.1))
  have hb (j : A.I₀) : P.map (q₁ j).op (b j) = P.map (ρ j).op (a j.1) := by
    let := hPiso j
    dsimp [b]
    rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id]
    simp
  have mapComp {Y Z T : B.Scheme} (f : Y ⟶ Z) (g : Z ⟶ T)
      (z : ToType (F.obj (op T))) :
      F.map f.op (F.map g.op z) = F.map (f ≫ g).op z := by
    rw [← Functor.map_comp_apply, ← op_comp]
  have hlocal' (j : A.I₀) : F.map (q₁ j).op (η.app (op (A.X j)) (b j)) =
      F.map (q₂ j).op s := by
    calc
      F.map (q₁ j).op (η.app (op (A.X j)) (b j)) =
          η.app (op (Q j)) (P.map (q₁ j).op (b j)) := (NatTrans.naturality_apply _ _ _).symm
      _ = η.app (op (Q j)) (P.map (ρ j).op (a j.1)) := by rw [hb]
      _ = F.map (ρ j).op (η.app (op (E.X j.1)) (a j.1)) := by
            rw [← NatTrans.naturality_apply]
      _ = F.map (ρ j).op (F.map (E.f j.1).op s) := by rw [ha]
      _ = F.map (ρ j ≫ E.f j.1).op s := mapComp (ρ j) (E.f j.1) _
      _ = F.map (q₂ j).op s := by rw [hρ]
  let R : A.I₀ → A.I₀ → B.Scheme := fun j l => pullback (A.f j) (A.f l)
  let r₁ : ∀ j l, R j l ⟶ A.X j := fun j l => pullback.fst (A.f j) (A.f l)
  let r₂ : ∀ j l, R j l ⟶ A.X l := fun j l => pullback.snd (A.f j) (A.f l)
  have hpbR (j l : A.I₀) : IsPullback (r₁ j l) (r₂ j l) (A.f j) (A.f l) :=
    IsPullback.of_hasPullback _ _
  let gR : ∀ j l, R j l ⟶ X' := fun j l => r₁ j l ≫ A.f j
  let W : A.I₀ → A.I₀ → B.Scheme := fun j l => pullback (gR j l) i
  let d₁ : ∀ j l, W j l ⟶ R j l := fun j l => pullback.fst (gR j l) i
  let d₂ : ∀ j l, W j l ⟶ X := fun j l => pullback.snd (gR j l) i
  have hpbW (j l : A.I₀) : IsPullback (d₁ j l) (d₂ j l) (gR j l) i :=
    IsPullback.of_hasPullback _ _
  have hthickW (j l : A.I₀) :
      Stacks.Thickenings.IsThickening ((B.inclusion).map (d₁ j l)) :=
    dimensionSheafData_baseChange_isThickening B (d₁ j l) (d₂ j l) (gR j l) i
      (hpbW j l) hi
  have hoverlap (j l : A.I₀) :
      F.map (r₁ j l).op (η.app (op (A.X j)) (b j)) =
        F.map (r₂ j l).op (η.app (op (A.X l)) (b l)) := by
    apply dimensionSheafData_map_injective_of_isThickening B n (d₁ j l)
      (hthickW j l)
    let u₁ : W j l ⟶ Q j := pullback.lift ((d₁ j l) ≫ r₁ j l) (d₂ j l) (by
      calc
        ((d₁ j l ≫ r₁ j l) ≫ A.f j) = d₁ j l ≫ (r₁ j l ≫ A.f j) :=
          Category.assoc _ _ _
        _ = d₂ j l ≫ i := (hpbW j l).w)
    let u₂ : W j l ⟶ Q l := pullback.lift ((d₁ j l) ≫ r₂ j l) (d₂ j l) (by
      calc
        ((d₁ j l ≫ r₂ j l) ≫ A.f l) = d₁ j l ≫ (r₂ j l ≫ A.f l) :=
          Category.assoc _ _ _
        _ = d₁ j l ≫ (r₁ j l ≫ A.f j) := by rw [(hpbR j l).w.symm]
        _ = d₂ j l ≫ i := (hpbW j l).w)
    have hu₁₁ : u₁ ≫ q₁ j = d₁ j l ≫ r₁ j l := pullback.lift_fst _ _ _
    have hu₁₂ : u₁ ≫ q₂ j = d₂ j l := pullback.lift_snd _ _ _
    have hu₂₁ : u₂ ≫ q₁ l = d₁ j l ≫ r₂ j l := pullback.lift_fst _ _ _
    have hu₂₂ : u₂ ≫ q₂ l = d₂ j l := pullback.lift_snd _ _ _
    have hleft : F.map (d₁ j l).op
        (F.map (r₁ j l).op (η.app (op (A.X j)) (b j))) =
        F.map (d₂ j l).op s := by
      simpa only [← Functor.map_comp_apply, ← op_comp, hu₁₁, hu₁₂] using
        congrArg (F.map u₁.op) (hlocal' j)
    have hright : F.map (d₁ j l).op
        (F.map (r₂ j l).op (η.app (op (A.X l)) (b l))) =
        F.map (d₂ j l).op s := by
      simpa only [← Functor.map_comp_apply, ← op_comp, hu₂₁, hu₂₂] using
        congrArg (F.map u₂.op) (hlocal' l)
    exact hleft.trans hright.symm
  have hFG : Presieve.IsSheaf B.topology (F ⋙ forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type B.topology (F ⋙ forget AddCommGrpCat)).mp
      ((Presheaf.isSheaf_iff_isSheaf_forget (J := B.topology)
        (P' := F) (forget AddCommGrpCat)).mp D.isSheaf)
  let xval : ∀ j : A.I₀, (F ⋙ forget AddCommGrpCat).obj (op (A.X j)) := fun j =>
    η.app (op (A.X j)) (b j)
  obtain ⟨t, ht, -⟩ :=
    (Presieve.isSheafFor_arrows_iff_pullbacks (P := F ⋙ forget AddCommGrpCat)
        (X := A.X) (π := A.f)).mp
      ((Presieve.isSheafFor_iff_generate _).mpr (hFG (Sieve.ofArrows A.X A.f) hcoverA))
      xval hoverlap
  have ht' (j : A.I₀) : F.map (A.f j).op t = xval j := ht j
  have heq (j : A.I₀) : F.map (q₂ j).op (F.map i.op t) = F.map (q₂ j).op s := by
    calc
      F.map (q₂ j).op (F.map i.op t) = F.map (q₂ j ≫ i).op t := mapComp (q₂ j) i _
      _ = F.map (q₁ j ≫ A.f j).op t := by rw [(hpb j).w.symm]
      _ = F.map (q₁ j).op (F.map (A.f j).op t) := (mapComp (q₁ j) (A.f j) _).symm
      _ = F.map (q₁ j).op (xval j) := by rw [ht']
      _ = F.map (q₂ j).op s := hlocal' j
  have hQcover : Sieve.ofArrows Q q₂ ∈ B.topology X := by
    rw [Sieve.ofArrows_eq_pullback_of_isPullback A.f fun j => (hpb j).flip]
    exact B.topology.pullback_stable i hcoverA
  have hEq : Presheaf.equalizerSieve (F.map i.op t) s ∈ B.topology X := by
    apply B.topology.superset_covering _ hQcover
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    exact heq
  have hts : F.map i.op t = s := D.isSheaf.isSeparated X
    (Presheaf.equalizerSieve (F.map i.op t) s) hEq _ _ (fun Y f hf => hf)
  exact ⟨t, hts⟩

/-- The canonical restriction map of `dimensionDetectingSheaf B n` along a thickening is an
isomorphism. -/
public theorem dimensionDetectingSheaf_map_isIso_of_isThickening
    (B : BigEtaleSite.{u}) (n : ℕ) {X X' : B.Scheme} (i : X ⟶ X')
    (hi : Stacks.Thickenings.IsThickening ((B.inclusion).map i)) :
    IsIso ((dimensionDetectingSheaf B n).obj.map i.op) := by
  let D := dimensionSheafData B n
  change IsIso (D.sheafification.map i.op)
  dsimp [D, dimensionSheafData, DimensionSheafData.sheafification]
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨dimensionSheafData_map_injective_of_isThickening B n i hi,
    dimensionSheafData_map_surjective_of_isThickening B n i hi⟩

/-- **Stacks 05LE.** For every big étale site and every natural number `n` there is a sheaf of
abelian groups `G` on it whose sections over `X` are zero when `\dim(X) < n`, are nonzero when
`\dim(X) \ge n`, and restrict isomorphically along a thickening `X \subset X'`. -/
@[stacks 05LE]
public theorem exists_sheaf_detecting_dimension (B : BigEtaleSite.{u}) (n : ℕ) :
    ∃ G : Sheaf B.topology AddCommGrpCat.{u + 1},
      (∀ X : B.Scheme, topologicalKrullDim ((B.inclusion).obj X) < (n : WithBot ℕ∞) →
          Subsingleton (G.obj.obj (Opposite.op X))) ∧
        (∀ X : B.Scheme, (n : WithBot ℕ∞) ≤ topologicalKrullDim ((B.inclusion).obj X) →
          Nontrivial (G.obj.obj (Opposite.op X))) ∧
        (∀ (X X' : B.Scheme) (i : X ⟶ X'),
          Stacks.Thickenings.IsThickening ((B.inclusion).map i) →
            IsIso (G.obj.map i.op)) :=
  ⟨dimensionDetectingSheaf B n, dimensionDetectingSheaf_subsingleton_of_dim_lt B n,
    dimensionDetectingSheaf_nontrivial_of_dim_ge B n,
    fun _ _ => dimensionDetectingSheaf_map_isIso_of_isThickening B n⟩

end Stacks.Examples.DimensionSheaf
