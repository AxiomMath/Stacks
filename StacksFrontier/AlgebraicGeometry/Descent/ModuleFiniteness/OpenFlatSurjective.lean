module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeLocallySurjective
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
public import StacksFrontier.Topology.Sheaves.Stalk.Module

/-!
# Finite type descends along open, surjective, flat morphisms

If a morphism of locally ringed spaces is open, surjective and flat, then a sheaf of modules on
the target is of finite type as soon as its pullback is of finite type.

## Main results

* `AlgebraicGeometry.isFiniteType_of_isFiniteType_modulePullback`: finite type descends along
  an open, surjective, flat morphism of locally ringed spaces.

## Implementation notes

The pullback is `RingedSpaceModuleAdjunction.modulePullback`, the canonical pullback functor for
sheaves of modules on ringed spaces. Flatness is the stalkwise predicate
`AlgebraicGeometry.IsFlat`, applied to the underlying morphism of ringed spaces. Local generation
is `Stacks.SheafOfModules.LocallySurjective.LocalLinComb`: every section over a smaller open is
locally a linear combination of the chosen ones.

## References

* [Stacks Project, Tag 09UB](https://stacks.math.columbia.edu/tag/09UB)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite RingedSpaceModuleAdjunction
  TopologicalSpace Limits

universe u v

namespace AlgebraicGeometry

/-- **The two stalk module structures on the stalk of a presheaf of modules agree** through
`SemilinearStalk.commStalkRingEquiv`: the one over the `CommRingCat`-valued stalk of the
structure presheaf and the one over the `RingCat`-valued stalk of its underlying presheaf of
rings. -/
private lemma commStalkRingEquiv_smul {Z : TopCat.{u}}
    (R : TopCat.Presheaf CommRingCat.{u} Z) (z : Z)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (r : TopCat.Presheaf.stalk (C := RingCat.{u})
      (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) z)
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf z) :
    SemilinearStalk.commStalkRingEquiv R z r • m = r • m := by
  obtain ⟨U₁, hzU₁, r₀, hr⟩ := TopCat.Presheaf.exists_germ_eq
    (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) r
  obtain ⟨U₂, hzU₂, m₀, hm⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
  have hmem : z ∈ U₁ ⊓ U₂ := ⟨hzU₁, hzU₂⟩
  have hr' : TopCat.Presheaf.germ (C := RingCat.{u})
      (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) (U₁ ⊓ U₂) z hmem
      ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).map
        (homOfLE inf_le_left).op r₀) = r := by
    rw [TopCat.Presheaf.germ_res_apply (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})
      (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) z hmem r₀]
    exact hr
  have hm' : TopCat.Presheaf.germ M.presheaf (U₁ ⊓ U₂) z hmem
      (M.presheaf.map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op m₀) = m := by
    rw [TopCat.Presheaf.germ_res_apply M.presheaf
      (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) z hmem m₀]
    exact hm
  rw [← hr', ← hm', SemilinearStalk.commStalkRingEquiv_germ]
  let rr : R.obj (op (U₁ ⊓ U₂)) := R.map (homOfLE inf_le_left).op r₀
  let mm : M.obj (op (U₁ ⊓ U₂)) := M.map (homOfLE inf_le_right).op m₀
  change R.germ (U₁ ⊓ U₂) z hmem rr •
    TopCat.Presheaf.germ M.presheaf (U₁ ⊓ U₂) z hmem mm =
    TopCat.Presheaf.germ (C := RingCat.{u})
      (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) (U₁ ⊓ U₂) z hmem rr •
      TopCat.Presheaf.germ M.presheaf (U₁ ⊓ U₂) z hmem mm
  exact (PresheafOfModules.germ_smul M z (U₁ ⊓ U₂) hmem rr mm).symm.trans
    (PresheafOfModules.germ_ringCat_smul M z (U₁ ⊓ U₂) hmem rr mm)

/-- If every scalar of `Q` acts as some scalar of `P`, a spanning set for `Q` spans for `P`. -/
private theorem span_eq_top_of_exists_smul_eq
    {P Q M : Type*} [Semiring P] [Semiring Q] [AddCommMonoid M] [Module P M] [Module Q M]
    (S : Set M) (h : ∀ (q : Q) (m : M), ∃ p : P, q • m = p • m)
    (hQ : Submodule.span Q S = ⊤) : Submodule.span P S = ⊤ := by
  refine top_unique fun m _ => ?_
  refine Submodule.span_induction (p := fun z _ => z ∈ Submodule.span P S)
    (fun z hz => Submodule.subset_span hz) (Submodule.zero_mem _)
    (fun _ _ _ _ hx hy => Submodule.add_mem _ hx hy) (fun q x _ hx => ?_)
    (show m ∈ Submodule.span Q S by rw [hQ]; exact Submodule.mem_top)
  obtain ⟨p, hp⟩ := h q x
  rw [hp]
  exact Submodule.smul_mem _ _ hx

/-- Spanning a module is insensitive to replacing the scalars by an isomorphic ring acting
compatibly. -/
private theorem span_eq_top_iff_ringEquiv
    {A B M : Type*} [Semiring A] [Semiring B] [AddCommMonoid M]
    [Module A M] [Module B M] (e : B ≃+* A)
    (hsmul : ∀ (b : B) (m : M), b • m = (e b) • m) (S : Set M) :
    Submodule.span A S = ⊤ ↔ Submodule.span B S = ⊤ :=
  ⟨span_eq_top_of_exists_smul_eq S fun a m => ⟨e.symm a, by rw [hsmul, e.apply_symm_apply]⟩,
    span_eq_top_of_exists_smul_eq S fun b m => ⟨e b, hsmul b m⟩⟩

/-- A stalk which is finite over one of two ring structures, compatibly identified by a ring
equivalence, is finite over the other. -/
private theorem finite_of_ringEquiv
    {A B M : Type u} [Semiring A] [Semiring B] [AddCommMonoid M]
    (e : B ≃+* A) [Module B M] [Module A M] (h : Module.Finite B M)
    (hsmul : ∀ (b : B) (m : M), b • m = (e b) • m) :
    Module.Finite A M := by
  obtain ⟨S, hSfin, hSspan⟩ := Submodule.fg_def.mp h.1
  exact Module.Finite.of_fg_top
    (Submodule.fg_def.mpr ⟨S, hSfin, (span_eq_top_iff_ringEquiv e hsmul S).mpr hSspan⟩)

/-- A spanning family base changes to a spanning family of pure tensors. -/
private theorem span_one_tmul_eq_top
    {A B M : Type*} [CommSemiring A] [Semiring B] [Algebra A B]
    [AddCommMonoid M] [Module A M] {ι : Type*} (s : ι → M)
    (hs : Submodule.span A (Set.range s) = ⊤) :
    Submodule.span B
      (Set.range (fun i => (1 : B) ⊗ₜ[A] s i)) = ⊤ := by
  have h := Submodule.baseChange_span (R := A) (M := M) B (Set.range s)
  rw [hs, Submodule.baseChange_top, ← Set.range_comp] at h
  exact h.symm

/-- Conversely, over a faithfully flat base change a family whose pure tensors span is already
spanning. -/
private theorem span_eq_top_of_span_one_tmul_eq_top
    {A B M : Type*} [CommRing A] [Ring B] [Algebra A B]
    [Module.FaithfullyFlat A B] [AddCommGroup M] [Module A M]
    {ι : Type*} (s : ι → M)
    (hs : Submodule.span B
      (Set.range (fun i => (1 : B) ⊗ₜ[A] s i)) = ⊤) :
    Submodule.span A (Set.range s) = ⊤ := by
  apply Submodule.baseChange_injective (A := B)
  rw [Submodule.baseChange_span, Submodule.baseChange_top, ← Set.range_comp]
  exact hs

/-- A linear equivalence carries a family to a spanning family exactly when the family spans. -/
private theorem span_range_eq_top_iff_of_linearEquiv
    {R M N ι : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (e : M ≃ₗ[R] N) (p : ι → M) (q : ι → N) (hp : ∀ i, e (p i) = q i) :
    Submodule.span R (Set.range p) = ⊤ ↔ Submodule.span R (Set.range q) = ⊤ := by
  obtain rfl : q = e ∘ p := funext fun i => (hp i).symm
  rw [Set.range_comp, ← LinearEquiv.coe_coe, ← Submodule.map_span, Submodule.map_eq_top_iff]

/-- The germ of a linear combination of sections is the linear combination of the germs. -/
private theorem germ_sum_smul
    {X : AlgebraicGeometry.RingedSpace.{u}}
    (R : Sheaf.{u, u, u, u + 1}
      (Opens.grothendieckTopology X.carrier) RingCat.{u})
    (M : SheafOfModules.{u} R) {I : Type*} [Fintype I]
    (W : Opens X) (x : X) (hxW : x ∈ W) (a : I → R.obj.obj (op W))
    (m : I → M.val.obj (op W)) :
    TopCat.Presheaf.germ M.val.presheaf W x hxW (∑ i, (a i • m i : M.val.presheaf.obj (op W))) =
      ∑ i, TopCat.Presheaf.germ (C := RingCat.{u}) R.obj W x hxW (a i) •
        TopCat.Presheaf.germ M.val.presheaf W x hxW (m i) := by
  refine (map_sum (ConcreteCategory.hom (TopCat.Presheaf.germ M.val.presheaf W x hxW)) _ _).trans
    (Finset.sum_congr rfl fun i _ => ?_)
  exact PresheafOfModules.germ_ringCat_smul M.val x W hxW (a i) (m i)

/-- Sections which locally generate a sheaf of modules over an open generate every stalk at a
point of that open. -/
private theorem span_stalk_of_localLinComb
    {X : AlgebraicGeometry.RingedSpace.{u}}
    (R : Sheaf.{u, u, u, u + 1}
      (Opens.grothendieckTopology X.carrier) RingCat.{u})
    (M : SheafOfModules.{u} R)
    {J : Type u} [Fintype J]
    (V : TopologicalSpace.Opens X) (s : J → M.val.presheaf.obj (op V))
    (hs : Stacks.SheafOfModules.LocallySurjective.LocalLinComb (R := R) (F := M) V s)
    (x : X) (hxV : x ∈ V) :
    Submodule.span (ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) R.obj x))
      (Set.range (fun j => TopCat.Presheaf.germ M.val.presheaf V x hxV (s j))) = ⊤ := by
  let sGerm : J → TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf x := fun j =>
    TopCat.Presheaf.germ M.val.presheaf V x hxV (s j)
  apply top_unique
  intro z _
  obtain ⟨U, hxU, t, hzt⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf z
  let U' : TopologicalSpace.Opens X.carrier := U ⊓ V
  have hxU' : x ∈ U' := ⟨hxU, hxV⟩
  let t' := ConcreteCategory.hom
    (M.val.presheaf.map (homOfLE (inf_le_left : U' ≤ U)).op) t
  obtain ⟨W, hWU', hxW, a, ha⟩ := hs U' inf_le_right t' x hxU'
  let sMW : J → M.val.obj (op W) := fun j => M.val.map
    (homOfLE (le_trans hWU' inf_le_right)).op (s j)
  have hsgerm (j : J) : TopCat.Presheaf.germ M.val.presheaf W x hxW (sMW j) = sGerm j :=
    TopCat.Presheaf.germ_res_apply M.val.presheaf
      (homOfLE (le_trans hWU' inf_le_right)) x hxW (s j)
  have hzsum : z = ∑ j, (TopCat.Presheaf.germ (C := RingCat.{u})
      R.obj W x hxW (a j)) • sGerm j := by
    calc
      z = TopCat.Presheaf.germ M.val.presheaf U x hxU t := hzt.symm
      _ = TopCat.Presheaf.germ M.val.presheaf W x hxW
          ((M.val.presheaf.map (homOfLE hWU').op) t') :=
        (TopCat.Presheaf.germ_res_apply M.val.presheaf
          (homOfLE (inf_le_left : U' ≤ U)) x hxU' t).symm.trans
          (TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE hWU') x hxW t').symm
      _ = _ := (congrArg (fun q => ConcreteCategory.hom
          (TopCat.Presheaf.germ M.val.presheaf W x hxW) q) ha).trans
        ((germ_sum_smul R M W x hxW a sMW).trans
          (Finset.sum_congr rfl fun j _ => congrArg _ (hsgerm j)))
  rw [hzsum]
  exact Submodule.sum_mem _ (fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

/-- A germ lying in the span of finitely many germs is, on a smaller neighbourhood, an actual
linear combination of the corresponding sections. -/
private theorem exists_nbhd_linear_combination_of_mem_span
    {X : AlgebraicGeometry.RingedSpace.{u}}
    (R : Sheaf.{u, u, u, u + 1}
      (Opens.grothendieckTopology X.carrier) RingCat.{u})
    (M : SheafOfModules.{u} R)
    {I : Type v} [Fintype I]
    (U V : Opens X) (s : I → M.val.presheaf.obj (op U))
    (t : M.val.presheaf.obj (op V)) (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    (ht : TopCat.Presheaf.germ M.val.presheaf V x hxV t ∈
      Submodule.span (ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) R.obj x))
        (Set.range (fun i => TopCat.Presheaf.germ M.val.presheaf U x hxU (s i)))) :
    ∃ (W : Opens X) (hWU : W ≤ U) (hWV : W ≤ V) (_ : x ∈ W)
      (a : I → R.obj.obj (op W)),
      (M.val.presheaf.map (homOfLE hWV).op) t =
        ∑ i, (a i • (M.val.presheaf.map (homOfLE hWU).op) (s i) :
          M.val.presheaf.obj (op W)) := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun
    (ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) R.obj x))).mp ht
  choose A hxA b hb using
    (fun i : I => TopCat.Presheaf.exists_germ_eq R.obj (c i))
  let W₀ : Opens X := U ⊓ V ⊓ ⟨⋂ i : I, (A i : Set X),
    isOpen_iInter_of_finite (fun i => (A i).2)⟩
  have hW₀U : W₀ ≤ U := le_trans inf_le_left inf_le_left
  have hW₀V : W₀ ≤ V := le_trans inf_le_left inf_le_right
  have hW₀A (i : I) : W₀ ≤ A i :=
    le_trans inf_le_right (Set.iInter_subset _ i)
  have hxW₀ : x ∈ W₀ := ⟨⟨hxU, hxV⟩, Set.mem_iInter.mpr hxA⟩
  let a₀ : I → R.obj.obj (op W₀) := fun i =>
    R.obj.map (homOfLE (hW₀A i)).op (b i)
  have ha₀ (i : I) : TopCat.Presheaf.germ (C := RingCat.{u})
      R.obj W₀ x hxW₀ (a₀ i) = c i :=
    (TopCat.Presheaf.germ_res_apply R.obj (homOfLE (hW₀A i)) x hxW₀ (b i)).trans (hb i)
  let t₀ : M.val.obj (op W₀) :=
    M.val.presheaf.map (homOfLE hW₀V).op t
  let s₀ : I → M.val.obj (op W₀) := fun i =>
    M.val.map (homOfLE hW₀U).op (s i)
  let q₀ : M.val.obj (op W₀) :=
    ∑ i, a₀ i • s₀ i
  have hqgerm : TopCat.Presheaf.germ M.val.presheaf W₀ x hxW₀ q₀ =
      TopCat.Presheaf.germ M.val.presheaf W₀ x hxW₀ t₀ := by
    have ht₀ : TopCat.Presheaf.germ M.val.presheaf W₀ x hxW₀ t₀ =
        TopCat.Presheaf.germ M.val.presheaf V x hxV t :=
      TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE hW₀V) x hxW₀ t
    refine (germ_sum_smul R M W₀ x hxW₀ a₀ s₀).trans ?_
    rw [ht₀, ← hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ha₀]
    exact congrArg (c i • ·) (TopCat.Presheaf.germ_res_apply M.val.presheaf
      (homOfLE hW₀U) x hxW₀ (s i))
  obtain ⟨W, hxW, hWW₀, hWW₀', heq⟩ :=
    TopCat.Presheaf.germ_eq M.val.presheaf x hxW₀ hxW₀ q₀ t₀ hqgerm
  obtain rfl : hWW₀ = hWW₀' := Subsingleton.elim _ _
  have hWU : W ≤ U := le_trans (leOfHom hWW₀) hW₀U
  have hWV : W ≤ V := le_trans (leOfHom hWW₀) hW₀V
  let a : I → R.obj.obj (op W) := fun i => R.obj.map hWW₀.op (a₀ i)
  refine ⟨W, hWU, hWV, hxW, a, ?_⟩
  have hmapt : (M.val.presheaf.map (homOfLE hWV).op) t =
      (M.val.presheaf.map hWW₀.op) t₀ := by
    dsimp [t₀]
    have hmap : M.val.presheaf.map (homOfLE hWV).op =
        M.val.presheaf.map (homOfLE hW₀V).op ≫ M.val.presheaf.map hWW₀.op := by
      rw [← Functor.map_comp]
      rfl
    rw [hmap]
    rfl
  rw [hmapt, ← heq]
  have hq₀ : q₀ = ∑ i, a₀ i • s₀ i := rfl
  have hqsum := congrArg (fun q : M.val.obj (op W₀) => M.val.map hWW₀.op q) hq₀
  simp only [map_sum] at hqsum
  change M.val.map hWW₀.op q₀ = _
  rw [hqsum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [M.val.map_smul]
  dsimp [a, s₀]
  congr 1
  change M.val.map hWW₀.op (M.val.map (homOfLE hW₀U).op (s i)) =
    M.val.map (homOfLE hWU).op (s i)
  calc
    _ = M.val.map ((homOfLE hW₀U).op ≫ hWW₀.op) (s i) :=
      (M.val.map_comp_apply (homOfLE hW₀U).op hWW₀.op (s i)).symm
    _ = _ := by congr 1

/-- Sections which span every stalk over an open locally generate the sheaf there. -/
private theorem localLinComb_of_stalk_spans
    {X : AlgebraicGeometry.RingedSpace.{u}}
    (R : Sheaf.{u, u, u, u + 1}
      (Opens.grothendieckTopology X.carrier) RingCat.{u})
    (M : SheafOfModules.{u} R)
    {I : Type v} [Fintype I]
    (V : Opens X) (s : I → M.val.presheaf.obj (op V))
    (hs : ∀ (x : X) (hxV : x ∈ V),
      Submodule.span (ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) R.obj x))
        (Set.range (fun i => TopCat.Presheaf.germ M.val.presheaf V x hxV (s i))) = ⊤) :
    Stacks.SheafOfModules.LocallySurjective.LocalLinComb (R := R) (F := M) V s := by
  intro U hUV t x hxU
  have hxV : x ∈ V := hUV hxU
  have ht : TopCat.Presheaf.germ M.val.presheaf U x hxU t ∈
      Submodule.span (ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) R.obj x))
        (Set.range (fun i => TopCat.Presheaf.germ M.val.presheaf V x hxV (s i))) := by
    rw [hs x hxV]
    exact Submodule.mem_top
  obtain ⟨W, hWV, hWU, hxW, a, ha⟩ :=
    exists_nbhd_linear_combination_of_mem_span R M V U s t x hxV hxU ht
  refine ⟨W, hWU, hxW, a, ?_⟩
  simpa only [le_trans hWU hUV] using ha

/-- A section over an open, read as a section of the localization of the sheaf at that open. -/
private def sectionOver
    {X : AlgebraicGeometry.RingedSpace.{u}}
    (R : Sheaf.{u, u, u, u + 1}
      (Opens.grothendieckTopology X.carrier) RingCat.{u})
    (M : SheafOfModules.{u} R) (V : Opens X)
    (s : M.val.obj (op V)) : (M.over V).sections :=
  (M.over V).val.sectionsMk
    (fun U => M.val.map (unop U).hom.op s)
    (by
      intro U W f
      change M.val.map f.unop.left.op (M.val.map (unop U).hom.op s) =
        M.val.map (unop W).hom.op s
      calc
        _ = M.val.map ((unop U).hom.op ≫ f.unop.left.op) s :=
          (M.val.map_comp_apply (unop U).hom.op f.unop.left.op s).symm
        _ = _ := by
          congr 1)

/-- Finitely many sections which locally generate a sheaf of modules over an open are generating
sections of the localization at that open. -/
private theorem exists_generatingSections_of_localLinComb
    {X : AlgebraicGeometry.RingedSpace.{u}}
    (R : Sheaf.{u, u, u, u + 1}
      (Opens.grothendieckTopology X.carrier) RingCat.{u})
    (M : SheafOfModules.{u} R) (V : Opens X)
    {I : Type u} [Fintype I]
    (s : I → M.val.presheaf.obj (op V))
    (hs : Stacks.SheafOfModules.LocallySurjective.LocalLinComb (R := R) (F := M) V s) :
    ∃ σ : (M.over V).GeneratingSections, σ.IsFiniteType := by
  classical
  let sec : I → (M.over V).sections := fun i => sectionOver R M V (s i)
  let π : SheafOfModules.free (R := R.over V) I ⟶ M.over V :=
    (M.over V).freeHomEquiv.symm sec
  have hloc : Presheaf.IsLocallySurjective
      ((Opens.grothendieckTopology X.carrier).over V)
      (((SheafOfModules.toSheaf (R.over V)).map π).hom) := by
    constructor
    intro Uo t
    rw [GrothendieckTopology.mem_over_iff]
    intro y hyU
    have hUV : Uo.left ≤ V := leOfHom Uo.hom
    obtain ⟨W, hWU, hyW, a, ha⟩ := hs Uo.left hUV t y hyU
    let Wo : Over V := Over.mk (homOfLE (le_trans hWU hUV))
    let g : Wo ⟶ Uo := Over.homMk (homOfLE hWU) (by cat_disch)
    refine ⟨W, homOfLE hWU, ?_, hyW⟩
    rw [Sieve.overEquiv_iff]
    change Presheaf.imageSieve
      (((SheafOfModules.toSheaf (R.over V)).map π).hom) t g
    let ar : I → (R.over V).obj.obj (op Wo) := fun i => a i
    let fs : I → (SheafOfModules.free (R := R.over V) I).val.obj (op Wo) :=
      fun i => (SheafOfModules.freeSection (R := R.over V) i).eval (op Wo)
    let q : (SheafOfModules.free (R := R.over V) I).val.obj (op Wo) :=
      ∑ i, ar i • fs i
    refine ⟨q, ?_⟩
    change π.val.app (op Wo) q = (M.over V).val.map g.op t
    dsimp [q]
    rw [map_sum]
    have hsmul (i : I) : π.val.app (op Wo) (ar i • fs i) =
        ar i • π.val.app (op Wo) (fs i) :=
      (π.val.app (op Wo)).hom.map_smul (ar i) _
    simp_rw [hsmul]
    have hfree (i : I) : π.val.app (op Wo) (fs i) = (sec i).eval (op Wo) := by
      have h := SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection sec i
      exact congrArg (fun q : (M.over V).sections => q.val (op Wo)) h
    simp_rw [hfree]
    convert ha.symm using 1
    rfl
  have hepiSheaf : Epi ((SheafOfModules.toSheaf (R.over V)).map π) := by
    have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf (R.over V)).map π) := hloc
    infer_instance
  have hepi : Epi π := (SheafOfModules.toSheaf (R.over V)).epi_of_epi_map hepiSheaf
  exact ⟨{ I := I, s := sec, epi := hepi }, ⟨inferInstance⟩⟩

/-- For a finite type sheaf of modules, spanning the stalk at one point spreads to spanning the
stalk at every point of a neighbourhood. -/
private theorem exists_nbhd_span_of_finite_type
    {X : AlgebraicGeometry.RingedSpace.{u}}
    (R : Sheaf.{u, u, u, u + 1}
      (Opens.grothendieckTopology X.carrier) RingCat.{u})
    (M : SheafOfModules.{u} R) (hM : M.IsFiniteType)
    {I : Type v} [Finite I] (U : Opens X)
    (s : I → M.val.presheaf.obj (op U)) (x : X) (hxU : x ∈ U)
    (hspan : Submodule.span (ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) R.obj x))
      (Set.range (fun i => TopCat.Presheaf.germ M.val.presheaf U x hxU (s i))) = ⊤) :
    ∃ (W : Opens X) (hWU : W ≤ U), x ∈ W ∧
      ∀ (y : X) (hyW : y ∈ W),
        Submodule.span (ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) R.obj y))
          (Set.range (fun i => TopCat.Presheaf.germ M.val.presheaf U y
            (hWU hyW) (s i))) = ⊤ := by
  classical
  let : Fintype I := Fintype.ofFinite I
  obtain ⟨V, hxV, J, hJ, t, ht⟩ := Stacks.SheafOfModules.LocallySurjective.exists_local_generators
    hM x
  have hj (j : J) : TopCat.Presheaf.germ M.val.presheaf V x hxV (t j) ∈
      Submodule.span (ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) R.obj x))
        (Set.range (fun i => TopCat.Presheaf.germ M.val.presheaf U x hxU (s i))) := by
    rw [hspan]
    exact Submodule.mem_top
  choose W hWU hWV hxW a ha using
    (fun j : J => exists_nbhd_linear_combination_of_mem_span
      R M U V s (t j) x hxU hxV (hj j))
  let W' : Opens X := ⟨⋂ j : J, (W j : Set X),
    isOpen_iInter_of_finite (fun j => (W j).2)⟩
  have hxW' : x ∈ W' := Set.mem_iInter.mpr hxW
  have hW'W (j : J) : W' ≤ W j := Set.iInter_subset _ j
  let Z : Opens X := W' ⊓ U ⊓ V
  have hZU : Z ≤ U := le_trans inf_le_left inf_le_right
  have hZV : Z ≤ V := inf_le_right
  have hZW (j : J) : Z ≤ W j :=
    le_trans (le_trans inf_le_left inf_le_left) (hW'W j)
  have hxZ : x ∈ Z := ⟨⟨hxW', hxU⟩, hxV⟩
  refine ⟨Z, hZU, hxZ, ?_⟩
  intro y hyZ
  have hyV : y ∈ V := hZV hyZ
  have htspan := span_stalk_of_localLinComb R M V t ht y hyV
  apply top_unique
  have hle : Submodule.span (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      R.obj y)) (Set.range (fun j => TopCat.Presheaf.germ M.val.presheaf V y
        hyV (t j))) ≤
      Submodule.span (ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) R.obj y))
        (Set.range (fun i => TopCat.Presheaf.germ M.val.presheaf U y
          (hZU hyZ) (s i))) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have hyW : y ∈ W j := hZW j hyZ
    have hres := (TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE (hWV j)) y hyW
      (t j)).symm.trans ((congrArg (fun q : M.val.obj (op (W j)) =>
        TopCat.Presheaf.germ M.val.presheaf (W j) y hyW q) (ha j)).trans
      (germ_sum_smul R M (W j) y hyW (a j)
        (fun i => M.val.map (homOfLE (hWU j)).op (s i))))
    change TopCat.Presheaf.germ M.val.presheaf V y hyV (t j) ∈ _
    rw [hres]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hsi := TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE (hWU j)) y hyW (s i)
    exact Submodule.smul_mem _ _ (hsi ▸ Submodule.subset_span ⟨i, rfl⟩)
  rwa [htspan] at hle

/-- The stalk map of a flat morphism of locally ringed spaces is faithfully flat. -/
@[ega "0 6.7.8" "partial"]
private lemma faithfullyFlat_stalkMap {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X)
    (hflat : (f.stalkMap x).hom.Flat) :
    letI : Algebra (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    Module.FaithfullyFlat (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := by
  let : Algebra (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := hflat
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x)) := by
    rw [RingHom.algebraMap_toAlgebra]
    infer_instance
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- If the pullback of a sheaf of modules along a flat morphism is of finite type, then the
stalk of the sheaf at the image of any point is a finite module. -/
private theorem finite_modulePullback_stalk
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (F : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (hflat : AlgebraicGeometry.IsFlat f.toShHom)
    (hF : ((modulePullback f.toShHom).obj F).IsFiniteType) (x : X) :
    let F' : PresheafOfModules
      (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
    letI : Module (ToType (Y.presheaf.stalk (f.toShHom.hom.base x)))
      (TopCat.Presheaf.stalk (C := Ab.{u}) F'.presheaf (f.toShHom.hom.base x)) :=
        inferInstance
    Module.Finite (Y.presheaf.stalk (f.toShHom.hom.base x))
      (TopCat.Presheaf.stalk (C := Ab.{u}) F'.presheaf (f.toShHom.hom.base x)) := by
  let P := (modulePullback f.toShHom).obj F
  let P' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) := P.val
  obtain ⟨V, hxV, J, hJ, s, hs⟩ := Stacks.SheafOfModules.LocallySurjective.exists_local_generators
    (F := P) hF x
  have hspan := span_stalk_of_localLinComb (structureSheafRing X.toRingedSpace) P V s hs x hxV
  have hfiniteRing : Module.Finite
      (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (structureSheafRing X.toRingedSpace).obj x))
      (TopCat.Presheaf.stalk (C := Ab.{u}) P.val.presheaf x) :=
    Module.Finite.of_fg_top ((Submodule.fg_def).mpr
      ⟨Set.range (fun j => TopCat.Presheaf.germ P.val.presheaf V x hxV (s j)),
        Set.finite_range _, hspan⟩)
  let eRing : ToType (TopCat.Presheaf.stalk (C := RingCat)
      (X.presheaf ⋙ forget₂ CommRingCat RingCat) x) ≃+*
      ToType (X.presheaf.stalk x) :=
    SemilinearStalk.commStalkRingEquiv X.presheaf x
  let : Module (ToType (X.presheaf.stalk x))
      (TopCat.Presheaf.stalk (C := Ab.{u}) P'.presheaf x) := inferInstance
  have hfiniteRing' : Module.Finite (ToType (TopCat.Presheaf.stalk (C := RingCat)
      (X.presheaf ⋙ forget₂ CommRingCat RingCat) x))
      (TopCat.Presheaf.stalk (C := Ab.{u}) P'.presheaf x) := hfiniteRing
  have hfinite := finite_of_ringEquiv eRing hfiniteRing' (by
    intro b m
    exact (commStalkRingEquiv_smul X.presheaf x P' b m).symm)
  let : Algebra (Y.presheaf.stalk (f.toShHom.hom.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  obtain ⟨e, _he⟩ := exists_modulePullbackStalkLinearEquiv f.toShHom F x
  let F' : PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
  have hfiniteTensor : Module.Finite (ToType (X.presheaf.stalk x))
      (TensorProduct (ToType (Y.presheaf.stalk (f.toShHom.hom.base x)))
        (ToType (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) F'.presheaf (f.toShHom.hom.base x))) := by
    have : Module.Finite (ToType (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) P'.presheaf x) := hfinite
    exact Module.Finite.equiv e
  have hff : Module.FaithfullyFlat (ToType (Y.presheaf.stalk (f.toShHom.hom.base x)))
      (ToType (X.presheaf.stalk x)) := faithfullyFlat_stalkMap f x (hflat x)
  let : Module (ToType (Y.presheaf.stalk (f.toShHom.hom.base x)))
      (TopCat.Presheaf.stalk (C := Ab.{u}) F'.presheaf (f.toShHom.hom.base x)) :=
    inferInstance
  have : Module.FaithfullyFlat
      (ToType (Y.presheaf.stalk (f.toShHom.hom.base x)))
      (ToType (X.presheaf.stalk x)) := hff
  have : Module.Finite (ToType (X.presheaf.stalk x))
      (TensorProduct (ToType (Y.presheaf.stalk (f.toShHom.hom.base x)))
        (ToType (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) F'.presheaf
          (f.toShHom.hom.base x))) := hfiniteTensor
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat
    (ToType (X.presheaf.stalk x))

/-- A finite stalk of a presheaf of modules is spanned by the germs of finitely many sections
over a single open neighbourhood. -/
private theorem exists_local_sections_generating_comm_stalk
    {Z : TopCat.{u}} (R : TopCat.Presheaf CommRingCat.{u} Z)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})) (z : Z)
    [Module.Finite (ToType (R.stalk z))
      (TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf z)] :
    ∃ (V : Opens Z) (hzV : z ∈ V) (n : ℕ)
      (s : Fin n → M.presheaf.obj (op V)),
      Submodule.span (ToType (R.stalk z))
        (Set.range (fun i => TopCat.Presheaf.germ M.presheaf V z hzV (s i))) = ⊤ := by
  classical
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := ToType (R.stalk z))
    (M := TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf z)
  choose U hzU t ht using
    (fun i : Fin n => TopCat.Presheaf.exists_germ_eq M.presheaf (g i))
  let V : Opens Z := ⟨⋂ i : Fin n, (U i : Set Z),
    isOpen_iInter_of_finite (fun i => (U i).2)⟩
  have hzV : z ∈ V := Set.mem_iInter.mpr hzU
  let s : Fin n → M.presheaf.obj (op V) := fun i =>
    M.presheaf.map (homOfLE (show V ≤ U i from Set.iInter_subset _ i)).op (t i)
  have hgs (i : Fin n) : TopCat.Presheaf.germ M.presheaf V z hzV (s i) = g i :=
    (TopCat.Presheaf.germ_res_apply M.presheaf
      (homOfLE (show V ≤ U i from Set.iInter_subset _ i)) z hzV (t i)).trans (ht i)
  refine ⟨V, hzV, n, s, ?_⟩
  simpa only [funext hgs] using hg

/-- Finitely many sections of the original module whose images span the stalk of the pullback. -/
private theorem exists_local_sections_generating_pullback_stalk
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (F : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (hflat : AlgebraicGeometry.IsFlat f.toShHom)
    (hF : ((modulePullback f.toShHom).obj F).IsFiniteType) (x : X) :
    let P := (modulePullback f.toShHom).obj F
    let P' : PresheafOfModules
      (X.presheaf ⋙ forget₂ CommRingCat RingCat) := P.val
    ∃ (V : Opens Y) (hxV : f.base x ∈ V) (n : ℕ)
      (s : Fin n → F.val.presheaf.obj (op V)),
      Submodule.span (ToType (X.presheaf.stalk x))
        (Set.range (fun i => TopCat.Presheaf.germ P'.presheaf
          ((opensMap f.toShHom).obj V) x hxV
          (((modulePullbackPushforwardAdjunction f.toShHom).unit.app F).val.app
            (op V) (s i)))) = ⊤ := by
  classical
  let F' : PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
  let P := (modulePullback f.toShHom).obj F
  let P' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) := P.val
  let : Module (ToType (Y.presheaf.stalk (f.base x)))
      (TopCat.Presheaf.stalk (C := Ab.{u}) F'.presheaf (f.base x)) := inferInstance
  have : Module.Finite (ToType (Y.presheaf.stalk (f.base x)))
      (TopCat.Presheaf.stalk (C := Ab.{u}) F'.presheaf (f.base x)) :=
    finite_modulePullback_stalk f F hflat hF x
  obtain ⟨V, hxV, n, s, hs⟩ :=
    exists_local_sections_generating_comm_stalk Y.presheaf F' (f.base x)
  let : Algebra (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  obtain ⟨e, he⟩ := exists_modulePullbackStalkLinearEquiv f.toShHom F x
  let : Module (ToType (X.presheaf.stalk x))
      (TopCat.Presheaf.stalk (C := Ab.{u}) P'.presheaf x) := inferInstance
  let p : Fin n → TopCat.Presheaf.stalk (C := Ab.{u}) P'.presheaf x := fun i =>
    TopCat.Presheaf.germ P'.presheaf ((opensMap f.toShHom).obj V) x hxV
      (((modulePullbackPushforwardAdjunction f.toShHom).unit.app F).val.app (op V) (s i))
  have hp : ∀ i, e (p i) =
      (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f.base x)]
        TopCat.Presheaf.germ F'.presheaf V (f.base x) hxV (s i) := fun i => he V hxV (s i)
  have htensor := span_one_tmul_eq_top
    (A := ToType (Y.presheaf.stalk (f.base x)))
    (B := ToType (X.presheaf.stalk x))
    (M := TopCat.Presheaf.stalk (C := Ab.{u}) F'.presheaf (f.base x))
    (fun i : Fin n => TopCat.Presheaf.germ F'.presheaf V (f.base x) hxV (s i)) hs
  have hspan : Submodule.span (ToType (X.presheaf.stalk x)) (Set.range p) = ⊤ :=
    (span_range_eq_top_iff_of_linearEquiv e p _ hp).mpr htensor
  exact ⟨V, hxV, n, s, hspan⟩

/-- Faithfully flat descent of spanning: if the images of finitely many sections span the stalk
of the pullback, the sections themselves span the stalk of the original module. -/
private theorem span_target_stalk_of_span_pullback_stalk
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (F : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (hflat : AlgebraicGeometry.IsFlat f.toShHom)
    (V : Opens Y) (n : ℕ) (s : Fin n → F.val.presheaf.obj (op V))
    (x : X) (hxV : f.base x ∈ V)
    (hspan :
      let P := (modulePullback f.toShHom).obj F
      let P' : PresheafOfModules
        (X.presheaf ⋙ forget₂ CommRingCat RingCat) := P.val
      Submodule.span (ToType (X.presheaf.stalk x))
        (Set.range (fun i => TopCat.Presheaf.germ P'.presheaf
          ((opensMap f.toShHom).obj V) x hxV
          (((modulePullbackPushforwardAdjunction f.toShHom).unit.app F).val.app
            (op V) (s i)))) = ⊤) :
    let F' : PresheafOfModules
      (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
    Submodule.span (ToType (Y.presheaf.stalk (f.base x)))
      (Set.range (fun i => TopCat.Presheaf.germ F'.presheaf V
        (f.base x) hxV (s i))) = ⊤ := by
  classical
  let F' : PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
  let P := (modulePullback f.toShHom).obj F
  let P' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) := P.val
  let : Algebra (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have : Module.FaithfullyFlat
      (ToType (Y.presheaf.stalk (f.base x)))
      (ToType (X.presheaf.stalk x)) := faithfullyFlat_stalkMap f x (hflat x)
  obtain ⟨e, he⟩ := exists_modulePullbackStalkLinearEquiv f.toShHom F x
  let p : Fin n → TopCat.Presheaf.stalk (C := Ab.{u}) P'.presheaf x := fun i =>
    TopCat.Presheaf.germ P'.presheaf ((opensMap f.toShHom).obj V) x hxV
      (((modulePullbackPushforwardAdjunction f.toShHom).unit.app F).val.app (op V) (s i))
  have hp (i : Fin n) : e (p i) =
      (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f.base x)]
        TopCat.Presheaf.germ F'.presheaf V (f.base x) hxV (s i) := he V hxV (s i)
  have htensor : Submodule.span (ToType (X.presheaf.stalk x))
      (Set.range (fun i : Fin n =>
        (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f.base x)]
          TopCat.Presheaf.germ F'.presheaf V (f.base x) hxV (s i))) = ⊤ :=
    (span_range_eq_top_iff_of_linearEquiv e p _ hp).mp hspan
  exact span_eq_top_of_span_one_tmul_eq_top
    (A := ToType (Y.presheaf.stalk (f.base x)))
    (B := ToType (X.presheaf.stalk x))
    (M := TopCat.Presheaf.stalk (C := Ab.{u}) F'.presheaf (f.base x))
    (fun i : Fin n => TopCat.Presheaf.germ F'.presheaf V (f.base x) hxV (s i)) htensor

/-- Around every point of the target there is an open set and finitely many sections of the
module which span the stalk at each of its points. -/
private theorem exists_open_stalk_generators_of_pullback_finite_type
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (F : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (hopen : IsOpenMap f.base) (hsurj : Function.Surjective f.base)
    (hflat : AlgebraicGeometry.IsFlat f.toShHom)
    (hF : ((modulePullback f.toShHom).obj F).IsFiniteType) (y : Y) :
    ∃ (V : Opens Y) (_ : y ∈ V) (n : ℕ)
      (s : Fin n → F.val.presheaf.obj (op V)),
      ∀ (z : Y) (hzV : z ∈ V),
        let F' : PresheafOfModules
          (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
        letI : Module (ToType (Y.presheaf.stalk z))
          (TopCat.Presheaf.stalk (C := Ab.{u}) F'.presheaf z) := inferInstance
        Submodule.span (ToType (Y.presheaf.stalk z))
          (Set.range (fun i => TopCat.Presheaf.germ F'.presheaf V z hzV
            (s i))) = ⊤ := by
  classical
  obtain ⟨x, hxy⟩ := hsurj y
  subst y
  obtain ⟨V, hxV, n, s, hs⟩ :=
    exists_local_sections_generating_pullback_stalk f F hflat hF x
  let P := (modulePullback f.toShHom).obj F
  let P' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) := P.val
  let U : Opens X := (opensMap f.toShHom).obj V
  let p : Fin n → P.val.presheaf.obj (op U) := fun i =>
    ((modulePullbackPushforwardAdjunction f.toShHom).unit.app F).val.app (op V) (s i)
  have hring : Submodule.span
      (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (X.presheaf ⋙ forget₂ CommRingCat RingCat) x))
      (Set.range (fun i => TopCat.Presheaf.germ P'.presheaf U x hxV (p i))) = ⊤ :=
    (span_eq_top_iff_ringEquiv (SemilinearStalk.commStalkRingEquiv X.presheaf x)
      (fun b m => (commStalkRingEquiv_smul X.presheaf x P' b m).symm)
      (Set.range (fun i => TopCat.Presheaf.germ P'.presheaf U x hxV (p i)))).mp hs
  obtain ⟨W, hWU, hxW, hWspan⟩ :=
    exists_nbhd_span_of_finite_type (structureSheafRing X.toRingedSpace) P hF U p x hxV hring
  let WX : Opens X.toTopCat := W
  let T : Opens Y := ⟨f.base '' (WX : Set X.toTopCat),
    hopen (WX : Set X.toTopCat) WX.isOpen⟩
  have hxT : f.base x ∈ T := ⟨x, hxW, rfl⟩
  have hTV : T ≤ V := by
    rintro z ⟨u, huW, rfl⟩
    exact hWU huW
  have hpull : ∀ (u : X) (huW : u ∈ W),
      Submodule.span (ToType (X.presheaf.stalk u))
        (Set.range (fun i => TopCat.Presheaf.germ P'.presheaf U u
          (hWU huW) (p i))) = ⊤ := fun u huW =>
    (span_eq_top_iff_ringEquiv (SemilinearStalk.commStalkRingEquiv X.presheaf u)
      (fun b m => (commStalkRingEquiv_smul X.presheaf u P' b m).symm)
      (Set.range (fun i => TopCat.Presheaf.germ P'.presheaf U u
        (hWU huW) (p i)))).mpr (hWspan u huW)
  let t : Fin n → F.val.presheaf.obj (op T) := fun i =>
    F.val.presheaf.map (homOfLE hTV).op (s i)
  refine ⟨T, hxT, n, t, ?_⟩
  intro z hzT
  obtain ⟨u, huW, huz⟩ := hzT
  subst z
  let F' : PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
  let : Module (ToType (Y.presheaf.stalk (f.base u)))
    (TopCat.Presheaf.stalk (C := Ab.{u}) F'.presheaf (f.base u)) := inferInstance
  have huV : f.base u ∈ V := hTV ⟨u, huW, rfl⟩
  have hdown := span_target_stalk_of_span_pullback_stalk
    f F hflat V n s u huV (hpull u huW)
  have htgerm (i : Fin n) : TopCat.Presheaf.germ F'.presheaf T
      (f.base u) ⟨u, huW, rfl⟩ (t i) =
      TopCat.Presheaf.germ F'.presheaf V (f.base u) huV (s i) :=
    TopCat.Presheaf.germ_res_apply F'.presheaf (homOfLE hTV) (f.base u) ⟨u, huW, rfl⟩ (s i)
  have hset : Set.range (fun i => TopCat.Presheaf.germ F'.presheaf T
      (f.base u) ⟨u, huW, rfl⟩ (t i)) =
      Set.range (fun i => TopCat.Presheaf.germ F'.presheaf V
        (f.base u) huV (s i)) :=
    congrArg Set.range (funext htgerm)
  change Submodule.span (ToType (Y.presheaf.stalk (f.base u)))
    (Set.range (fun i : Fin n => TopCat.Presheaf.germ F'.presheaf T
      (f.base u) ⟨u, huW, rfl⟩ (t i))) = ⊤
  rwa [hset]

/-- Finite type of a sheaf of modules descends along an open, surjective, flat morphism of
locally ringed spaces. -/
@[stacks 09UB]
public theorem isFiniteType_of_isFiniteType_modulePullback
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (F : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (hopen : IsOpenMap f.base) (hsurj : Function.Surjective f.base)
    (hflat : AlgebraicGeometry.IsFlat f.toShHom)
    (hF : ((modulePullback f.toShHom).obj F).IsFiniteType) :
    F.IsFiniteType := by
  classical
  choose V hyV n s hs using
    (fun y : Y => exists_open_stalk_generators_of_pullback_finite_type
      f F hopen hsurj hflat hF y)
  have hgen (y : Y) : ∃ σ : (F.over (V y)).GeneratingSections, σ.IsFiniteType := by
    let I : Type u := ULift.{u} (Fin (n y))
    have : Fintype I := Fintype.ofFinite I
    let s' : I → F.val.presheaf.obj (op (V y)) := fun i => s y i.down
    have hring (z : Y) (hzV : z ∈ V y) :
        Submodule.span (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
          (structureSheafRing Y.toRingedSpace).obj z))
          (Set.range (fun i => TopCat.Presheaf.germ F.val.presheaf
            (V y) z hzV (s' i))) = ⊤ := by
      let F' : PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
      let : Module (ToType (Y.presheaf.stalk z))
        (TopCat.Presheaf.stalk (C := Ab.{u}) F'.presheaf z) := inferInstance
      have hset : Set.range (fun i : I => TopCat.Presheaf.germ F'.presheaf
          (V y) z hzV (s' i)) =
          Set.range (fun i : Fin (n y) => TopCat.Presheaf.germ F'.presheaf
            (V y) z hzV (s y i)) := by
        ext q
        exact ⟨fun ⟨i, h⟩ => ⟨i.down, h⟩, fun ⟨i, h⟩ => ⟨⟨i⟩, h⟩⟩
      have hcomm : Submodule.span (ToType (Y.presheaf.stalk z))
          (Set.range (fun i : I => TopCat.Presheaf.germ F'.presheaf
            (V y) z hzV (s' i))) = ⊤ := by
        rw [hset]
        exact hs y z hzV
      exact (span_eq_top_iff_ringEquiv
        (SemilinearStalk.commStalkRingEquiv Y.presheaf z)
        (fun b m => (commStalkRingEquiv_smul Y.presheaf z F' b m).symm)
        (Set.range (fun i : I => TopCat.Presheaf.germ F'.presheaf
          (V y) z hzV (s' i)))).mp hcomm
    exact exists_generatingSections_of_localLinComb
      (structureSheafRing Y.toRingedSpace) F (V y) s'
      (localLinComb_of_stalk_spans (structureSheafRing Y.toRingedSpace) F (V y) s' hring)
  let data : F.LocalGeneratorsData.{u} := {
    I := Y
    X := V
    coversTop :=
      (Opens.coversTop_iff (Y : Type u) V).2 (top_unique fun z _ => Opens.mem_iSup.2 ⟨z, hyV z⟩)
    generators := fun y => (hgen y).choose
  }
  have hdata : data.IsFiniteType := by
    constructor
    intro y
    change ((hgen y).choose).IsFiniteType
    exact (hgen y).choose_spec
  exact SheafOfModules.IsFiniteType.mk.{u, u, u} ⟨data, hdata⟩

end AlgebraicGeometry
