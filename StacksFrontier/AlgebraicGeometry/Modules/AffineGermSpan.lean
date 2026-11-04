module

public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.FinGenFromCover.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange

/-!
# Germs of sections over an affine open span the stalk

Let `F` be a quasi-coherent module on a scheme `X` and let `V` be an affine open. Then for every
`x ∈ V` the germs at `x` of the sections of `F` over `V` span the stalk `F_x`, and if `F` is
moreover of finite type then **finitely many** sections over `V` already do, uniformly in `x`.

The first statement is false for a general module: the stalk is a colimit over *all*
neighbourhoods of `x`, and nothing makes the sections over one of them generate it. It is true
here because on an affine open a quasi-coherent module is determined by its sections: every germ
is represented over some basic open `D(a) ⊆ V`, and `Γ(F, D(a))` is the localization of `Γ(F, V)`
away from `a` ([Stacks, Tag 01I8], `Stacks.AlgebraicGeometry.QuasicoherentBaseChange.`
`isLocalizedModule_restrictₗ`), so the germ is a unit multiple of the germ of a section over `V`.

## Main results

* `Stacks.AffineGermSpan.span_range_germ_sections_eq_top`: **the germs of `Γ(F, V)` span `F_x`**,
  for `F` quasi-coherent, `V` affine and `x ∈ V`.
* `Stacks.AffineGermSpan.exists_finite_sections_span_germ`: **finitely many sections over `V` whose
  germs span at every point of `V`**, for `F` quasi-coherent of finite type.

## Implementation notes

**Two stalk rings, and the span is over the `RingCat` one.** The span is taken over
`TopCat.Presheaf.stalk X.ringCatSheaf.obj x`, with the scoped instance
`Stacks.FinGenFromCover.ringStalkModule`, because that is the ring
`AlgebraicGeometry.generates_iff_stalkwise_generates` and
`Stacks.AmpleLocalGeneration.IsFinGenOn` use. The localization argument, on the other hand, runs
over `X.presheaf.stalk x`, the `CommRingCat` stalk, which is where a germ of `𝒪_X` is a unit at a
point of its basic open. The two are bridged one scalar at a time by
`Stacks.FinGenFromCover.exists_ringStalk_smul_eq`, which is all that is needed: the first lemma
produces a *single* scalar multiple, and the second transfers a span by induction using
`Stacks.FinGenFromCover.ringStalk_germ_smul`, never leaving the `RingCat` stalk.

**Finiteness enters only through `Module.Finite Γ(X, V) Γ(F, V)`**, which is [Stacks, Tag 01PB],
`Stacks.AlgebraicGeometry.CoherentFinite.finite_sections`. The index type is `ULift (Fin n)`
rather than `Fin n` because a generating family in this development must be indexed by a type in
the scheme's universe.

**The route avoids the restriction to the open subscheme.** The other way to this statement is
through `Stacks.AlgebraicGeometry.CoherentFinite.exists_finite_generatingSections_restrict` and
`AlgebraicGeometry.generates_iff_stalkwise_generates` read on `V.toScheme`, and it needs the
stalk of `F.restrict V.ι` and the stalk of `𝒪_{V.toScheme}` identified with those of `F` and
`𝒪_X`. The first identification exists (`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`);
the second exists only for the `CommRingCat`-valued structure sheaf
(`AlgebraicGeometry.Scheme.Opens.stalkIso`) and not for the `RingCat`-valued one the span is
taken over, so that route would need a second index change through
`forget₂ CommRingCat RingCat`. The localization argument used here needs neither.

## References

* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01AN](https://stacks.math.columbia.edu/tag/01AN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open scoped Stacks.ModuleStalk Stacks.FinGenFromCover

universe u

namespace Stacks.AffineGermSpan

variable {X : Scheme.{u}}

/-- **The germs of the sections over an affine open span the stalk**, for a quasi-coherent module:
for `V` affine and `x ∈ V`, the germs at `x` of the elements of `Γ(F, V)` span `F_x` over the
stalk of the structure sheaf. -/
theorem span_range_germ_sections_eq_top (F : X.Modules) [F.IsQuasicoherent] {V : X.Opens}
    (hV : IsAffineOpen V) {x : X} (hx : x ∈ V) :
    Submodule.span (R := (TopCat.Presheaf.stalk X.ringCatSheaf.obj x : RingCat))
      (Set.range fun m : Γ(F, V) => (F.presheaf.germ V x hx).hom m) = ⊤ := by
  refine eq_top_iff.mpr fun y _ => ?_
  obtain ⟨W, hxW, u, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := Ab.{u}) F.presheaf y
  obtain ⟨a, haW, hxa⟩ := hV.exists_basicOpen_le (⟨x, hxW⟩ : W) hx
  have hDV : X.basicOpen a ≤ V := X.basicOpen_le a
  have hyu' : (F.presheaf.germ (X.basicOpen a) x hxa).hom
      (F.presheaf.map (homOfLE haW).op u) = (F.presheaf.germ W x hxW).hom u :=
    TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE haW) x hxa u
  let _ := moduleOfLE F hDV
  have _ := isLocalizedModule_restrictₗ F hV a rfl hDV
  obtain ⟨⟨m, b⟩, hmb⟩ := IsLocalizedModule.surj (Submonoid.powers a) (restrictₗ F hDV)
    (F.presheaf.map (homOfLE haW).op u)
  dsimp only at hmb
  obtain ⟨k, hk⟩ := b.2
  have hres : (b • (F.presheaf.map (homOfLE haW).op u) : Γ(F, X.basicOpen a))
      = X.presheaf.map (homOfLE hDV).op (b : Γ(X, V))
        • (F.presheaf.map (homOfLE haW).op u) := rfl
  have h2 : (F.presheaf.germ (X.basicOpen a) x hxa).hom (restrictₗ F hDV m)
      = (F.presheaf.germ V x hx).hom m :=
    TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE hDV) x hxa m
  have h1 := congrArg (F.presheaf.germ (X.basicOpen a) x hxa).hom hmb
  rw [hres, Stacks.ModuleStalk.germ_smul,
    TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hDV) x hxa (b : Γ(X, V)), hyu', h2] at h1
  have hua : IsUnit ((X.presheaf.germ V x hx).hom a) := (X.mem_basicOpen a x hx).mp hxa
  have hub : IsUnit ((X.presheaf.germ V x hx).hom (b : Γ(X, V))) := by
    rw [← hk, map_pow]
    exact hua.pow k
  obtain ⟨v, hv⟩ := hub
  have hy : (F.presheaf.germ W x hxW).hom u
      = (↑v⁻¹ : X.presheaf.stalk x) • (F.presheaf.germ V x hx).hom m := by
    rw [← h1, ← hv, smul_smul]
    simp
  obtain ⟨r', hr'⟩ := Stacks.FinGenFromCover.exists_ringStalk_smul_eq F x (↑v⁻¹)
    ((F.presheaf.germ V x hx).hom m)
  rw [hy, hr']
  exact Submodule.smul_mem _ r' (Submodule.subset_span ⟨m, rfl⟩)

/-- **Finitely many sections over an affine open whose germs span the stalk at every point of
it**, for a quasi-coherent module of finite type: for `V` affine there is a finite family in
`Γ(F, V)` whose germs at `x` span `F_x` for every `x ∈ V`. -/
theorem exists_finite_sections_span_germ (F : X.Modules) [F.IsQuasicoherent]
    [SheafOfModules.IsFiniteType.{u, u, u} F] {V : X.Opens} (hV : IsAffineOpen V) :
    ∃ (I : Type u) (_ : Finite I) (t : I → Γ(F, V)), ∀ (x : X) (hx : x ∈ V),
      Submodule.span (R := (TopCat.Presheaf.stalk X.ringCatSheaf.obj x : RingCat))
        (Set.range fun i => (F.presheaf.germ V x hx).hom (t i)) = ⊤ := by
  have hfin := Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F hV
  obtain ⟨n, s, hs⟩ := @Module.Finite.exists_fin _ _ _ _ _ hfin
  refine ⟨ULift.{u} (Fin n), inferInstance, fun i => s i.down, fun x hx => ?_⟩
  have key : ∀ m : Γ(F, V), (F.presheaf.germ V x hx).hom m ∈
      Submodule.span (R := (TopCat.Presheaf.stalk X.ringCatSheaf.obj x : RingCat))
        (Set.range fun i : ULift.{u} (Fin n) => (F.presheaf.germ V x hx).hom (s i.down)) := by
    intro m
    have hm : m ∈ Submodule.span Γ(X, V) (Set.range s) := by rw [hs]; trivial
    induction hm using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        exact Submodule.subset_span ⟨⟨j⟩, rfl⟩
    | zero => simp
    | add y z _ _ ihy ihz =>
        rw [map_add]
        exact Submodule.add_mem _ ihy ihz
    | smul r y _ ih =>
        rw [Stacks.FinGenFromCover.ringStalk_germ_smul]
        exact Submodule.smul_mem _ _ ih
  rw [eq_top_iff, ← span_range_germ_sections_eq_top F hV hx, Submodule.span_le]
  rintro - ⟨m, rfl⟩
  exact key m

end Stacks.AffineGermSpan

end
