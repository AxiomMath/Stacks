module

public import StacksFrontier.AlgebraicGeometry.AnnihilatorQcoh.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The stalks of the subsheaf of sections annihilated by an ideal sheaf

Let `X` be a scheme, `I` a quasi-coherent ideal subsheaf of `𝒪_X` of finite type and `F` an
`𝒪_X`-module, and let `N` be the subsheaf of `F` of sections annihilated by `I`. This file
identifies the image of the stalk of `N` at a point `x` inside the stalk of `F`: it consists
exactly of the germs annihilated by `I` at `x`. This is part (3) of [Stacks, Tag 01PO].

## Main results

* `IsAnnihilatorSubsheaf.exists_stalk_eq_iff`: **part (3) of [Stacks, Tag 01PO]** — a germ of
  `F` at `x` comes from the stalk of `N` exactly when, for every representative of it over
  every open neighbourhood, every section of `I` there kills it to first order.

## Implementation notes

The statement is phrased through representatives rather than through a module structure on the
stalk: `I_x · s = 0` would require the `𝒪_{X,x}`-module structure on the stalk of `F`, whose
spelling in Mathlib is an explicit `PresheafOfModules` instance that does not agree
syntactically with the sheaf-of-rings one, and all three forms of the condition are equivalent
because every germ has a representative. Nothing is lost: each germ of `I` at `x` is the germ of
a section over some neighbourhood, and the condition on representatives is exactly `I_x · s = 0`
read through `germ (r • t) = germ r • germ t`.

The forward implication needs neither quasi-coherence nor finiteness: a germ in the image is
represented by a section of `N`, two representatives of the same germ agree on a smaller
neighbourhood, and `IsAnnihilatorSubsheaf.smul_eq_zero` kills the product there.

The backward implication is where the hypotheses enter, and it is the same uniform-exponent
argument as for quasi-coherence read one step down. A representative `t₀` over an **affine**
neighbourhood `U₀` exists because the affine opens are a basis. Each element of a finite
generating family of `Γ(I, U₀)` kills `t₀` on some neighbourhood of `x`; the finitely many
neighbourhoods are intersected, and the result shrunk to a basic open `X.basicOpen f ∋ x` inside
`U₀`, which is again affine. There the generators kill the restricted section, hence so does all
of `Γ(I, U₀)` (`smul_eq_zero_of_span_eq_top`), hence so does all of `Γ(I, X.basicOpen f)`
(`exists_pow_smul_mem_image`, `f` being a unit on its own basic open). The affine description of
the sections of `N` puts the restricted section into `N`, and its germ is the required element.

## References

* [Stacks Project, Tag 01PO](https://stacks.math.columbia.edu/tag/01PO)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.AlgebraicGeometry.AnnihilatorQcoh

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule}
  {F : X.Modules} {N : F.Submodule}

/-- A point of a finite intersection of opens, taken in the lattice of opens. -/
theorem mem_finset_inf {ι : Type*} (W : ι → X.Opens) (x : X)
    (S : Finset ι) (h : ∀ i ∈ S, x ∈ W i) : x ∈ S.inf W :=
  Finset.inf_induction (p := (x ∈ ·)) (Set.mem_univ x) (fun _ h₁ _ h₂ ↦ ⟨h₁, h₂⟩) h

/-- Restricting along two composable inclusions is restricting along the composite. -/
private theorem map_map_eq_map {A B C : X.Opens} (i : A ⟶ B) (j : B ⟶ C) (k : A ⟶ C)
    (a : Γ(F, C)) :
    F.presheaf.map i.op (F.presheaf.map j.op a) = F.presheaf.map k.op a := by
  rw [← F.presheaf.map_comp_apply]
  rfl

/-- A germ in the image of the stalk of the annihilator subsheaf is killed, to first order, by
every section of `I` over a neighbourhood of the point. -/
private theorem IsAnnihilatorSubsheaf.germ_smul_eq_zero_of_exists_stalk_eq
    (hN : IsAnnihilatorSubsheaf I F N) {x : X} {s : F.presheaf.stalk x}
    (hs : ∃ t : (Scheme.Modules.presheaf N.toSheafOfModules).stalk x,
        (TopCat.Presheaf.stalkFunctor Ab.{u} x).map (Scheme.Modules.Hom.mapPresheaf N.ι) t = s)
    (U : X.Opens) (hx : x ∈ U) (t : Γ(F, U)) (ht : F.presheaf.germ U x hx t = s)
    (r : Γ(X, U)) (hr : r ∈ I.toSubmodule.obj (op U)) :
    F.presheaf.germ U x hx (r • t) = 0 := by
  obtain ⟨g, hg⟩ := hs
  obtain ⟨V, hxV, b, hb⟩ :=
    TopCat.Presheaf.exists_germ_eq (Scheme.Modules.presheaf N.toSheafOfModules) g
  have hsV : F.presheaf.germ V x hxV (subVal N b) = s := by
    rwa [← hb, TopCat.Presheaf.stalkFunctor_map_germ_apply] at hg
  have h1 : F.presheaf.germ (U ⊓ V) x ⟨hx, hxV⟩
      (F.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op t) = s :=
    (TopCat.Presheaf.germ_res_apply F.presheaf
      (homOfLE (inf_le_left : U ⊓ V ≤ U)) x ⟨hx, hxV⟩ t).trans ht
  have h2 : F.presheaf.germ (U ⊓ V) x ⟨hx, hxV⟩
      (F.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op (subVal N b)) = s :=
    (TopCat.Presheaf.germ_res_apply F.presheaf
      (homOfLE (inf_le_right : U ⊓ V ≤ V)) x ⟨hx, hxV⟩ (subVal N b)).trans hsV
  obtain ⟨W, hxW, i₁, i₂, heq⟩ := F.presheaf.germ_eq x
    (show x ∈ U ⊓ V from ⟨hx, hxV⟩) (show x ∈ U ⊓ V from ⟨hx, hxV⟩) _ _ (h1.trans h2.symm)
  have hWU : W ≤ U := le_trans i₁.le inf_le_left
  have hWV : W ≤ V := le_trans i₂.le inf_le_right
  have hts : F.presheaf.map (homOfLE hWU).op t =
      subVal N ((Scheme.Modules.presheaf N.toSheafOfModules).map (homOfLE hWV).op b) := by
    rw [← map_map_eq_map i₁ (homOfLE (inf_le_left : U ⊓ V ≤ U)) (homOfLE hWU), heq,
      map_map_eq_map i₂ (homOfLE (inf_le_right : U ⊓ V ≤ V)) (homOfLE hWV)]
    rfl
  have hzero : F.presheaf.map (homOfLE hWU).op (r • t) = 0 := by
    rw [Scheme.Modules.map_smul, hts]
    exact hN.smul_section_eq_zero W (subVal_mem N _) _ (I.toSubmodule.map_mem _ hr)
  rw [← TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE hWU) x hxW (r • t), hzero, map_zero]

/-- A germ killed to first order by every section of `I` over a neighbourhood of the point comes
from the stalk of the annihilator subsheaf. -/
private theorem IsAnnihilatorSubsheaf.exists_stalk_eq_of_germ_smul_eq_zero
    (hN : IsAnnihilatorSubsheaf I F N)
    [I.toSheafOfModules.IsQuasicoherent] [I.toSheafOfModules.IsFiniteType]
    {x : X} {s : F.presheaf.stalk x}
    (h : ∀ (U : X.Opens) (hx : x ∈ U) (t : Γ(F, U)), F.presheaf.germ U x hx t = s →
        ∀ r : Γ(X, U), r ∈ I.toSubmodule.obj (op U) →
          F.presheaf.germ U x hx (r • t) = 0) :
    ∃ t : (Scheme.Modules.presheaf N.toSheafOfModules).stalk x,
      (TopCat.Presheaf.stalkFunctor Ab.{u} x).map (Scheme.Modules.Hom.mapPresheaf N.ι) t = s := by
  classical
  obtain ⟨U₀, hx₀, hU₀ : IsAffineOpen U₀, t₀, ht₀⟩ :=
    TopCat.Presheaf.exists_mem_germ_eq_of_isBasis X.isBasis_affineOpens F.presheaf x s
  obtain ⟨T, hT⟩ := exists_finset_span_eq_top I hU₀
  have hgen : ∀ z ∈ T, ∃ (W : X.Opens) (_ : x ∈ W) (hWU : W ≤ U₀),
      F.presheaf.map (homOfLE hWU).op (idealVal I z • t₀) = 0 := by
    intro z _
    obtain ⟨W, hxW, i₁, _, heq⟩ := F.presheaf.germ_eq x hx₀ hx₀ (idealVal I z • t₀)
      (0 : Γ(F, U₀)) (by rw [h U₀ hx₀ t₀ ht₀ _ (idealVal_mem I z), map_zero])
    exact ⟨W, hxW, i₁.le, heq.trans (map_zero _)⟩
  choose! Wz hxWz hWzU hWz using hgen
  set W : X.Opens := U₀ ⊓ (T.inf Wz : X.Opens)
  have hxinf : x ∈ W := ⟨hx₀, mem_finset_inf Wz x T hxWz⟩
  obtain ⟨f, hfle, hxf⟩ := hU₀.exists_basicOpen_le (show W from ⟨x, hxinf⟩) hx₀
  have hDU₀ : X.basicOpen f ≤ U₀ := X.basicOpen_le f
  have hDWz : ∀ z ∈ T, X.basicOpen f ≤ Wz z := fun z hz ↦
    le_trans hfle (le_trans (show W ≤ (T.inf Wz : X.Opens) from inf_le_right)
      (Finset.inf_le hz))
  let := moduleOfLE F hDU₀
  have hgenD : ∀ z ∈ T, idealVal I z •
      F.presheaf.map (homOfLE hDU₀).op t₀ = (0 : Γ(F, X.basicOpen f)) := by
    intro z hz
    have hrestr := congrArg (F.presheaf.map (homOfLE (hDWz z hz)).op) (hWz z hz)
    rw [map_zero, map_map_eq_map _ _ (homOfLE hDU₀)] at hrestr
    rwa [Scheme.Modules.map_smul] at hrestr
  have hmem : F.presheaf.map (homOfLE hDU₀).op t₀ ∈
      N.toSubmodule.obj (op (X.basicOpen f)) := by
    refine (hN.mem_iff_of_isAffineOpen (hU₀.basicOpen f) _).mpr fun b hb ↦ ?_
    obtain ⟨k, r, hrmem, hr⟩ := exists_pow_smul_mem_image I hU₀ f b hb
    have hunit : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ k)) := by
      simpa using (isUnit_map_of_le_basicOpen f le_rfl).pow k
    refine eq_zero_of_isUnit_smul_eq_zero hunit ?_
    rw [smul_smul, hr]
    exact smul_eq_zero_of_span_eq_top I (T : Set Γ(I.toSheafOfModules, U₀)) hT _ hgenD r hrmem
  have hstalk := TopCat.Presheaf.stalkFunctor_map_germ_apply (C := Ab.{u})
    (X.basicOpen f) x hxf (Scheme.Modules.Hom.mapPresheaf N.ι)
    (show Γ(N.toSheafOfModules, X.basicOpen f) from
      ⟨F.presheaf.map (homOfLE hDU₀).op t₀, hmem⟩)
  refine ⟨_, hstalk.trans ?_⟩
  change F.presheaf.germ (X.basicOpen f) x hxf (F.presheaf.map (homOfLE hDU₀).op t₀) = s
  exact (TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE hDU₀) x hxf t₀).trans ht₀

/-- **Part (3) of [Stacks, Tag 01PO].** A germ of `F` at `x` lies in the image of the stalk of
the annihilator subsheaf exactly when every section of `I` over a neighbourhood of `x`
annihilates every representative of that germ, to first order at `x`.

Quasi-coherence of `F` is not needed: the forward implication uses no hypothesis beyond the
sheaf axiom, and the backward one goes through the affine description of the sections of `N`,
which needs only `I`. -/
@[stacks 01PO "part (3)"]
theorem IsAnnihilatorSubsheaf.exists_stalk_eq_iff (hN : IsAnnihilatorSubsheaf I F N)
    [I.toSheafOfModules.IsQuasicoherent] [I.toSheafOfModules.IsFiniteType]
    (x : X) (s : F.presheaf.stalk x) :
    (∃ t : (Scheme.Modules.presheaf N.toSheafOfModules).stalk x,
        (TopCat.Presheaf.stalkFunctor Ab.{u} x).map
          (Scheme.Modules.Hom.mapPresheaf N.ι) t = s) ↔
      ∀ (U : X.Opens) (hx : x ∈ U) (t : Γ(F, U)), F.presheaf.germ U x hx t = s →
        ∀ r : Γ(X, U), r ∈ I.toSubmodule.obj (op U) →
          F.presheaf.germ U x hx (r • t) = 0 :=
  ⟨fun hs ↦ hN.germ_smul_eq_zero_of_exists_stalk_eq hs, hN.exists_stalk_eq_of_germ_smul_eq_zero⟩

end Stacks.AlgebraicGeometry.AnnihilatorQcoh

end
