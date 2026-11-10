module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleHilbertPolynomial
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleInvertible
public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.OutsideImageDepth

/-!
# The Euler characteristic of an invertible coherent triple

Let `A` be a Noetherian local ring of depth at least three, let `f ∈ 𝔪` be a nonzerodivisor, and
let `(F, F₀, α)` be a coherent triple for `(A, f)` whose two members are invertible. The Euler
characteristic of the triple is then the length of the cokernel of the canonical map on global
sections

`Γ(U, F) ⟶ Γ(U₀, F₀|_{U₀})`,

`U` being the punctured spectrum of `A` and `U₀` the punctured closed fibre; in particular it is
nonnegative. This is the computation of [Stacks, Tag 0F28].

## Main results

* `Stacks.Algebraization.CoherentTriple.eulerCharacteristic_eq_length_cokernel`:
  **[Stacks, Tag 0F28]** — the Euler characteristic is the length of the cokernel of the
  canonical map on global sections.
* `Stacks.Algebraization.CoherentTriple.eulerCharacteristic_nonneg`: it is nonnegative.
* `Stacks.Algebraization.two_le_depth_globalSections_of_isIso_unit`: the global sections of a
  module of finite type on `Spec A` which is the direct image of its restriction to the punctured
  spectrum have depth at least two over `A`.

## Implementation notes

The Euler characteristic is computed on the prepared extension produced by
`Stacks.Algebraization.exists_preparedExtension_length_cokernel_eq`, namely the direct image of
the triple's punctured-spectrum member: there the cokernel of the closed-fibre map already has
the same length as the cokernel of the canonical map on global sections. What the formula adds is
that the *kernel* of that closed-fibre map vanishes, so that no correction term survives.

Vanishing of the kernel is `Stacks.Algebraization.injective_closedFibreMap_of_two_le_depth`, whose
two hypotheses on the global sections of the prepared extension are supplied here. Finiteness is
coherence of the direct image read through the tilde construction. Depth at least two is
[Stacks, Tag 0EY0] part (3) in the form
`Stacks.AlgebraicGeometry.PushforwardRegularity.two_le_depth_stalk_of_isIso_unit_of_notMem`,
applied at the closed point — the one point outside the punctured spectrum. That result is about
the stalk, and over a local ring the stalk of a module at the closed point is its module of global
sections, because the only open containing the closed point is the whole space; the germ map at
the closed point is therefore bijective, and it is semilinear over the identification of `A` with
the stalk of the structure sheaf there.

Both members of the triple are assumed invertible, as in the source. Invertibility of the member
on the punctured spectrum is what makes its direct image coherent and reflexive, hence recovered
from its own restriction; invertibility of the member on the closed fibre is what makes
restriction of global sections to the punctured closed fibre bijective. Both enter only through
`Stacks.Algebraization.exists_preparedExtension_length_cokernel_eq`.

## References

* [Stacks Project, Tag 0F28](https://stacks.math.columbia.edu/tag/0F28)
* [Stacks Project, Tag 0EY0](https://stacks.math.columbia.edu/tag/0EY0)
* [Stacks Project, Tag 0F25](https://stacks.math.columbia.edu/tag/0F25)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing Opposite
open TopologicalSpace

universe u

namespace Stacks.Algebraization

/-! ### Global sections and the stalk at the closed point -/

/-- **The germ map at the closed point of the spectrum of a local ring is bijective** on global
sections: the only open containing the closed point is the whole spectrum, so every germ there is
the germ of a global section, and two global sections with the same germ already agree. -/
public theorem bijective_germ_closedPoint (A : Type u) [CommRing A] [IsLocalRing A]
    (F : TopCat.Presheaf Ab.{u} (Spec (CommRingCat.of A)).toTopCat) :
    Function.Bijective (F.germ ⊤ (closedPoint A) trivial) := by
  refine ⟨fun s t h => ?_, fun s => ?_⟩
  · obtain ⟨V, hx, i, j, he⟩ := F.germ_eq (U := ⊤) (V := ⊤) (closedPoint A) trivial trivial s t h
    obtain rfl := (closedPoint_mem_iff V).mp hx
    rw [Subsingleton.elim i.op (𝟙 _), Subsingleton.elim j.op (𝟙 _)] at he
    erw [F.map_id] at he
    exact he
  · obtain ⟨V, hx, t, ht⟩ := F.exists_germ_eq s
    obtain rfl := (closedPoint_mem_iff V).mp hx
    exact ⟨t, ht⟩

/-- **The global sections of a module of finite type on `Spec A` which is the direct image of its
restriction to the punctured spectrum have depth at least two over `A`.**

This is [Stacks, Tag 0EY0] part (3) at the closed point, the one point outside the punctured
spectrum, transported from the stalk to the global sections along the germ map there, which is
bijective and semilinear over the identification of `A` with the stalk of the structure sheaf at
the closed point. -/
public theorem two_le_depth_globalSections_of_isIso_unit (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (G : (Spec (CommRingCat.of A)).Modules)
    [G.IsFiniteType]
    (hunit : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
      (Stacks.Divisors.puncturedSpectrum A).ι).unit.app G)) :
    2 ≤ Module.depth A (maximalIdeal A)
      ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj G) := by
  have hnot : (closedPoint A) ∉
      ((Stacks.Divisors.puncturedSpectrum A : (Spec (CommRingCat.of A)).Opens) :
        Set (Spec (CommRingCat.of A))) :=
    fun h => h rfl
  have hd :=
    Stacks.AlgebraicGeometry.PushforwardRegularity.two_le_depth_stalk_of_isIso_unit_of_notMem
      (Stacks.Divisors.puncturedSpectrum A) G hunit (closedPoint A) hnot
  let : IsLocalRing ↑((Spec (CommRingCat.of A)).presheaf.stalk (closedPoint A)) :=
    (Spec (CommRingCat.of A)).isLocalRing _
  let hst := AlgebraicGeometry.Scheme.Modules.moduleStalk G (closedPoint A)
  let e : A ≃+* ↑((Spec (CommRingCat.of A)).presheaf.stalk (closedPoint A)) :=
    (stalkClosedPointIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
  let : Algebra A ↑((Spec (CommRingCat.of A)).presheaf.stalk (closedPoint A)) :=
    e.toRingHom.toAlgebra
  let : Module A ↑(TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (closedPoint A)) :=
    Module.compHom _ e.toRingHom
  let : IsScalarTower A ↑((Spec (CommRingCat.of A)).presheaf.stalk (closedPoint A))
      ↑(TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (closedPoint A)) :=
    ⟨fun _ _ _ => mul_smul _ _ _⟩
  have hgerm : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (Spec (CommRingCat.of A)).presheaf.germ ⊤ (closedPoint A) trivial =
      (stalkClosedPointIso (CommRingCat.of A)).inv := by
    rw [← ΓSpecIso_hom_stalkClosedPointIso_inv]
    simp
  let g : ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj G) →ₗ[A]
      ↑(TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (closedPoint A)) :=
    { toFun := TopCat.Presheaf.germ G.val.presheaf ⊤ (closedPoint A) trivial
      map_add' := map_add _
      map_smul' := by
        intro a s
        change TopCat.Presheaf.germ G.val.presheaf ⊤ (closedPoint A) trivial
            (SMul.smul (M := Γ(Spec (CommRingCat.of A), ⊤)) (α := Γ(G, ⊤))
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) s) =
          e a • TopCat.Presheaf.germ G.val.presheaf ⊤ (closedPoint A) trivial s
        have h1 : TopCat.Presheaf.germ G.val.presheaf ⊤ (closedPoint A) trivial
              (SMul.smul (M := Γ(Spec (CommRingCat.of A), ⊤)) (α := Γ(G, ⊤))
                ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) s) =
            SMul.smul
              ((Spec (CommRingCat.of A)).presheaf.germ ⊤ (closedPoint A) trivial
                ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))
              (TopCat.Presheaf.germ G.val.presheaf ⊤ (closedPoint A) trivial s) :=
          PresheafOfModules.germ_smul G.val (closedPoint A) ⊤ trivial _ s
        exact h1.trans (congrArg (fun c => SMul.smul c
          (TopCat.Presheaf.germ G.val.presheaf ⊤ (closedPoint A) trivial s))
          (ConcreteCategory.congr_hom hgerm a)) }
  let E := LinearEquiv.ofBijective g (bijective_germ_closedPoint A G.val.presheaf)
  rwa [Module.depth_eq_depth_of_linearEquiv (maximalIdeal A) E,
    Module.depth_eq_depth_map_algebraMap e.surjective,
    show Ideal.map (algebraMap A ↑((Spec (CommRingCat.of A)).presheaf.stalk (closedPoint A)))
        (maximalIdeal A) =
      maximalIdeal ↑((Spec (CommRingCat.of A)).presheaf.stalk (closedPoint A)) from
      IsLocalRing.map_ringEquiv_maximalIdeal e]

/-! ### The Euler characteristic formula -/

/-- **Stacks Project, Tag 0F28.** For an invertible coherent triple over a Noetherian local ring
of depth at least three, the Euler characteristic of the triple is the length of the cokernel of
the canonical map on global sections.

The prepared extension taken is the direct image of the triple's punctured-spectrum member; its
closed-fibre map has a cokernel of the same length as that of the canonical map on global
sections, and its kernel vanishes because the global sections of that direct image have depth at
least two over `A`. -/
@[stacks 0F28 "the Euler characteristic formula"]
public theorem CoherentTriple.eulerCharacteristic_eq_length_cokernel (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (f : A) (hf : f ∈ maximalIdeal A) (hreg : IsRegular f)
    (T : CoherentTriple A f)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
      (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatSheaf.2 T.F]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (closedFibre A f).presheaf
      (closedFibre A f).ringCatSheaf.2 T.F₀]
    (hdepth : 3 ≤ Module.depth A (maximalIdeal A) A) :
    letI := puncturedSectionsModule A T.F
    letI := puncturedClosedFibreSectionsModule A f
      ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)
    T.eulerCharacteristic =
      ((Module.length A
        (Γ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀, ⊤) ⧸
          LinearMap.range (globalSectionsMap A f T))).toNat : ℤ) := by
  obtain ⟨P, hP, hlen, -⟩ :=
    exists_preparedExtension_length_cokernel_eq A f hf hreg T hdepth
  have hcP : _root_.SheafOfModules.IsCoherent P.F' := P.coherent
  have hfin : Module.Finite A ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj P.F') :=
    finite_globalSections_of_isCoherent P.F' P.coherent
  have hftP : P.F'.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType
  have hunit : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
      (Stacks.Divisors.puncturedSpectrum A).ι).unit.app P.F') :=
    ((Scheme.Modules.pullbackPushforwardAdjunction
      (Stacks.Divisors.puncturedSpectrum A).ι).unit.isIso_app_iff_of_iso
        (eqToIso hP)).mpr (isIso_unit_pushforward_puncturedSpectrum A T.F
          ((show (2 : ℕ∞) ≤ 3 by decide).trans hdepth))
  have : Mono P.closedFibreMap := (ModuleCat.mono_iff_injective _).mpr
    (injective_closedFibreMap_of_two_le_depth A f hf T P hfin
      (two_le_depth_globalSections_of_isIso_unit A P.F' hunit))
  have hsub : Subsingleton (kernel P.closedFibreMap).carrier :=
    ModuleCat.isZero_iff_subsingleton.mp (isZero_kernel_of_mono _)
  rw [T.eulerCharacteristic_eq_of_preparedExtension hf P]
  unfold PreparedExtension.eulerCharacteristic
  rw [Module.length_eq_zero (R := A) (M := (kernel P.closedFibreMap).carrier),
    ENat.toNat_zero, Int.natCast_zero, sub_zero]
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) hlen

/-- **The Euler characteristic of an invertible coherent triple is nonnegative**, being the
length of a cokernel. -/
@[stacks 0F28 "nonnegativity"]
public theorem CoherentTriple.eulerCharacteristic_nonneg (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (f : A) (hf : f ∈ maximalIdeal A) (hreg : IsRegular f)
    (T : CoherentTriple A f)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
      (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatSheaf.2 T.F]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (closedFibre A f).presheaf
      (closedFibre A f).ringCatSheaf.2 T.F₀]
    (hdepth : 3 ≤ Module.depth A (maximalIdeal A) A) :
    0 ≤ T.eulerCharacteristic := by
  rw [CoherentTriple.eulerCharacteristic_eq_length_cokernel A f hf hreg T hdepth]
  exact Int.natCast_nonneg _

end Stacks.Algebraization

end
