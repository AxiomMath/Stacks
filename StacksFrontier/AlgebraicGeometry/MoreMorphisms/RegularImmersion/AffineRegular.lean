module

public import StacksFrontier.AlgebraicGeometry.RegularImmersion.Affine

/-!
# Regular ideal sheaves are affine-locally weakly regular

Let `X` be a scheme and `J ⊆ O_X` a sheaf of ideals. Over an affine open `U` of `X`, a family of
sections of `O_X` over `U` is a regular sequence on `U` if and only if it is weakly regular in the
ring of sections `Γ(X, U)`. Hence `J` is regular if and only if, around each point of the support
of `O_X / J`, it is generated on an affine open by a family of sections which is weakly regular in
the ring of sections of that open.

## Main results

* `Stacks.AlgebraicGeometry.RegularIdealSheaf.isRegularSequenceOn_of_le`: regularity of a
  sequence of sections is inherited by smaller opens.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.isWeaklyRegular_of_isRegularSequenceOn`: over an
  affine open, a regular sequence of sections is weakly regular in the ring of sections.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.isRegularSequenceOn_iff_isWeaklyRegular`: the two
  conditions agree over an affine open.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.isRegularIdealSheaf_iff_exists_affine_generators`:
  a sheaf of ideals is regular if and only if it is generated affine-locally by weakly regular
  sequences.

## References

* [Stacks Project, Definition 31.20.1 (Tag 063D)](https://stacks.math.columbia.edu/tag/063D)
* [Stacks Project, Lemma 31.20.3 (Tag 063G)](https://stacks.math.columbia.edu/tag/063G)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasiRegular
open Stacks.RingedSpace

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

/-- On a quotient by an ideal, multiplication by `a` is injective as soon as `a` is a
nonzerodivisor modulo that ideal. -/
private theorem isSMulRegular_quotient_of_forall_mul_mem {R : Type*} [CommRing R] (I : Ideal R)
    (a : R) (h : ∀ x : R, a * x ∈ I → x ∈ I) : IsSMulRegular (R ⧸ I) a := by
  intro y₁ y₂ hy
  obtain ⟨x₁, rfl⟩ := Submodule.Quotient.mk_surjective I y₁
  obtain ⟨x₂, rfl⟩ := Submodule.Quotient.mk_surjective I y₂
  rw [Submodule.Quotient.eq]
  refine h _ ?_
  rwa [mul_sub, ← smul_eq_mul, ← smul_eq_mul, ← Submodule.Quotient.eq I]

/-- The germs of the predecessors of `fᵢ` generate the germ of the ideal that the predecessors
of `fᵢ` generate. -/
private theorem map_germ_Jid_precedingFamily (X : Scheme.{u}) (U : X.Opens) {r : ℕ}
    (f : Fin r → Γ(X, U)) (y : X) (hy : y ∈ U) (i : Fin r) :
    (Jid (precedingFamily f i)).map (X.presheaf.germ U y hy).hom =
      Jid (precedingFamily (germFamily X.toRingedSpace U f y hy) i) := by
  rw [Jid, Jid, Ideal.map_span]
  congr 1
  rw [show precedingFamily (germFamily X.toRingedSpace U f y hy) i =
    (X.presheaf.germ U y hy).hom ∘ precedingFamily f i from rfl, Set.range_comp]

/-- If a family of sections over `U` is a regular sequence on `U`, then its restriction to an open
`V ≤ U` is a regular sequence on `V`. -/
theorem isRegularSequenceOn_of_le (X : RingedSpace.{u, u}) {U V : Opens X} (hVU : V ≤ U) {r : ℕ}
    (f : Fin r → X.presheaf.obj (op U)) (h : IsRegularSequenceOn X U f) :
    IsRegularSequenceOn X V (fun i => X.presheaf.map (homOfLE hVU).op (f i)) := by
  rw [isRegularSequenceOn_iff_germ] at h ⊢
  intro y hy i τ hτ
  rw [germFamily_res U V hVU f y hy] at hτ ⊢
  exact h y (hVU hy) i τ hτ

/-- Over an affine open, a regular sequence of sections is weakly regular in the ring of
sections. -/
theorem isWeaklyRegular_of_isRegularSequenceOn (X : Scheme.{u}) (U : X.Opens)
    (hU : IsAffineOpen U) {r : ℕ} (f : Fin r → Γ(X, U))
    (h : IsRegularSequenceOn X.toRingedSpace U f) :
    RingTheory.Sequence.IsWeaklyRegular Γ(X, U) (List.ofFn f) := by
  rw [isRegularSequenceOn_iff_germ] at h
  refine (RingTheory.Sequence.isWeaklyRegular_iff _ _).mpr fun i hi => ?_
  obtain ⟨j, rfl⟩ : ∃ j : Fin r, j.1 = i := ⟨⟨i, by simpa using hi⟩, rfl⟩
  rw [show (List.ofFn f)[j.1] = f j from by simp,
    show Ideal.ofList ((List.ofFn f).take j.1) • (⊤ : Submodule Γ(X, U) Γ(X, U)) =
      Jid (precedingFamily f j) from ofList_take_ofFn f j]
  refine isSMulRegular_quotient_of_forall_mul_mem _ _ fun x hx => ?_
  refine hU.mem_ideal_iff.mpr fun y hyU => ?_
  rw [map_germ_Jid_precedingFamily X U f y hyU j]
  refine h y hyU j _ ?_
  rw [← map_germ_Jid_precedingFamily X U f y hyU j,
    show germFamily X.toRingedSpace U f y hyU j * (X.presheaf.germ U y hyU).hom x =
    (X.presheaf.germ U y hyU).hom (f j * x) from (map_mul _ _ _).symm]
  exact Ideal.mem_map_of_mem _ hx

/-- Over an affine open `U`, a family of sections is a regular sequence on `U` if and only if it is
weakly regular in `Γ(X, U)`. -/
theorem isRegularSequenceOn_iff_isWeaklyRegular (X : Scheme.{u}) (U : X.Opens)
    (hU : IsAffineOpen U) {r : ℕ} (f : Fin r → Γ(X, U)) :
    IsRegularSequenceOn X.toRingedSpace U f ↔
      RingTheory.Sequence.IsWeaklyRegular Γ(X, U) (List.ofFn f) :=
  ⟨isWeaklyRegular_of_isRegularSequenceOn X U hU f,
    isRegularSequenceOn_of_isWeaklyRegular X U hU f⟩

/-- A sheaf of ideals on a scheme is regular if and only if, around each point of the support of
its quotient, it is generated on an affine open by a family of sections which is weakly regular in
the ring of sections of that open. -/
theorem isRegularIdealSheaf_iff_exists_affine_generators (X : Scheme.{u})
    (J : (structureSheafModule X.toRingedSpace).Submodule) :
    IsRegularIdealSheaf X.toRingedSpace J ↔
      ∀ x : X, x ∈ idealQuotientSupport X.toRingedSpace J →
        ∃ (U : X.affineOpens) (_hx : x ∈ (U : Set X)) (r : ℕ) (f : Fin r → Γ(X, U.1)),
          IsGeneratedByOn X.toRingedSpace J U.1 f ∧
            RingTheory.Sequence.IsWeaklyRegular Γ(X, U.1) (List.ofFn f) := by
  refine ⟨fun h x hx => ?_, fun h => isRegularIdealSheaf_of_exists_affine_generators X J
    fun x hx => let ⟨U, hxU, r, f, hgen, hwr⟩ := h x hx; ⟨U.1, U.2, hxU, r, f, hgen, hwr⟩⟩
  obtain ⟨U₀, hxU₀, r, f, hreg, hgen⟩ := h x hx
  obtain ⟨V, hV, hxV, hVU₀⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxU₀
  exact ⟨⟨V, hV⟩, hxV, r, fun i => X.presheaf.map (homOfLE hVU₀).op (f i),
    isGeneratedByOn_of_le U₀ f hgen V hVU₀,
    isWeaklyRegular_of_isRegularSequenceOn X V hV _
      (isRegularSequenceOn_of_le X.toRingedSpace hVU₀ f hreg)⟩

end Stacks.AlgebraicGeometry.RegularIdealSheaf

end
