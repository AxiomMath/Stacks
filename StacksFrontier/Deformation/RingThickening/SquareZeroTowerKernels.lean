module

public import StacksFrontier.Algebra.Category.CommAlgCat.SectionsLimit
public import StacksFrontier.Deformation.RingThickening.SquareZeroKernelModule

/-!
# The kernels of a square-zero tower of algebras

Let `(Rₙ)` be an inverse system of commutative `Λ`-algebras indexed by `ℕ` whose transition maps
are surjective with square-zero kernels, and let `R = lim Rₙ`. The kernels
`Iₙ = Ker(Rₙ → R₀)` are `R₀`-modules (`RingHom.squareZeroKer`) and form an inverse system of
`R₀`-modules, and the kernel `Ker(R → R₀)` of the limit is their limit:

`0 → lim Iₙ → lim Rₙ → R₀ → 0`.

This is the exact sequence `0 → lim Iₙ → lim Rₙ → R₁ → 0` of the body of
[Stacks Project, Tag 0D3X] (the source indexes from `1`), over which the extension
`0 → 𝒪_{X₁} ⊗_{R₁} lim Iₙ → 𝒪' → 𝒪_{X₁} → 0` is formed.

## Main definitions

* `CommAlgCat.towerKernelSystem`: the inverse system `n ↦ Iₙ` of `R₀`-modules.
* `CommAlgCat.towerKernelCone`: the cone over it with vertex `Ker(R → R₀)`, `R = lim Rₙ`.

## Main results

* `CommAlgCat.surjective_towerLimit_π_zero`, `CommAlgCat.ker_towerLimit_π_zero_sq_eq_bot`:
  `R → R₀` is surjective with square-zero kernel.
* `CommAlgCat.isLimitTowerKernelCone`: `Ker(R → R₀) = lim Iₙ`.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CommAlgCat

variable {Λ : Type u} [CommRing Λ] (R : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ)
  (hsurj : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), Function.Surjective (R.map f).hom)
  (hsq : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), RingHom.ker (R.map f).hom.toRingHom ^ 2 = ⊥)

/-- The projection `Rₙ → R₀` of the tower. -/
abbrev towerProjection (n : ℕᵒᵖ) : R.obj n →+* R.obj (op 0) :=
  (R.map (homOfLE (Nat.zero_le n.unop)).op).hom.toRingHom

/-- The projection `Rₙ → R₀` composed with a transition map `Rₘ → Rₙ` is the projection
`Rₘ → R₀`. -/
theorem towerProjection_comp {m n : ℕᵒᵖ} (f : m ⟶ n) :
    (towerProjection R n).comp (R.map f).hom.toRingHom = towerProjection R m := by
  show ((R.map f ≫ R.map (homOfLE (Nat.zero_le n.unop)).op).hom.toRingHom) = _
  rw [← R.map_comp]
  rfl

/-- **The inverse system of the kernels `Iₙ = Ker(Rₙ → R₀)`**, as `R₀`-modules. -/
def towerKernelSystem : ℕᵒᵖ ⥤ ModuleCat.{u} (R.obj (op 0)) where
  obj n := RingHom.squareZeroKer (towerProjection R n) (hsurj _) (hsq _)
  map {m n} f := RingHom.squareZeroKerMap (towerProjection R n) (hsurj _) (hsq _)
    (towerProjection R m) (hsurj _) (hsq _) (R.map f).hom.toRingHom (towerProjection_comp R f)
  map_id n := by
    ext x
    exact Subtype.ext (congrArg (fun φ : R.obj n ⟶ R.obj n => φ.hom x.1) (R.map_id n))
  map_comp {l m n} f g := by
    ext x
    exact Subtype.ext (congrArg (fun φ : R.obj l ⟶ R.obj n => φ.hom x.1) (R.map_comp f g))

/-- **The transition maps `I_{n+1} ⟶ Iₙ` of the kernels are surjective**: a preimage in `R_{n+1}`
of an element of `Iₙ` lies in `I_{n+1}`. -/
theorem surjective_towerKernelSystem_map (n : ℕ) :
    Function.Surjective ((towerKernelSystem R hsurj hsq).map (homOfLE (Nat.le_succ n)).op) := by
  intro x
  obtain ⟨y, hy⟩ := hsurj (homOfLE (Nat.le_succ n)).op x.1
  refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
  rw [RingHom.mem_ker, ← towerProjection_comp R (homOfLE (Nat.le_succ n)).op, RingHom.comp_apply]
  show towerProjection R (op n) ((R.map (homOfLE (Nat.le_succ n)).op).hom y) = 0
  rw [hy]
  exact x.2

/-- The forgetful functor of commutative algebras preserves limits, through the equivalence with
commutative rings under the base ring. -/
theorem forget_preservesLimitsOfShape_nat :
    PreservesLimitsOfShape ℕᵒᵖ (forget (CommAlgCat.{u} Λ)) := by
  show PreservesLimitsOfShape ℕᵒᵖ ((commAlgCatEquivUnder (CommRingCat.of Λ)).functor ⋙
    Under.forget (CommRingCat.of Λ) ⋙ forget CommRingCat)
  infer_instance

variable {R} (cR : Cone R) (hcR : IsLimit cR)

/-- The projection `R → R₀` from the vertex of a cone of the tower. -/
abbrev towerLimitProjection : cR.pt →+* R.obj (op 0) := (cR.π.app (op 0)).hom.toRingHom

include hcR hsurj in
/-- **`lim Rₙ → R₀` is surjective.** -/
theorem surjective_towerLimit_π_zero : Function.Surjective (towerLimitProjection cR) := by
  have := forget_preservesLimitsOfShape_nat (Λ := Λ)
  exact Concrete.surjective_π_app_zero_of_surjective_map hcR fun n => hsurj _

/-- The projection `Rₙ → R₀` of the image of `c` under the cone projection `R → Rₙ` is the
projection of `c`. -/
private theorem towerProjection_π_apply (n : ℕᵒᵖ) (c : cR.pt) :
    towerProjection R n ((cR.π.app n).hom c) = towerLimitProjection cR c := by
  show (cR.π.app n ≫ R.map (homOfLE (Nat.zero_le n.unop)).op) c = _
  rw [cR.w]
  rfl

include hcR hsq in
/-- **`Ker(lim Rₙ → R₀)` has square zero.** -/
theorem ker_towerLimit_π_zero_sq_eq_bot :
    RingHom.ker (towerLimitProjection cR) ^ 2 = ⊥ := by
  have := forget_preservesLimitsOfShape_nat (Λ := Λ)
  refine le_bot_iff.mp ?_
  rw [pow_two, Submodule.mul_le]
  intro a ha b hb
  rw [Ideal.mem_bot]
  refine Concrete.isLimit_ext R hcR _ _ fun n => ?_
  have hmem : ∀ c : cR.pt, c ∈ RingHom.ker (towerLimitProjection cR) →
      cR.π.app n c ∈ RingHom.ker (towerProjection R n) := by
    intro c hc
    rw [RingHom.mem_ker] at hc ⊢
    exact (towerProjection_π_apply cR n c).trans hc
  have h := Ideal.mul_mem_mul (hmem a ha) (hmem b hb)
  rw [← pow_two, hsq, Ideal.mem_bot] at h
  show (cR.π.app n).hom (a * b) = (cR.π.app n).hom 0
  rw [map_mul, map_zero]
  exact h

/-- The projection `Rₙ → R₀` composed with the cone projection `R → Rₙ` is the projection
`R → R₀`. -/
theorem towerProjection_comp_π (n : ℕᵒᵖ) :
    (towerProjection R n).comp (cR.π.app n).hom.toRingHom = towerLimitProjection cR := by
  exact RingHom.ext (towerProjection_π_apply cR n)

/-- **The cone `Ker(lim Rₙ → R₀) ⟶ Iₙ`** over the inverse system of kernels. -/
def towerKernelCone : Cone (towerKernelSystem R hsurj hsq) where
  pt := RingHom.squareZeroKer (towerLimitProjection cR) (surjective_towerLimit_π_zero hsurj cR hcR)
    (ker_towerLimit_π_zero_sq_eq_bot hsq cR hcR)
  π :=
    { app n := RingHom.squareZeroKerMap (towerProjection R n) (hsurj _) (hsq _)
        (towerLimitProjection cR) _ _ (cR.π.app n).hom.toRingHom (towerProjection_comp_π cR n)
      naturality {m n} f := by
        ext x
        refine Subtype.ext ?_
        change (cR.π.app n).hom x.1 = (R.map f).hom ((cR.π.app m).hom x.1)
        rw [← cR.w f]
        rfl }

/-- **`Ker(lim Rₙ → R₀) = lim Iₙ`.** -/
def isLimitTowerKernelCone : IsLimit (towerKernelCone hsurj hsq cR hcR) := by
  haveI := forget_preservesLimitsOfShape_nat (Λ := Λ)
  letI := RingHom.squareZeroKerModule (towerLimitProjection cR)
    (surjective_towerLimit_π_zero hsurj cR hcR) (ker_towerLimit_π_zero_sq_eq_bot hsq cR hcR)
  let hT := isLimitOfPreserves (forget (CommAlgCat.{u} Λ)) hcR
  let lift₀ (s : Cone (towerKernelSystem R hsurj hsq)) (x : s.pt) : cR.pt :=
    (Types.isLimitEquivSections hT).symm
      ⟨fun n => ((s.π.app n).hom x).1, fun {m n} f => by
        have := congrArg (fun φ => (φ.hom x).1) (s.w f)
        exact this⟩
  have hlift₀ (s : Cone (towerKernelSystem R hsurj hsq)) (x : s.pt) (n : ℕᵒᵖ) :
      (cR.π.app n).hom (lift₀ s x) = ((s.π.app n).hom x).1 :=
    Types.isLimitEquivSections_symm_apply hT _ n
  have hker (s : Cone (towerKernelSystem R hsurj hsq)) (x : s.pt) :
      lift₀ s x ∈ RingHom.ker (towerLimitProjection cR) := by
    rw [RingHom.mem_ker]
    refine (hlift₀ s x (op 0)).trans ?_
    have h0 := ((s.π.app (op 0)).hom x).2
    rw [RingHom.mem_ker] at h0
    simpa [towerProjection] using h0
  refine
    { lift s := ModuleCat.ofHom
        { toFun x := ⟨lift₀ s x, hker s x⟩
          map_add' x y := Subtype.ext (Concrete.isLimit_ext R hcR _ _ fun n => by
            change (cR.π.app n).hom (lift₀ s (x + y)) =
              (cR.π.app n).hom (lift₀ s x + lift₀ s y)
            rw [map_add, hlift₀, hlift₀, hlift₀, map_add]
            rfl)
          map_smul' b x := by
            obtain ⟨a, rfl⟩ := surjective_towerLimit_π_zero hsurj cR hcR b
            refine Subtype.ext (Concrete.isLimit_ext R hcR _ _ fun n => ?_)
            have e1 : towerLimitProjection cR a = towerProjection R n ((cR.π.app n).hom a) :=
              (RingHom.congr_fun (towerProjection_comp_π cR n) a).symm
            have hL : (cR.π.app n).hom (lift₀ s (towerLimitProjection cR a • x)) =
                (cR.π.app n).hom a * ((s.π.app n).hom x).1 := by
              rw [hlift₀, map_smul, e1]
              exact RingHom.squareZeroKerModule_smul (towerProjection R n) (hsurj _) (hsq _) _ _
            refine hL.trans ?_
            rw [RingHom.id_apply]
            change _ = (cR.π.app n).hom ((towerLimitProjection cR a •
              (⟨lift₀ s x, hker s x⟩ : RingHom.ker (towerLimitProjection cR)) :
                RingHom.ker (towerLimitProjection cR)) : cR.pt)
            rw [RingHom.squareZeroKerModule_smul, map_mul, hlift₀] }
      fac s n := by
        ext x
        exact Subtype.ext (hlift₀ s x n)
      uniq s m hm := by
        ext x
        refine Subtype.ext (Concrete.isLimit_ext R hcR _ _ fun n => ?_)
        refine Eq.trans ?_ (hlift₀ s x n).symm
        rw [← hm n]
        rfl }

end CommAlgCat
