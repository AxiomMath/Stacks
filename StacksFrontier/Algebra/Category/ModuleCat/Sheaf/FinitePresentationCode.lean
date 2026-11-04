module

public import StacksFrontier.CategoryTheory.Preadditive.CofanMatrix
public import StacksFrontier.AlgebraicGeometry.Topologies.GlobalPresentationComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite

/-!
# Isomorphism classes of sheaves of modules with a finite global presentation

A sheaf of modules with a finite global presentation is a cokernel of a morphism between two
finite coproducts of copies of the structure sheaf, and such a cokernel is determined up to
isomorphism by the matrix of that morphism, a finite matrix of global sections of the structure
sheaf. So the sheaves of modules with a finite global presentation have at most as many
isomorphism classes as there are finite matrices of global sections: this file records the
*code* of a finite global presentation and the fact that two sheaves with the same code are
isomorphic.

## Main definitions

* `SheafOfModules.PresentationCode`: the type of codes, a size of a matrix and a matrix of
  endomorphisms of the universe-lifted structure sheaf.
* `SheafOfModules.FinitePresentationData`: the data of a finite global presentation, whose
  existence is `SheafOfModules.HasFiniteGlobalPresentation`.

## Main results

* `SheafOfModules.FinitePresentationData.nonempty_iso_of_code_eq`: two sheaves of modules with
  finite global presentations of the same code are isomorphic.
* `SheafOfModules.mk_presentationCode_le`: there are at most `max ℵ₀ #E` codes, `E` the
  endomorphisms of the lifted structure sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe t u v w

/-- A countable family of types of cardinality at most an infinite cardinal `c` has a sigma type
of cardinality at most `c`. -/
theorem Cardinal.mk_sigma_nat_le {Y : ℕ → Type t} {c : Cardinal.{t}} (hc : ℵ₀ ≤ c)
    (h : ∀ n, #(Y n) ≤ c) : #(Σ n, Y n) ≤ c := by
  rw [Cardinal.mk_sigma]
  calc sum (fun n => #(Y n)) ≤ sum (fun _ : ℕ => c) := sum_le_sum _ _ h
    _ = lift.{t} #ℕ * lift.{0} c := sum_const _ _
    _ = ℵ₀ * c := by simp
    _ ≤ c := (mul_le_max_of_aleph0_le_right hc).trans (by simp [hc])

/-- A finite matrix with entries in a type of cardinality at most an infinite cardinal `c` lies in
a type of cardinality at most `c`. -/
theorem Cardinal.mk_fin_fin_le {E : Type t} {c : Cardinal.{t}} (hc : ℵ₀ ≤ c) (hE : #E ≤ c)
    (k n : ℕ) : #(Fin k → Fin n → E) ≤ c := by
  have h₀ : ∀ (m : ℕ) (F : Type t), #F ≤ c → #(Fin m → F) ≤ c := fun m F hF => by
    rw [show #(Fin m → F) = #F ^ (m : Cardinal) by simp]
    exact (power_le_power_right hF).trans (power_nat_le hc)
  exact h₀ k _ (h₀ n E hE)

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

variable (R) in
/-- **The codes of finite global presentations**: a pair of sizes and a matrix of endomorphisms
of the universe-lifted structure sheaf. -/
abbrev PresentationCode :=
  Σ n k : ℕ, Fin k → Fin n →
    (uliftForPresentation.{u, v, w, w, max u v w} (unit R) ⟶
      uliftForPresentation.{u, v, w, w, max u v w} (unit R))

/-- **The data of a finite global presentation** of a sheaf of modules: a cokernel of a morphism
between two finite coproducts of copies of the structure sheaf, everything raised to the
universe of `SheafOfModules.HasFiniteGlobalPresentation`. -/
structure FinitePresentationData (M : SheafOfModules.{w} R) where
  /-- The number of generators. -/
  n : ℕ
  /-- The number of relations. -/
  k : ℕ
  /-- The coproduct of the generators. -/
  P : SheafOfModules.{max u v w} R
  /-- The coproduct of the relations. -/
  Q : SheafOfModules.{max u v w} R
  /-- The inclusions of the generators. -/
  ι : Fin n → (uliftForPresentation.{u, v, w, w, max u v w} (unit R) ⟶ P)
  /-- The inclusions of the relations. -/
  κ : Fin k → (uliftForPresentation.{u, v, w, w, max u v w} (unit R) ⟶ Q)
  /-- `P` is the coproduct. -/
  hP : IsColimit (Cofan.mk P ι)
  /-- `Q` is the coproduct. -/
  hQ : IsColimit (Cofan.mk Q κ)
  /-- The relations. -/
  a : Q ⟶ P
  /-- The presentation map. -/
  b : P ⟶ uliftForPresentation.{u, v, w, w, max u v w} M
  /-- The relations are killed. -/
  hab : a ≫ b = 0
  /-- The lifted module is the cokernel. -/
  hc : IsColimit (CokernelCofork.ofπ b hab)

/-- A sheaf of modules with a finite global presentation admits finite presentation data. -/
theorem nonempty_finitePresentationData {M : SheafOfModules.{w} R}
    (h : M.HasFiniteGlobalPresentation) : Nonempty (FinitePresentationData M) := by
  obtain ⟨n, k, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hc⟩⟩ := h
  exact ⟨⟨n, k, P, Q, ι, κ, hP, hQ, a, b, hab, hc⟩⟩

namespace FinitePresentationData

variable {M M' : SheafOfModules.{w} R}

/-- The code of a finite global presentation: its sizes and the matrix of its relations. -/
def code (d : FinitePresentationData M) : PresentationCode R :=
  ⟨d.n, d.k, cofanMatrix d.hP d.κ d.a⟩

/-- **Two sheaves of modules with finite global presentations of the same code are
isomorphic.** -/
theorem nonempty_iso_of_code_eq (d : FinitePresentationData M) (d' : FinitePresentationData M')
    (h : d.code = d'.code) : Nonempty (M ≅ M') := by
  obtain ⟨n, k, P, Q, ι, κ, hP, hQ, a, b, hab, hc⟩ := d
  obtain ⟨n', k', P', Q', ι', κ', hP', hQ', a', b', hab', hc'⟩ := d'
  simp only [code, Sigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  have h' := eq_of_heq h
  simp only [Sigma.mk.injEq] at h'
  obtain ⟨rfl, h''⟩ := h'
  let e : (Stacks.SheafOfModules.moduleULift.{max u v w, w} R).obj M ≅
      (Stacks.SheafOfModules.moduleULift.{max u v w, w} R).obj M' :=
    isoOfCofanMatrixEq hP hQ hP' hQ' hc hc' (eq_of_heq h'')
  exact ⟨(Stacks.SheafOfModules.moduleULiftFullyFaithful.{max u v w, w} R).preimageIso e⟩

/-- **A morphism out of a sheaf of modules with a finite global presentation is determined by
the images of the generators**, finitely many global sections of the target. -/
theorem exists_injective_hom (d : FinitePresentationData M) (N : SheafOfModules.{w} R) :
    ∃ u : (M ⟶ N) → (Fin d.n → N.sections), Function.Injective u := by
  refine ⟨fun f i => Stacks.SheafOfModules.uliftForPresentationSectionsEquiv N
    (d.ι i ≫ d.b ≫ Stacks.SheafOfModules.uliftForPresentationHomEquiv _ _ f), ?_⟩
  intro f g h
  apply (Stacks.SheafOfModules.uliftForPresentationHomEquiv _ _).injective
  have hb : Epi d.b := Cofork.IsColimit.epi d.hc
  refine (cancel_epi d.b).1 (Cofan.IsColimit.hom_ext d.hP _ _ fun i => ?_)
  have h' := (Stacks.SheafOfModules.uliftForPresentationSectionsEquiv N).injective (congrFun h i)
  simpa only [cofan_mk_inj, Category.assoc] using h'

end FinitePresentationData

/-- **There are at most `max ℵ₀ #E` codes**, `E` the endomorphisms of the lifted structure
sheaf. -/
theorem mk_presentationCode_le :
    #(PresentationCode R) ≤ max ℵ₀
      #(uliftForPresentation.{u, v, w, w, max u v w} (unit R) ⟶
        uliftForPresentation.{u, v, w, w, max u v w} (unit R)) := by
  have hc : ℵ₀ ≤ max ℵ₀ #(uliftForPresentation.{u, v, w, w, max u v w} (unit R) ⟶
      uliftForPresentation.{u, v, w, w, max u v w} (unit R)) := le_max_left _ _
  exact mk_sigma_nat_le hc fun n => mk_sigma_nat_le hc fun k =>
    mk_fin_fin_le hc (le_max_right _ _) k n

end SheafOfModules

end
