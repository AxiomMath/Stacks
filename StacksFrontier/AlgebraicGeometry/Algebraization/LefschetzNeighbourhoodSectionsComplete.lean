module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Neighbourhoods
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionPowerThickenings
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.DegreeZeroSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsAtFactor

/-!
# Infinitesimal section completeness from the degree-zero comparison of Stacks 0EL1

Let `i : Z ⟶ X` be a closed immersion with ideal sheaf `𝓘` and let `F` be a quasi-coherent
`𝒪_X`-module. Two spellings of "the sections of `F` are determined by its restrictions to the
infinitesimal neighbourhoods of `Z`" are in use in this library:

* the degree-zero comparison `H⁰(X, F) ⟶ lim H⁰(Qₙ, Fₙ)` of
  `Stacks.Algebraization.IdealTower.comparison`, for the tower `Qₙ = V(𝓘ⁿ)`, which is the form in
  which [Stacks, Tag 0EL1] and [Stacks, Tag 0EL2] are stated here;
* `Stacks.Algebraization.IsInfinitesimalSectionsComplete` and its neighbourhood version
  `Stacks.Algebraization.IsNeighbourhoodSectionsComplete`, which are the forms in which the
  conditions of [Stacks, Tag 0EK2] are stated.

This file passes from the first to the second.

## Main results

* `Stacks.Algebraization.isInfinitesimalSectionsComplete_of_isIso_comparison` — invertibility of
  the degree-zero comparison gives infinitesimal section completeness.
* `Stacks.Algebraization.isNeighbourhoodSectionsComplete_of_isInfinitesimalSectionsComplete` —
  if moreover restriction `Γ(X, F) ⟶ Γ(V, F)` is bijective for every open `V ⊇ Z`, the colimit
  over those opens of `Γ(V, F)` is the inverse limit of the sections on the neighbourhoods.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0EL2](https://stacks.math.columbia.edu/tag/0EL2)
* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.Algebraization

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- A family over `ℕᵒᵖ` compatible with the successor maps is a section. -/
public theorem mem_sections_of_succ {D : ℕᵒᵖ ⥤ Type*} (σ : ∀ n : ℕ, D.obj (op n))
    (hσ : ∀ n : ℕ, D.map (homOfLE (Nat.le_succ n)).op (σ (n + 1)) = σ n) :
    (fun j : ℕᵒᵖ => σ j.unop) ∈ D.sections := by
  intro j j' f
  obtain ⟨m⟩ := j
  obtain ⟨n⟩ := j'
  have hnm : n ≤ m := leOfHom f.unop
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  show D.map f (σ (n + k)) = σ n
  induction k with
  | zero =>
    have : f = 𝟙 _ := Subsingleton.elim _ _
    subst this
    simp
  | succ k ih =>
    have hf : f = (homOfLE (Nat.le_succ (n + k))).op ≫ (homOfLE (Nat.le_add_right n k)).op :=
      Subsingleton.elim _ _
    rw [hf, D.map_comp, types_comp_apply]
    exact (congrArg _ (hσ (n + k))).trans (ih _ (Nat.le_add_right n k))

/-- **From the global sections to the neighbourhoods.** If the global sections of `F` are the
inverse limit of its sections on the infinitesimal neighbourhoods of `Z`, and restriction
`Γ(X, F) ⟶ Γ(V, F)` is bijective for every open `V` containing `Z`, then the colimit over those
opens of `Γ(V, F)` is that inverse limit too. -/
public theorem isNeighbourhoodSectionsComplete_of_isInfinitesimalSectionsComplete (F : X.Modules)
    (hinf : IsInfinitesimalSectionsComplete i F)
    (hres : ∀ V : X.Opens, Set.range i.base ⊆ V →
      Function.Bijective (F.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op)) :
    IsNeighbourhoodSectionsComplete i F := by
  have htop : Set.range i.base ⊆ ((⊤ : X.Opens) : Set X) := fun _ _ => trivial
  have hglob : ∀ (n : ℕ) (t : Γ(F, ⊤)), neighbourhoodSections i F htop n t =
      pullbackGlobalSections (nthInfinitesimalNeighbourhoodι i n) F t := fun _ _ => rfl
  have hcompat : ∀ (t : Γ(F, ⊤)) (n m : ℕ) (h : n ≤ m),
      pullbackSectionsMap F (nthInfinitesimalNeighbourhoodTransition i h)
        (pullbackGlobalSections (nthInfinitesimalNeighbourhoodι i m) F t) =
      pullbackGlobalSections (nthInfinitesimalNeighbourhoodι i n) F t := by
    intro t n m h
    exact pullbackSectionsAt_trans F (nthInfinitesimalNeighbourhoodTransition i h)
      (Opens.map_top _) (Opens.map_top _) t
  refine ⟨fun s hs => ?_, fun V W hV hW t u htu => ?_⟩
  · obtain ⟨t, ht, -⟩ := hinf s hs
    exact ⟨⊤, htop, t, fun n => (hglob n t).trans (ht n)⟩
  · obtain ⟨t', rfl⟩ := (hres V hV).2 t
    obtain ⟨u', rfl⟩ := (hres W hW).2 u
    have hres' : ∀ {V : X.Opens} (hV : Set.range i.base ⊆ V) (n : ℕ) (x : Γ(F, ⊤)),
        neighbourhoodSections i F hV n (F.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op x) =
          pullbackGlobalSections (nthInfinitesimalNeighbourhoodι i n) F x := fun hV n x =>
      pullbackSectionsAt_restrict _ F le_top (Opens.map_top _) _ x
    have heq : t' = u' := by
      obtain ⟨t₀, -, huniq⟩ := hinf
        (fun n => pullbackGlobalSections (nthInfinitesimalNeighbourhoodι i n) F t')
        (hcompat t')
      exact (huniq t' fun _ => rfl).trans (huniq u' fun n => ((hres' hW n u').symm.trans
        (htu n).symm).trans (hres' hV n t')).symm
    subst heq
    refine ⟨V ⊓ W, Set.subset_inter hV hW, inf_le_left, inf_le_right, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp]
    rfl

/-- **Infinitesimal section completeness from the degree-zero comparison of Stacks 0EL1.** For a
closed immersion `i` with ideal sheaf `𝓘` and a quasi-coherent `F`, if the comparison
`H⁰(X, F) ⟶ lim H⁰(Qₙ, Fₙ)` along the tower `Qₙ = V(𝓘ⁿ)` is invertible, then every compatible
family of sections of `F` on the infinitesimal neighbourhoods of `i` comes from a unique global
section. The ideal sheaf is passed as `K` with `K = i.ker`. -/
public theorem isInfinitesimalSectionsComplete_of_isIso_comparison (F : X.Modules)
    [F.IsQuasicoherent] (K : X.IdealSheafData) (hK : ∀ n, K ^ (n + 1) ≤ K ^ n) (hKi : K = i.ker)
    (hiso : IsIso (IdealTower.comparison (fun n => K ^ n) hK F 0)) :
    IsInfinitesimalSectionsComplete i F := by
  subst hKi
  set J : ℕ → X.IdealSheafData := fun n => i.ker ^ n
  have h1 : IsIso (IdealTower.ambientComparison J hK F 0) := by
    have heq : IdealTower.comparison J hK F 0 = IdealTower.ambientComparison J hK F 0 ≫
        limMap (IdealTower.cohomologyTowerIso J hK F 0).hom :=
      (limit.lift_map _ _).symm
    rw [heq] at hiso
    exact IsIso.of_isIso_comp_right _ (limMap (IdealTower.cohomologyTowerIso J hK F 0).hom)
  have h2 : IsLimit ((Hfunctor X.ringCatSheaf ⊤ 0).mapCone (IdealTower.cone J hK F)) :=
    @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit _) h1
  have h3 := (IsLimit.mapConeEquiv (HzeroIso X.ringCatSheaf ⊤)) h2
  have h4 := isLimitOfPreserves (forget AddCommGrpCat) h3
  have h5 := (Types.isLimit_iff _).1 ⟨h4⟩
  intro s hs
  let φ : ∀ k : ℕ, idealPowerQuotient i.ker k F ≅ (IdealTower.system J hK F).obj (op k) :=
    fun k => idealQuotientPushforwardIso i.ker k F (i.ker ^ k).subschemeι
      (Scheme.IdealSheafData.ker_subschemeι _)
  have hφ : ∀ k : ℕ, cokernel.π (C := X.Modules) (idealPowerMultiple i.ker k F).ι ≫ (φ k).hom =
      (IdealTower.cone J hK F).π.app (op k) := fun k =>
    idealQuotientPushforwardMap_π i.ker k F (i.ker ^ k).subschemeι
      (Scheme.IdealSheafData.ker_subschemeι _)
  have capp : ∀ {M N P : X.Modules} (α : M ⟶ N) (β : N ⟶ P) (x : Γ(M, ⊤)),
      (α ≫ β).app ⊤ x = β.app ⊤ (α.app ⊤ x) := fun α β x => by
    rw [Scheme.Modules.Hom.comp_app]; rfl
  have hcomp : ∀ {M N P : X.Modules} {α : M ⟶ N} {β : N ⟶ P} {γ : M ⟶ P}, α ≫ β = γ →
      ∀ x : Γ(M, ⊤), γ.app ⊤ x = β.app ⊤ (α.app ⊤ x) := fun h x => by rw [← h, capp]
  have hnat : ∀ k : ℕ, (IdealTower.cone J hK F).π.app (op (k + 1)) ≫
      (IdealTower.system J hK F).map (homOfLE (Nat.le_succ k)).op =
      (IdealTower.cone J hK F).π.app (op k) := fun k =>
    ((IdealTower.cone J hK F).π.naturality (homOfLE (Nat.le_succ k)).op).symm.trans
      (Category.id_comp _)
  let ψ : ∀ n : ℕ, Γ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i n)).obj F, ⊤) →
      Γ((IdealTower.system J hK F).obj (op (n + 1)), ⊤) := fun n y =>
    (φ (n + 1)).hom.app ⊤ ((infinitesimalSectionsEquiv i F n).symm y)
  have hF : ∀ n : ℕ, ((IdealTower.system J hK F).map (homOfLE (Nat.le_succ (n + 1))).op).app ⊤
      (ψ (n + 1) (s (n + 1))) = ψ n (s n) := by
    intro n
    set τ : idealPowerQuotient i.ker (n + 2) F ⟶ idealPowerQuotient i.ker (n + 1) F :=
      (φ (n + 2)).hom ≫ (IdealTower.system J hK F).map (homOfLE (Nat.le_succ (n + 1))).op ≫
        (φ (n + 1)).inv with hτdef
    have hτ : infinitesimalQuotientπ i F (n + 1) ≫ τ = infinitesimalQuotientπ i F n := by
      rw [hτdef, ← Category.assoc, ← Category.assoc]
      exact (Iso.comp_inv_eq _).mpr
        (((congrArg (· ≫ _) (hφ (n + 2))).trans (hnat (n + 1))).trans (hφ (n + 1)).symm)
    set y := (infinitesimalSectionsEquiv i F (n + 1)).symm (s (n + 1)) with hy
    have h1 := infinitesimalSectionsEquiv_transition i F (Nat.le_succ n) τ hτ y
    rw [hy, Equiv.apply_symm_apply, hs n (n + 1)] at h1
    have h2 : τ.app ⊤ y = (infinitesimalSectionsEquiv i F n).symm (s n) := by
      rw [h1, Equiv.symm_apply_apply]
    have h3 : τ ≫ (φ (n + 1)).hom = (φ (n + 2)).hom ≫
        (IdealTower.system J hK F).map (homOfLE (Nat.le_succ (n + 1))).op := by
      rw [hτdef, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    show ((IdealTower.system J hK F).map (homOfLE (Nat.le_succ (n + 1))).op).app ⊤
      ((φ (n + 2)).hom.app ⊤ y) = (φ (n + 1)).hom.app ⊤ _
    rw [← capp, ← h3, capp, h2]
  have hmap : ∀ {M N : X.Modules} (f : M ⟶ N) (x : ToType Γ(M, ⊤)),
      (forget AddCommGrpCat).map ((secF X.ringCatSheaf ⊤).map f) x = f.app ⊤ x :=
    fun _ _ => rfl
  let σ : ∀ k : ℕ, ToType Γ((IdealTower.system J hK F).obj (op k), ⊤) := fun k =>
    ((IdealTower.system J hK F).map (homOfLE (Nat.le_succ k)).op).app ⊤ (ψ k (s k))
  have hσ : (fun j : ℕᵒᵖ => σ j.unop) ∈
      ((IdealTower.system J hK F ⋙ secF X.ringCatSheaf ⊤) ⋙ forget AddCommGrpCat).sections := by
    refine mem_sections_of_succ (D := (IdealTower.system J hK F ⋙ secF X.ringCatSheaf ⊤) ⋙
      forget AddCommGrpCat) σ fun n => ?_
    refine (hmap _ _).trans ?_
    exact congrArg (((IdealTower.system J hK F).map (homOfLE (Nat.le_succ n)).op).app ⊤) (hF n)
  obtain ⟨t, ht, huniq⟩ := h5 _ hσ
  have hinj : ∀ k : ℕ, Function.Injective ((φ k).hom.app ⊤) := fun k a b hab => by
    have h := congrArg ((φ k).inv.app ⊤) hab
    rwa [← capp, ← capp, Iso.hom_inv_id] at h
  have hconeπ : ∀ (k : ℕ) (x : Γ(F, ⊤)), ((IdealTower.cone J hK F).π.app (op k)).app ⊤ x =
      ((IdealTower.system J hK F).map (homOfLE (Nat.le_succ k)).op).app ⊤
        (((IdealTower.cone J hK F).π.app (op (k + 1))).app ⊤ x) := fun k x =>
    hcomp (hnat k) x
  have hπφ : ∀ (k : ℕ) (x : Γ(F, ⊤)), ((IdealTower.cone J hK F).π.app (op (k + 1))).app ⊤ x =
      (φ (k + 1)).hom.app ⊤ ((infinitesimalQuotientπ i F k).app ⊤ x) := fun k x =>
    hcomp (hφ (k + 1)) x
  have hB : ∀ x : Γ(F, ⊤), (∀ n : ℕ,
      pullbackGlobalSections (nthInfinitesimalNeighbourhoodι i n) F x = s n) ↔
      ∀ n : ℕ, ((IdealTower.cone J hK F).π.app (op (n + 1))).app ⊤ x = ψ n (s n) := by
    intro x
    refine forall_congr' fun n => ?_
    rw [hπφ, ← infinitesimalSectionsEquiv_quotient_apply]
    exact ⟨fun h => congrArg ((φ (n + 1)).hom.app ⊤) ((Equiv.eq_symm_apply _).mpr h),
      fun h => (Equiv.eq_symm_apply _).mp (hinj (n + 1) h)⟩
  refine ⟨t, (hB t).mpr fun n => ?_, fun t' ht' => huniq t' fun j => ?_⟩
  · have e1 : ((IdealTower.cone J hK F).π.app (op (n + 1))).app ⊤ t = σ (n + 1) :=
      ht (op (n + 1))
    exact e1.trans (hF n)
  · obtain ⟨k⟩ := j
    show ((IdealTower.cone J hK F).π.app (op k)).app ⊤ t' = σ k
    rw [hconeπ, (hB t').mp ht' k]


end Stacks.Algebraization

end
