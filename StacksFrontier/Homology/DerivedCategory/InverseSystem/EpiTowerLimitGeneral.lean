module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.EpiTowerLimit

/-!
# Milnor triangles of epimorphic towers, for an arbitrary model of the derived category

`StacksFrontier/Homology/DerivedCategory/InverseSystem/EpiTowerLimit.lean` proves that the ordinary
limit of a tower of complexes of modules with epimorphic transitions represents its derived
inverse limit, in the standard model `HasDerivedCategory.standard` of the derived category.  This
file proves the same statement for an **arbitrary** `HasDerivedCategory` instance on modules,
with the projections of the Milnor triangle pinned to the localizations of the legs of the limit
cone, and a transport lemma moving such a triangle across isomorphisms of cone data.

## Main results

* `DerivedCategory.exists_distTriang_of_limitCone_of_epi` — for a tower of complexes of modules
  with epimorphic transitions and a limit cone `s`, the triangle
  `Q(s.pt) ⟶ ∏ Q(Fₙ) ⟶ ∏ Q(Fₙ) ⟶ Q(s.pt)[1]` with first map the localized legs of `s` and second
  map the difference map of the localized transitions is distinguished.
* `CategoryTheory.Pretriangulated.exists_distTriang_milnor_of_iso` — such a triangle is transported
  across isomorphisms of the vertex and of the terms compatible with the legs and the transitions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w

namespace CategoryTheory.Pretriangulated

variable {D : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **A Milnor triangle is transported across isomorphisms of cone data**: if the vertex `K ≅ K'`
and the terms `Xₙ ≅ X'ₙ` are identified compatibly with the legs `πₙ`, `π'ₙ` and the transitions
`tₙ`, `t'ₙ`, and `K' ⟶ ∏ X' ⟶ ∏ X'` is the first two maps of a distinguished triangle, then so
is `K ⟶ ∏ X ⟶ ∏ X`. -/
theorem exists_distTriang_milnor_of_iso {X X' : ℕ → D} [HasProduct X] [HasProduct X']
    (t : ∀ n, X (n + 1) ⟶ X n) (t' : ∀ n, X' (n + 1) ⟶ X' n) {K K' : D}
    (π : ∀ n, K ⟶ X n) (π' : ∀ n, K' ⟶ X' n) (φ : K ≅ K') (ψ : ∀ n, X n ≅ X' n)
    (hπ : ∀ n, π n ≫ (ψ n).hom = φ.hom ≫ π' n)
    (ht : ∀ n, t n ≫ (ψ n).hom = (ψ (n + 1)).hom ≫ t' n)
    (h : ∃ δ', Triangle.mk (Pi.lift π') (Pi.lift fun n => Pi.π X' n - Pi.π X' (n + 1) ≫ t' n)
      δ' ∈ distTriang D) :
    ∃ δ, Triangle.mk (Pi.lift π) (Pi.lift fun n => Pi.π X n - Pi.π X (n + 1) ≫ t n) δ ∈
      distTriang D := by
  obtain ⟨δ', hδ'⟩ := h
  let Ψ : (∏ᶜ X) ≅ ∏ᶜ X' :=
    { hom := Pi.lift fun n => Pi.π X n ≫ (ψ n).hom
      inv := Pi.lift fun n => Pi.π X' n ≫ (ψ n).inv
      hom_inv_id := Pi.hom_ext _ _ fun n => by simp
      inv_hom_id := Pi.hom_ext _ _ fun n => by simp }
  refine ⟨Ψ.hom ≫ δ' ≫ (shiftFunctor D (1 : ℤ)).map φ.inv, isomorphic_distinguished _ hδ' _ ?_⟩
  refine Triangle.isoMk _ _ φ Ψ Ψ ?_ ?_ ?_
  · refine Pi.hom_ext _ _ fun n => ?_
    simp [Ψ, hπ]
  · refine Pi.hom_ext _ _ fun n => ?_
    simp only [Triangle.mk_obj₂, Triangle.mk_obj₃, Triangle.mk_mor₂, Category.assoc, Ψ,
      Pi.lift_comp_π, Preadditive.comp_sub, Preadditive.sub_comp, Pi.lift_comp_π_assoc, ht]
  · simp only [Triangle.mk_obj₃, Triangle.mk_obj₁, Triangle.mk_mor₃, Category.assoc,
      ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, Category.comp_id]

end CategoryTheory.Pretriangulated

namespace DerivedCategory

/-- The difference map of an epimorphic tower of modules is an epimorphism. -/
private theorem epi_pi_sub_shift_of_epi' {A : Type u} [Ring A] (X : ℕ → ModuleCat.{v} A)
    (t : ∀ n, X (n + 1) ⟶ X n) [∀ n, Epi (t n)] :
    Epi (Pi.lift fun n ↦ Pi.π X n - Pi.π X (n + 1) ≫ t n) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro y
  obtain ⟨x, hx⟩ := Stacks.InverseSystem.surjective_pi_sub_shift (fun n ↦ t n)
    (fun n ↦ (ModuleCat.epi_iff_surjective (t n)).mp inferInstance)
    ((ModuleCat.piIsoPi X).hom y)
  refine ⟨(ModuleCat.piIsoPi X).inv x, ?_⟩
  apply (ModuleCat.piIsoPi X).toLinearEquiv.injective
  funext n
  simp only
  show ((Pi.lift (fun n ↦ Pi.π X n - Pi.π X (n + 1) ≫ t n) ≫ Pi.π X n)
    ((ModuleCat.piIsoPi X).inv x)) = _
  rw [Pi.lift_comp_π]
  show (Pi.π X n) ((ModuleCat.piIsoPi X).inv x) -
    (t n) ((Pi.π X (n + 1)) ((ModuleCat.piIsoPi X).inv x)) =
      (ModuleCat.piIsoPi X).hom y n
  rw [ModuleCat.piIsoPi_inv_kernel_ι_apply, ModuleCat.piIsoPi_inv_kernel_ι_apply]
  exact congrFun hx n

/-- An additive functor carries the difference map of a tower to the difference map of the image
tower, up to the product comparison isomorphisms. -/
private theorem map_pi_sub_shift_comp_piComparison {C E : Type*} [Category* C] [Category* E]
    [Preadditive C] [Preadditive E] (G : C ⥤ E) [G.Additive] (X : ℕ → C) (t : ∀ n, X (n + 1) ⟶ X n)
    [HasProduct X] [HasProduct fun n ↦ G.obj (X n)] :
    G.map (Pi.lift fun n ↦ Pi.π X n - Pi.π X (n + 1) ≫ t n) ≫ piComparison G X =
      piComparison G X ≫ Pi.lift fun n ↦ Pi.π (fun n ↦ G.obj (X n)) n -
        Pi.π (fun n ↦ G.obj (X n)) (n + 1) ≫ G.map (t n) := by
  refine Pi.hom_ext _ _ fun n ↦ ?_
  rw [Category.assoc, piComparison_comp_π, ← G.map_comp]
  simp only [Pi.lift_comp_π, G.map_sub, G.map_comp, Category.assoc,
    Preadditive.comp_sub, piComparison_comp_π_assoc, piComparison_comp_π]

/-- The difference map of an epimorphic tower of complexes of modules is an epimorphism,
degreewise. -/
private theorem epi_complex_pi_sub_shift_of_epi' {A : Type u} [Ring A]
    (X : ℕ → CochainComplex (ModuleCat.{v} A) ℤ) (t : ∀ n, X (n + 1) ⟶ X n) [∀ n, Epi (t n)] :
    Epi (Pi.lift fun n ↦ Pi.π X n - Pi.π X (n + 1) ≫ t n) := by
  apply HomologicalComplex.epi_of_epi_f
  intro i
  let G := HomologicalComplex.eval (ModuleCat.{v} A) (ComplexShape.up ℤ) i
  have : ∀ n, Epi (G.map (t n)) := fun n => inferInstanceAs (Epi ((t n).f i))
  have : Epi (Pi.lift fun n ↦ Pi.π (fun n ↦ G.obj (X n)) n -
      Pi.π (fun n ↦ G.obj (X n)) (n + 1) ≫ G.map (t n)) :=
    epi_pi_sub_shift_of_epi' (fun n ↦ G.obj (X n)) (fun n ↦ G.map (t n))
  have : Epi (G.map (Pi.lift fun n ↦ Pi.π X n - Pi.π X (n + 1) ≫ t n) ≫ piComparison G X) := by
    rw [map_pi_sub_shift_comp_piComparison]; infer_instance
  exact (epi_comp_iff_of_isIso _ (piComparison G X)).mp this

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]

/-- **The ordinary limit of an epimorphic tower of complexes of modules has a Milnor triangle with
the localized legs as projections**, in any model of the derived category: for
`F : ℕᵒᵖ ⥤ CochainComplex (ModuleCat R) ℤ` with epimorphic transitions and a limit cone `s`, the
triangle `Q(s.pt) ⟶ ∏ₙ Q(Fₙ) ⟶ ∏ₙ Q(Fₙ) ⟶ Q(s.pt)[1]`, whose first map has components the
localized legs `Q(s.π n)` and whose second map is `(xₙ) ↦ (xₙ - Q(fₙ₊₁)(xₙ₊₁))`, is
distinguished for some third map.  At index `n` the transition is the map from `n + 1` to `n`. -/
theorem exists_distTriang_of_limitCone_of_epi
    (F : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} R) ℤ)
    [∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)]
    (s : Cone F) (hs : IsLimit s) [HasProduct fun n : ℕ ↦ DerivedCategory.Q.obj (F.obj ⟨n⟩)] :
    ∃ δ, Triangle.mk (Pi.lift fun n : ℕ ↦ DerivedCategory.Q.map (s.π.app ⟨n⟩))
      (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (F.obj ⟨n⟩)) n -
        Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (F.obj ⟨n⟩)) (n + 1) ≫
          DerivedCategory.Q.map (F.map (homOfLE (Nat.le_succ n)).op)) δ ∈
        distTriang (DerivedCategory (ModuleCat.{v} R)) := by
  have : PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.Q (C := ModuleCat.{v} R)) :=
    Stacks.DerivedProducts.preservesLimitsOfShape_Q
  let X := fun n : ℕ ↦ F.obj ⟨n⟩
  let d := Pi.lift fun n : ℕ ↦ Pi.π X n - Pi.π X (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
  let p : s.pt ⟶ ∏ᶜ X := Pi.lift fun n : ℕ ↦ s.π.app ⟨n⟩
  have hpd : p ≫ d = 0 := by
    apply Pi.hom_ext
    intro n
    simp [p, d, Preadditive.comp_sub, s.w]
  have hk : IsLimit (KernelFork.ofι p hpd) := by
    let coneOfKernel (t : KernelFork d) : Cone F :=
      { pt := t.pt
        π := NatTrans.ofOpSequence (fun n ↦ t.ι ≫ Pi.π _ n) (fun n ↦ by
          have h := congrArg (fun f ↦ f ≫ Pi.π X n) t.condition
          simp only [d, Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub, zero_comp] at h
          show 𝟙 t.pt ≫ (t.ι ≫ Pi.π _ n) =
            (t.ι ≫ Pi.π _ (n + 1)) ≫ F.map (homOfLE (Nat.le_succ n)).op
          exact (Category.id_comp _).trans
            ((sub_eq_zero.mp h).trans (Category.assoc _ _ _).symm)) }
    refine Fork.IsLimit.mk _ (fun t ↦ hs.lift (coneOfKernel t)) ?_ ?_
    · intro t
      apply Pi.hom_ext
      intro n
      simp [p, hs.fac, coneOfKernel]
    · intro t m hm
      apply hs.hom_ext
      intro n
      have h := congrArg (fun f ↦ f ≫ Pi.π X n.unop) hm
      simpa [p, coneOfKernel] using h
  have : Epi d := epi_complex_pi_sub_shift_of_epi' X _
  let S := ShortComplex.mk p d hpd
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel S hk
      mono_f := mono_of_isLimit_fork hk
      epi_g := inferInstance }
  let Q : CochainComplex (ModuleCat.{v} R) ℤ ⥤ DerivedCategory (ModuleCat.{v} R) :=
    DerivedCategory.Q
  let e := asIso (piComparison Q X)
  let d' := Pi.lift fun n : ℕ ↦ Pi.π (fun n ↦ Q.obj (X n)) n -
    Pi.π (fun n ↦ Q.obj (X n)) (n + 1) ≫ Q.map (F.map (homOfLE (Nat.le_succ n)).op)
  have hd : Q.map d ≫ e.hom = e.hom ≫ d' := map_pi_sub_shift_comp_piComparison Q X _
  have hp : Q.map p ≫ e.hom = Pi.lift fun n : ℕ ↦ Q.map (s.π.app ⟨n⟩) := by
    apply Pi.hom_ext
    intro n
    show (Q.map p ≫ piComparison Q X) ≫ Pi.π _ n = _
    rw [Category.assoc, piComparison_comp_π, ← Q.map_comp, Pi.lift_comp_π, Pi.lift_comp_π]
  refine ⟨e.inv ≫ DerivedCategory.triangleOfSESδ hS,
    isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS) _ ?_⟩
  refine Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm ?_ ?_ ?_
  · show Pi.lift (fun n : ℕ ↦ Q.map (s.π.app ⟨n⟩)) ≫ e.inv = 𝟙 _ ≫ Q.map p
    rw [← hp, Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · show d' ≫ e.inv = e.inv ≫ Q.map d
    rw [Iso.comp_inv_eq, Category.assoc, hd, Iso.inv_hom_id_assoc]
  · show (e.inv ≫ DerivedCategory.triangleOfSESδ hS) ≫
        (shiftFunctor (DerivedCategory (ModuleCat.{v} R)) (1 : ℤ)).map (𝟙 _) =
      e.inv ≫ DerivedCategory.triangleOfSESδ hS
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

end DerivedCategory

end
