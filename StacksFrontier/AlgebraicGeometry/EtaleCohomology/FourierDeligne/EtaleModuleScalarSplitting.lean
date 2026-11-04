module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.EtaleModuleRestrictScalarsLift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LowerShriekRestrictScalarsIsogeny

/-!
# Isogenies after a finite free extension of the coefficients

Let `ρ : Λ →+* Λ''` be a homomorphism of commutative rings. A *scalar splitting* of a sheaf `A''`
of `Λ''`-modules over a sheaf `A` of `Λ`-modules on the small étale site of `X`
(`Stacks.EtaleCohomology.EtaleModuleScalarSplitting`) is a decomposition `res_ρ A'' ≅ A^e`, given
by projections `π_i : res_ρ A'' ⟶ A` and injections `ι_i : A ⟶ res_ρ A''`, along which
multiplication by `o ∈ Λ''` is the matrix `(c(o)_{ki})` of multiplications by elements of `Λ`. The
model is `A'' = A ⊗_Λ Λ''` for `Λ''` free over `Λ` with basis `β`, `c(o)_{ki}` the `k`-th
coordinate of `o β_i`.

## Main definitions

* `Stacks.EtaleCohomology.EtaleModuleScalarSplitting`: a scalar splitting of `A''` over `A`.

## Main results

* `Stacks.EtaleCohomology.EtaleModuleScalarSplitting.map`: scalar splittings are carried by every
  pair of functors commuting with `res_ρ` and with the scalars, such as `R^q f_!` and inverse
  images.
* `Stacks.EtaleCohomology.exists_isogeny_of_etaleModuleScalarSplitting`: an `n`-isogeny `A ⇄ B`
  of sheaves of `Λ`-modules gives an `n`-isogeny `A'' ⇄ B''` of sheaves of `Λ''`-modules for any
  two scalar splittings with the same matrices.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable {Λ Λ'' : Type} [CommRing Λ] [CommRing Λ''] (ρ : Λ →+* Λ'') {e : ℕ}
  (c : Λ'' → Fin e → Fin e → Λ)

/-- **A scalar splitting** of a sheaf `A''` of `Λ''`-modules over a sheaf `A` of `Λ`-modules:
`π_i : res_ρ A'' ⟶ A` and `ι_i : A ⟶ res_ρ A''` (`i < e`) with `ι_i ≫ π_j = δ_{ij}`,
`Σ_i π_i ≫ ι_i = 𝟙`, and `ι_i ≫ (o • -) = Σ_k c(o)_{ki} • ι_k` for `o ∈ Λ''`. -/
def EtaleModuleScalarSplitting {X : Scheme.{u}} (A'' : EtaleModules.{u, 0} Λ'' X)
    (A : EtaleModules.{u, 0} Λ X) (π : Fin e → ((etaleModuleRestrictScalars ρ X).obj A'' ⟶ A))
    (ι : Fin e → (A ⟶ (etaleModuleRestrictScalars ρ X).obj A'')) : Prop :=
  (∀ i j, ι i ≫ π j = if i = j then 𝟙 A else 0) ∧ ∑ i, π i ≫ ι i = 𝟙 _ ∧
    ∀ (o : Λ'') (i : Fin e), ι i ≫ (etaleModuleRestrictScalars ρ X).map
        ((etaleModuleSMul X o).app A'') = ∑ k, (etaleModuleSMul X (c o k i)).app A ≫ ι k

variable {ρ c}

/-- **Scalar splittings are carried by functors commuting with restriction of scalars and with
the scalars.** -/
theorem EtaleModuleScalarSplitting.map {X Y : Scheme.{u}} {A'' : EtaleModules.{u, 0} Λ'' X}
    {A : EtaleModules.{u, 0} Λ X} {π : Fin e → ((etaleModuleRestrictScalars ρ X).obj A'' ⟶ A)}
    {ι : Fin e → (A ⟶ (etaleModuleRestrictScalars ρ X).obj A'')}
    (h : EtaleModuleScalarSplitting ρ c A'' A π ι)
    (F'' : EtaleModules.{u, 0} Λ'' X ⥤ EtaleModules.{u, 0} Λ'' Y)
    (F : EtaleModules.{u, 0} Λ X ⥤ EtaleModules.{u, 0} Λ Y) [F.Additive]
    (eF : etaleModuleRestrictScalars ρ X ⋙ F ≅ F'' ⋙ etaleModuleRestrictScalars ρ Y)
    (hF : ∀ (a : Λ) (G : EtaleModules.{u, 0} Λ X),
      F.map ((etaleModuleSMul X a).app G) = (etaleModuleSMul Y a).app (F.obj G))
    (hF'' : ∀ (a : Λ'') (G : EtaleModules.{u, 0} Λ'' X),
      F''.map ((etaleModuleSMul X a).app G) = (etaleModuleSMul Y a).app (F''.obj G)) :
    EtaleModuleScalarSplitting ρ c (F''.obj A'') (F.obj A)
      (fun i => eF.inv.app A'' ≫ F.map (π i)) (fun i => F.map (ι i) ≫ eF.hom.app A'') := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨fun i j ↦ ?_, ?_, fun o i ↦ ?_⟩
  · rw [Category.assoc, Iso.hom_inv_id_app_assoc, ← F.map_comp, h₁]
    split_ifs
    · exact F.map_id _
    · exact F.map_zero _ _
  · simp only [Category.assoc]
    rw [← Preadditive.comp_sum, show (∑ j, F.map (π j) ≫ F.map (ι j) ≫ eF.hom.app A'') =
        F.map (∑ j, π j ≫ ι j) ≫ eF.hom.app A'' by
      rw [F.map_sum, Preadditive.sum_comp]
      simp only [F.map_comp, Category.assoc], h₂, F.map_id, Category.id_comp]
    exact eF.inv_hom_id_app A''
  · rw [Category.assoc, ← hF'']
    have hn : F.map ((etaleModuleRestrictScalars ρ X).map ((etaleModuleSMul X o).app A'')) ≫
        eF.hom.app A'' = eF.hom.app A'' ≫
          (etaleModuleRestrictScalars ρ Y).map (F''.map ((etaleModuleSMul X o).app A'')) :=
      eF.hom.naturality ((etaleModuleSMul X o).app A'')
    rw [← hn, ← Category.assoc, ← F.map_comp, h₃, F.map_sum, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [F.map_comp, hF, Category.assoc]

/-- **An isogeny of `Λ`-sheaves gives an isogeny of `Λ''`-sheaves along scalar splittings with
the same matrices**: for `f : A ⟶ B`, `g : B ⟶ A` with `f ≫ g = n • 𝟙` and `g ≫ f = n • 𝟙`,
there are `f'' : A'' ⟶ B''` and `g'' : B'' ⟶ A''` with `f'' ≫ g'' = n • 𝟙` and
`g'' ≫ f'' = n • 𝟙`. -/
theorem exists_isogeny_of_etaleModuleScalarSplitting {X : Scheme.{u}}
    {A'' B'' : EtaleModules.{u, 0} Λ'' X} {A B : EtaleModules.{u, 0} Λ X}
    {πA : Fin e → ((etaleModuleRestrictScalars ρ X).obj A'' ⟶ A)}
    {ιA : Fin e → (A ⟶ (etaleModuleRestrictScalars ρ X).obj A'')}
    {πB : Fin e → ((etaleModuleRestrictScalars ρ X).obj B'' ⟶ B)}
    {ιB : Fin e → (B ⟶ (etaleModuleRestrictScalars ρ X).obj B'')}
    (hA : EtaleModuleScalarSplitting ρ c A'' A πA ιA)
    (hB : EtaleModuleScalarSplitting ρ c B'' B πB ιB) (f : A ⟶ B) (g : B ⟶ A) {n : ℕ}
    (hfg : f ≫ g = n • 𝟙 A) (hgf : g ≫ f = n • 𝟙 B) :
    ∃ (f'' : A'' ⟶ B'') (g'' : B'' ⟶ A''), f'' ≫ g'' = n • 𝟙 A'' ∧ g'' ≫ f'' = n • 𝟙 B'' := by
  let res := etaleModuleRestrictScalars ρ X
  have hcomp : ∀ {P'' Q'' : EtaleModules.{u, 0} Λ'' X} {P Q : EtaleModules.{u, 0} Λ X}
      {πP : Fin e → (res.obj P'' ⟶ P)} {ιP : Fin e → (P ⟶ res.obj P'')}
      {πQ : Fin e → (res.obj Q'' ⟶ Q)} {ιQ : Fin e → (Q ⟶ res.obj Q'')},
      EtaleModuleScalarSplitting ρ c P'' P πP ιP → EtaleModuleScalarSplitting ρ c Q'' Q πQ ιQ →
      ∀ (a : P ⟶ Q) (b : Q ⟶ P), a ≫ b = n • 𝟙 P →
        (∑ i, πP i ≫ a ≫ ιQ i) ≫ (∑ i, πQ i ≫ b ≫ ιP i) = n • 𝟙 _ := by
    intro P'' Q'' P Q πP ιP πQ ιQ hP hQ a b hab
    rw [Preadditive.sum_comp]
    have : ∀ i, (πP i ≫ a ≫ ιQ i) ≫ (∑ j, πQ j ≫ b ≫ ιP j) = n • (πP i ≫ ιP i) := fun i ↦ by
      rw [Preadditive.comp_sum]
      simp only [← Category.assoc (ιQ i), hQ.1 i, ite_comp, comp_ite, zero_comp, comp_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true, Category.id_comp, Category.assoc]
      rw [← Category.assoc a, hab, Preadditive.nsmul_comp, Category.id_comp,
        Preadditive.comp_nsmul]
    simp only [this]
    rw [← Finset.smul_sum, hP.2.1]
  have hlin : ∀ {P'' Q'' : EtaleModules.{u, 0} Λ'' X} {P Q : EtaleModules.{u, 0} Λ X}
      {πP : Fin e → (res.obj P'' ⟶ P)} {ιP : Fin e → (P ⟶ res.obj P'')}
      {πQ : Fin e → (res.obj Q'' ⟶ Q)} {ιQ : Fin e → (Q ⟶ res.obj Q'')},
      EtaleModuleScalarSplitting ρ c P'' P πP ιP → EtaleModuleScalarSplitting ρ c Q'' Q πQ ιQ →
      ∀ (a : P ⟶ Q) (o : Λ''),
        res.map ((etaleModuleSMul X o).app P'') ≫ (∑ i, πP i ≫ a ≫ ιQ i) =
          (∑ i, πP i ≫ a ≫ ιQ i) ≫ res.map ((etaleModuleSMul X o).app Q'') := by
    intro P'' Q'' P Q πP ιP πQ ιQ hP hQ a o
    have hπ : ∀ k, res.map ((etaleModuleSMul X o).app P'') ≫ πP k =
        ∑ i, πP i ≫ (etaleModuleSMul X (c o k i)).app P := fun k ↦ by
      have e₁ : res.map ((etaleModuleSMul X o).app P'') ≫ πP k =
          (∑ i, πP i ≫ ιP i) ≫ res.map ((etaleModuleSMul X o).app P'') ≫ πP k := by
        rw [hP.2.1, Category.id_comp]
      rw [e₁, Preadditive.sum_comp]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Category.assoc, ← Category.assoc (ιP i), hP.2.2 o i, Preadditive.sum_comp]
      simp only [Category.assoc, hP.1 _ k, comp_ite, comp_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      exact congrArg (πP i ≫ ·) (Category.comp_id _)
    rw [Preadditive.comp_sum, Preadditive.sum_comp]
    simp_rw [← Category.assoc, hπ, Preadditive.sum_comp]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Category.assoc, Category.assoc, hQ.2.2 o i, Preadditive.comp_sum, Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hn : a ≫ (etaleModuleSMul X (c o k i)).app Q =
        (etaleModuleSMul X (c o k i)).app P ≫ a := (etaleModuleSMul X (c o k i)).naturality a
    rw [Category.assoc, ← Category.assoc a, hn]
    simp only [Category.assoc]
  have hsec : ∀ {P'' Q'' : EtaleModules.{u, 0} Λ'' X} (φ : res.obj P'' ⟶ res.obj Q''),
      (∀ o : Λ'', res.map ((etaleModuleSMul X o).app P'') ≫ φ =
        φ ≫ res.map ((etaleModuleSMul X o).app Q'')) →
      ∃ ψ : P'' ⟶ Q'', res.map ψ = φ := by
    intro P'' Q'' φ hφ
    exact exists_etaleModuleRestrictScalars_map_eq ρ φ fun U l x ↦
      congrArg (fun t ↦ (t.hom.app U).hom x) (hφ l)
  obtain ⟨f'', hf''⟩ := hsec _ (hlin hA hB f)
  obtain ⟨g'', hg''⟩ := hsec _ (hlin hB hA g)
  have hfaith : ∀ {P'' : EtaleModules.{u, 0} Λ'' X} (t : P'' ⟶ P''),
      res.map t = n • 𝟙 _ → t = n • 𝟙 P'' := by
    intro P'' t ht
    apply Sheaf.hom_ext
    ext U x
    exact (congrArg (fun s ↦ (s.hom.app U).hom x) ht).trans
      (by rw [← res.map_id, ← Functor.map_nsmul])
  refine ⟨f'', g'', hfaith _ ?_, hfaith _ ?_⟩
  · rw [res.map_comp, hf'', hg'']
    exact hcomp hA hB f g hfg
  · rw [res.map_comp, hf'', hg'']
    exact hcomp hB hA g f hgf

end Stacks.EtaleCohomology

end
