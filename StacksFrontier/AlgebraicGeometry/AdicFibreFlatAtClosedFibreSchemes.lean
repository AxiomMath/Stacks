module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Algebraization
public import StacksFrontier.RingTheory.Etale.AdicFibreFlatAtClosedFibreStages

/-!
# A morphism whose adic base changes are étale is étale along the closed fibre

Let `A` be a ring, `I ⊆ A` an ideal, `p : Y ⟶ Spec A` with `Y` locally Noetherian, and
`g : X ⟶ Y` locally of finite type. If for every `n` the base change of `g` to the adic
thickening `Spec (A / I^{n+1})` is étale, then `g` is étale on an open neighbourhood of every
point of `X` lying over `V(I)`.

On affine opens `Spec C ⊆ X`, `Spec D ⊆ Y` this is
`Algebra.exists_notMem_etale_localization_away_of_forall_etale_quotient_pow`: the base change of
`Spec C ⟶ Spec D` to `Spec (A / I^{n+1})` is `Spec` of `D / I^{n+1} D → C / I^{n+1} C`.

## Main results

* `AlgebraicGeometry.exists_isOpenImmersion_etale_of_forall_etale_pullbackMap`: the statement
  above, with the neighbourhood given as an open immersion.
* `AlgebraicGeometry.exists_isOpenImmersion_flat_of_forall_flat_pullbackMap`: the flat analogue:
  if every adic base change is flat, `g` is flat near every point over `V(I)`.

## References

* [Stacks Project, Tag 0523](https://stacks.math.columbia.edu/tag/0523)
* [Stacks Project, Tag 00MK](https://stacks.math.columbia.edu/tag/00MK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The base change of `Spec C ⟶ Spec D` to `Spec T`, for a ring `T` over `A` and `D → C` over
`A`, is `Spec` of `D ⊗_A T → C ⊗_A T`, through the isomorphisms `pullbackSpecIso`. -/
theorem pullbackSpecIso_inv_comp_pullbackMap (D C T : Type u) [CommRing D] [CommRing C]
    [CommRing T] [Algebra A D] [Algebra D C] [Algebra A C] [IsScalarTower A D C] [Algebra A T] :
    (pullbackSpecIso A C T).inv ≫
        pullback.map (Spec.map (CommRingCat.ofHom (algebraMap A C)))
          (Spec.map (CommRingCat.ofHom (algebraMap A T)))
          (Spec.map (CommRingCat.ofHom (algebraMap A D)))
          (Spec.map (CommRingCat.ofHom (algebraMap A T)))
          (Spec.map (CommRingCat.ofHom (algebraMap D C))) (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            ← IsScalarTower.algebraMap_eq])
          (by simp) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A D C)
          (AlgHom.id A T)).toRingHom) ≫ (pullbackSpecIso A D T).inv := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullbackSpecIso_inv_fst_assoc, Category.assoc,
      pullbackSpecIso_inv_fst, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
  · rw [Category.assoc, pullback.lift_snd, pullbackSpecIso_inv_snd_assoc, Category.assoc,
      pullbackSpecIso_inv_snd, Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun t => ?_
    change (1 : C) ⊗ₜ[A] t = Algebra.TensorProduct.map (IsScalarTower.toAlgHom A D C)
      (AlgHom.id A T) ((1 : D) ⊗ₜ[A] t)
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

/-- **The affine model.** Let `A → D → C` be ring maps with `D` Noetherian and `D → C` of finite
type. If the base change of `Spec C ⟶ Spec D` to every `Spec (A / I^{n+1})` is étale, then for
every prime `q ⊇ IC` of `C` some `s ∉ q` has `D → C_s` étale. -/
theorem exists_notMem_etale_away_of_forall_etale_pullbackMap_spec (D C : Type u) [CommRing D]
    [CommRing C] [Algebra A D] [Algebra D C] [Algebra A C] [IsScalarTower A D C]
    [IsNoetherianRing D] [Algebra.FiniteType D C]
    (h : ∀ n : ℕ, Etale (pullback.map (Spec.map (CommRingCat.ofHom (algebraMap A C)))
      (adicThickeningι A I n) (Spec.map (CommRingCat.ofHom (algebraMap A D)))
      (adicThickeningι A I n) (Spec.map (CommRingCat.ofHom (algebraMap D C))) (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq])
      (by simp)))
    (q : Ideal C) [q.IsPrime] (hq : I.map (algebraMap A C) ≤ q) :
    ∃ s ∉ q, Algebra.Etale D (Localization.Away s) := by
  set J : Ideal D := I.map (algebraMap A D)
  have hJ : J.map (algebraMap D C) ≤ q := by
    rwa [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  refine Algebra.exists_notMem_etale_localization_away_of_forall_etale_quotient_pow J q hJ
    fun n => ?_
  set K : Ideal A := I ^ (n + 1)
  let T := A ⧸ K
  -- the base change, read on rings
  have hspec : RingHom.Etale (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A D C)
      (AlgHom.id A T)).toRingHom := by
    have h' : Etale ((pullbackSpecIso A C T).inv ≫
        pullback.map (Spec.map (CommRingCat.ofHom (algebraMap A C)))
          (Spec.map (CommRingCat.ofHom (algebraMap A T)))
          (Spec.map (CommRingCat.ofHom (algebraMap A D)))
          (Spec.map (CommRingCat.ofHom (algebraMap A T)))
          (Spec.map (CommRingCat.ofHom (algebraMap D C))) (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            ← IsScalarTower.algebraMap_eq])
          (by simp)) := by
      have hn : Etale (pullback.map (Spec.map (CommRingCat.ofHom (algebraMap A C)))
          (Spec.map (CommRingCat.ofHom (algebraMap A T)))
          (Spec.map (CommRingCat.ofHom (algebraMap A D)))
          (Spec.map (CommRingCat.ofHom (algebraMap A T)))
          (Spec.map (CommRingCat.ofHom (algebraMap D C))) (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            ← IsScalarTower.algebraMap_eq])
          (by simp)) := h n
      infer_instance
    rw [pullbackSpecIso_inv_comp_pullbackMap] at h'
    have h'' : Etale ((Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom A D C) (AlgHom.id A T)).toRingHom) ≫
          (pullbackSpecIso A D T).inv) ≫ (pullbackSpecIso A D T).hom) := inferInstance
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h''
    exact HasRingHomProperty.Spec_iff.mp h''
  -- the base change, read on quotients
  set L : Ideal D := K.map (algebraMap A D)
  have hLC : L.map (algebraMap D C) = K.map (algebraMap A C) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  let eD := Algebra.TensorProduct.quotIdealMapEquivTensorQuot D K
  let eC := Algebra.TensorProduct.quotIdealMapEquivTensorQuot C K
  have heq : algebraMap (D ⧸ L) (C ⧸ L.map (algebraMap D C)) =
      (eC.symm.toRingEquiv.trans (Ideal.quotEquivOfEq hLC).symm).toRingHom.comp
        ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom A D C)
          (AlgHom.id A T)).toRingHom.comp eD.toRingEquiv.toRingHom) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun d => ?_)
    simp only [RingHom.comp_apply, Ideal.Quotient.algebraMap_quotient_map_quotient]
    rw [show eD.toRingHom (Ideal.Quotient.mk L d) = d ⊗ₜ[A] (1 : T) from
      Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk D K d]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      IsScalarTower.coe_toAlgHom', AlgHom.coe_id, id_eq]
    have hC : eC.symm ((algebraMap D C d) ⊗ₜ[A] (1 : T)) =
        Ideal.Quotient.mk _ (algebraMap D C d) := by
      rw [AlgEquiv.symm_apply_eq]
      exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk C K _).symm
    change _ = (Ideal.quotEquivOfEq hLC).symm (eC.symm ((algebraMap D C d) ⊗ₜ[A] (1 : T)))
    rw [hC, Ideal.quotEquivOfEq_symm, Ideal.quotEquivOfEq_mk]
  have hL : Algebra.Etale (D ⧸ L) (C ⧸ L.map (algebraMap D C)) := by
    rw [← RingHom.etale_algebraMap, heq]
    exact RingHom.Etale.respectsIso.1 _ _ (RingHom.Etale.respectsIso.2 _ _ hspec)
  have hLJ : L = J ^ (n + 1) := Ideal.map_pow _ _ _
  rw [hLJ] at hL
  exact hL

/-- Étaleness of the base change of `g : X ⟶ Y` along `ι` is unchanged on replacing `X` and `Y`
by isomorphic schemes. -/
theorem etale_pullbackMap_of_iso {X Y X' Y' S T : Scheme.{u}} (ι : T ⟶ S) (g : X ⟶ Y)
    (p : Y ⟶ S) (g' : X' ⟶ Y') (p' : Y' ⟶ S) (f' : X' ⟶ S) (eX : X ≅ X') (eY : Y ≅ Y')
    (hg : eX.hom ≫ g' = g ≫ eY.hom) (hp : eY.hom ≫ p' = p) (hf' : g' ≫ p' = f')
    (h : Etale (pullback.map (g ≫ p) ι p ι g (𝟙 _) (𝟙 _) (by simp) (by simp))) :
    Etale (pullback.map f' ι p' ι g' (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hf']) (by simp)) := by
  subst hp hf'
  have hg' : eX.inv ≫ g ≫ eY.hom = g' := by rw [← hg, Iso.inv_hom_id_assoc]
  have e : pullback.map (g' ≫ p') ι (g ≫ eY.hom ≫ p') ι eX.inv (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, ← hg', Category.assoc, Category.assoc]) (by simp) ≫
      pullback.map (g ≫ eY.hom ≫ p') ι (eY.hom ≫ p') ι g (𝟙 _) (𝟙 _) (by simp) (by simp) ≫
      pullback.map (eY.hom ≫ p') ι p' ι eY.hom (𝟙 _) (𝟙 _) (by simp) (by simp) =
      pullback.map (g' ≫ p') ι p' ι g' (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext <;>
      simp only [pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, Category.comp_id, hg']
  have : Etale (pullback.map (g' ≫ p') ι (g ≫ eY.hom ≫ p') ι eX.inv (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, ← hg', Category.assoc, Category.assoc]) (by simp) ≫
      pullback.map (g ≫ eY.hom ≫ p') ι (eY.hom ≫ p') ι g (𝟙 _) (𝟙 _) (by simp) (by simp) ≫
      pullback.map (eY.hom ≫ p') ι p' ι eY.hom (𝟙 _) (𝟙 _) (by simp) (by simp)) :=
    inferInstance
  rwa [e] at this

/-- **The affine case.** Let `X`, `Y` be affine with `Y` Noetherian, `g : X ⟶ Y` locally of
finite type and `p : Y ⟶ Spec A`. If the base change of `g` to every `Spec (A / I^{n+1})` is
étale, then `g` is étale on an open neighbourhood of every point of `X` over `V(I)`. -/
theorem exists_isOpenImmersion_etale_of_forall_etale_pullbackMap_of_isAffine {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] [IsLocallyNoetherian Y] (g : X ⟶ Y) [LocallyOfFiniteType g]
    (p : Y ⟶ Spec (.of A))
    (h : ∀ n : ℕ, Etale (pullback.map (g ≫ p) (adicThickeningι A I n) p (adicThickeningι A I n)
      g (𝟙 _) (𝟙 _) (by simp) (by simp)))
    (x : X) (hx : ∃ n, (g ≫ p) x ∈ Set.range (adicThickeningι A I n)) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ X), IsOpenImmersion j ∧ x ∈ Set.range j ∧ Etale (j ≫ g) := by
  let C := Γ(X, ⊤)
  let D := Γ(Y, ⊤)
  let : Algebra D C := g.appTop.hom.toAlgebra
  let : Algebra A D := ((Scheme.ΓSpecIso (.of A)).inv ≫ p.appTop).hom.toAlgebra
  let : Algebra A C := ((Scheme.ΓSpecIso (.of A)).inv ≫ p.appTop ≫ g.appTop).hom.toAlgebra
  have : IsScalarTower A D C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsNoetherianRing D := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  have : Algebra.FiniteType D C := HasRingHomProperty.iff_of_isAffine.mp ‹LocallyOfFiniteType g›
  have hg : X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap D C)) = g ≫ Y.isoSpec.hom :=
    Scheme.isoSpec_hom_naturality g
  have hp : Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A D)) = p := by
    change Y.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of A)).inv ≫ p.appTop) = p
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
  have hf : Spec.map (CommRingCat.ofHom (algebraMap D C)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A D)) =
        Spec.map (CommRingCat.ofHom (algebraMap A C)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have h' := fun n => etale_pullbackMap_of_iso (adicThickeningι A I n) g p _ _ _ X.isoSpec
    Y.isoSpec hg hp hf (h n)
  let q : Ideal C := (X.isoSpec.hom x).asIdeal
  have : q.IsPrime := (X.isoSpec.hom x).isPrime
  have hgp : g ≫ p = X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)) := by
    rw [← hp, ← reassoc_of% hg, hf]
  have hq : I.map (algebraMap A C) ≤ q := by
    obtain ⟨n, y, hy⟩ := hx
    have hK : I ^ (n + 1) ≤ ((g ≫ p) x).asIdeal := by
      rw [← hy]
      intro a ha
      change Ideal.Quotient.mk (I ^ (n + 1)) a ∈ y.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact zero_mem _
    rw [hgp] at hK
    change I ^ (n + 1) ≤ q.comap (algebraMap A C) at hK
    exact Ideal.map_le_iff_le_comap.mpr ((Ideal.comap_isPrime _ q).le_of_pow_le hK)
  obtain ⟨s, hs, hsE⟩ := exists_notMem_etale_away_of_forall_etale_pullbackMap_spec I D C h' q hq
  refine ⟨Spec (.of (Localization.Away s)),
    Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away s))) ≫ X.isoSpec.inv,
    inferInstance, ?_, ?_⟩
  · have hmem : (⟨q, inferInstance⟩ : PrimeSpectrum C) ∈
        Set.range (PrimeSpectrum.comap (algebraMap C (Localization.Away s))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away s) s]
      exact hs
    obtain ⟨z, hz⟩ := hmem
    refine ⟨z, ?_⟩
    change X.isoSpec.inv (PrimeSpectrum.comap (algebraMap C (Localization.Away s)) z) = x
    rw [hz]
    change (X.isoSpec.hom ≫ X.isoSpec.inv) x = x
    rw [Iso.hom_inv_id]
    rfl
  · have e : (Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away s))) ≫
        X.isoSpec.inv) ≫ g =
          Spec.map (CommRingCat.ofHom (algebraMap D (Localization.Away s))) ≫ Y.isoSpec.inv := by
      rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Category.assoc, ← Spec.map_comp,
        IsScalarTower.algebraMap_eq D C (Localization.Away s), CommRingCat.ofHom_comp]
      rfl
    rw [e]
    have : Etale (Spec.map (CommRingCat.ofHom (algebraMap D (Localization.Away s)))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hsE)
    infer_instance

/-- Étaleness of the base change of `g` along `ι` restricts to open subschemes `U ⊆ g⁻¹ V`. -/
theorem etale_pullbackMap_resLE {X Y S T : Scheme.{u}} (ι : T ⟶ S) (g : X ⟶ Y) (p : Y ⟶ S)
    (U : X.Opens) (V : Y.Opens) (hUV : U ≤ g ⁻¹ᵁ V)
    (h : Etale (pullback.map (g ≫ p) ι p ι g (𝟙 _) (𝟙 _) (by simp) (by simp))) :
    Etale (pullback.map (g.resLE V U hUV ≫ V.ι ≫ p) ι (V.ι ≫ p) ι (g.resLE V U hUV) (𝟙 _) (𝟙 _)
      (by simp) (by simp)) := by
  have hg₁ : g.resLE V U hUV ≫ V.ι = U.ι ≫ g := Scheme.Hom.resLE_comp_ι ..
  have hgp₁ : g.resLE V U hUV ≫ V.ι ≫ p = U.ι ≫ g ≫ p := by
    rw [← Category.assoc, hg₁, Category.assoc]
  have ha : IsOpenImmersion (pullback.map (g.resLE V U hUV ≫ V.ι ≫ p) ι (g ≫ p) ι U.ι (𝟙 _)
      (𝟙 _) (by rw [Category.comp_id, hgp₁]) (by simp)) :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) (i₁ := U.ι) (i₂ := 𝟙 _)
      (inferInstanceAs (IsOpenImmersion U.ι)) (inferInstanceAs (IsOpenImmersion (𝟙 _))) hgp₁
      (by simp)
  have hb : IsOpenImmersion (pullback.map (V.ι ≫ p) ι p ι V.ι (𝟙 _) (𝟙 _) (by simp)
      (by simp)) :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) (i₁ := V.ι) (i₂ := 𝟙 _)
      (inferInstanceAs (IsOpenImmersion V.ι)) (inferInstanceAs (IsOpenImmersion (𝟙 _))) rfl
      (by simp)
  have heq : pullback.map (g.resLE V U hUV ≫ V.ι ≫ p) ι (V.ι ≫ p) ι (g.resLE V U hUV) (𝟙 _)
      (𝟙 _) (by simp) (by simp) ≫
      pullback.map (V.ι ≫ p) ι p ι V.ι (𝟙 _) (𝟙 _) (by simp) (by simp) =
      pullback.map (g.resLE V U hUV ≫ V.ι ≫ p) ι (g ≫ p) ι U.ι (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, hgp₁]) (by simp) ≫
      pullback.map (g ≫ p) ι p ι g (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext <;>
      simp only [pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, Category.comp_id, hg₁]
  have : Etale (pullback.map (g.resLE V U hUV ≫ V.ι ≫ p) ι (V.ι ≫ p) ι (g.resLE V U hUV) (𝟙 _)
      (𝟙 _) (by simp) (by simp) ≫
      pullback.map (V.ι ≫ p) ι p ι V.ι (𝟙 _) (𝟙 _) (by simp) (by simp)) := by
    rw [heq]
    infer_instance
  exact Etale.of_comp _ (pullback.map (V.ι ≫ p) ι p ι V.ι (𝟙 _) (𝟙 _) _ _)

/-- **A morphism whose adic base changes are étale is étale along the closed fibre.** Let
`p : Y ⟶ Spec A` with `Y` locally Noetherian, `g : X ⟶ Y` locally of finite type, and suppose the
base change of `g` to every adic thickening `Spec (A / I^{n+1})` is étale. Then every point of `X`
lying over `V(I)` has an open neighbourhood on which `g` is étale. -/
theorem exists_isOpenImmersion_etale_of_forall_etale_pullbackMap {X Y : Scheme.{u}}
    [IsLocallyNoetherian Y] (g : X ⟶ Y) [LocallyOfFiniteType g] (p : Y ⟶ Spec (.of A))
    (h : ∀ n : ℕ, Etale (pullback.map (g ≫ p) (adicThickeningι A I n) p (adicThickeningι A I n)
      g (𝟙 _) (𝟙 _) (by simp) (by simp)))
    (x : X) (hx : ∃ n, (g ≫ p) x ∈ Set.range (adicThickeningι A I n)) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ X), IsOpenImmersion j ∧ x ∈ Set.range j ∧ Etale (j ≫ g) := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := g x) (U := ⊤) trivial
  obtain ⟨U, hU, hxU, hUV'⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := g ⁻¹ᵁ V) hxV
  have hUV : U ≤ g ⁻¹ᵁ V := hUV'
  have : IsAffine U := hU
  have : IsAffine V := hV
  have hg₁ : g.resLE V U hUV ≫ V.ι = U.ι ≫ g := Scheme.Hom.resLE_comp_ι ..
  have hx₁ : ∃ n, (g.resLE V U hUV ≫ V.ι ≫ p) ⟨x, hxU⟩ ∈
      Set.range (adicThickeningι A I n) := by
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, by rwa [← Category.assoc, hg₁]⟩
  obtain ⟨Z, j, hj, ⟨z, hz⟩, hjE⟩ :=
    exists_isOpenImmersion_etale_of_forall_etale_pullbackMap_of_isAffine I (g.resLE V U hUV)
      (V.ι ≫ p) (fun n => etale_pullbackMap_resLE _ g p U V hUV (h n)) ⟨x, hxU⟩ hx₁
  refine ⟨Z, j ≫ U.ι, inferInstance, ⟨z, ?_⟩, ?_⟩
  · change U.ι (j z) = x
    rw [hz]
    rfl
  · rw [Category.assoc, ← hg₁, ← Category.assoc]
    infer_instance

/-- A morphism whose composite with an open immersion is flat is flat: the stalk maps of an
open immersion are isomorphisms. -/
theorem flat_of_flat_comp_isOpenImmersion {X Y Z : Scheme.{u}} (k : X ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion b] [Flat (k ≫ b)] : Flat k := by
  refine Flat.of_stalkMap k fun x => ?_
  have h := Flat.stalkMap (k ≫ b) x
  rw [Scheme.Hom.stalkMap_comp] at h
  have h' : ((k.stalkMap x).hom.comp (b.stalkMap (k x)).hom).Flat := h
  exact (RingHom.Flat.comp_iff_of_bijective_right
    (ConcreteCategory.bijective_of_isIso (b.stalkMap (k x)))).mp h'

/-- **The affine model.** Let `A → D → C` be ring maps with `D` Noetherian and `D → C` of finite
type. If the base change of `Spec C ⟶ Spec D` to every `Spec (A / I^{n+1})` is flat, then for
every prime `q ⊇ IC` of `C` some `s ∉ q` has `D → C_s` flat. -/
theorem exists_notMem_flat_away_of_forall_flat_pullbackMap_spec (D C : Type u) [CommRing D]
    [CommRing C] [Algebra A D] [Algebra D C] [Algebra A C] [IsScalarTower A D C]
    [IsNoetherianRing D] [Algebra.FiniteType D C]
    (h : ∀ n : ℕ, Flat (pullback.map (Spec.map (CommRingCat.ofHom (algebraMap A C)))
      (adicThickeningι A I n) (Spec.map (CommRingCat.ofHom (algebraMap A D)))
      (adicThickeningι A I n) (Spec.map (CommRingCat.ofHom (algebraMap D C))) (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq])
      (by simp)))
    (q : Ideal C) [q.IsPrime] (hq : I.map (algebraMap A C) ≤ q) :
    ∃ s ∉ q, Module.Flat D (Localization.Away s) := by
  set J : Ideal D := I.map (algebraMap A D)
  have hJ : J.map (algebraMap D C) ≤ q := by
    rwa [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  refine Algebra.exists_notMem_flat_localization_away_of_forall_flat_quotient_pow J q hJ
    fun n => ?_
  set K : Ideal A := I ^ (n + 1)
  let T := A ⧸ K
  -- the base change, read on rings
  have hspec : RingHom.Flat (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A D C)
      (AlgHom.id A T)).toRingHom := by
    have h' : Flat ((pullbackSpecIso A C T).inv ≫
        pullback.map (Spec.map (CommRingCat.ofHom (algebraMap A C)))
          (Spec.map (CommRingCat.ofHom (algebraMap A T)))
          (Spec.map (CommRingCat.ofHom (algebraMap A D)))
          (Spec.map (CommRingCat.ofHom (algebraMap A T)))
          (Spec.map (CommRingCat.ofHom (algebraMap D C))) (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            ← IsScalarTower.algebraMap_eq])
          (by simp)) := by
      have hn : Flat (pullback.map (Spec.map (CommRingCat.ofHom (algebraMap A C)))
          (Spec.map (CommRingCat.ofHom (algebraMap A T)))
          (Spec.map (CommRingCat.ofHom (algebraMap A D)))
          (Spec.map (CommRingCat.ofHom (algebraMap A T)))
          (Spec.map (CommRingCat.ofHom (algebraMap D C))) (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            ← IsScalarTower.algebraMap_eq])
          (by simp)) := h n
      infer_instance
    rw [pullbackSpecIso_inv_comp_pullbackMap] at h'
    have h'' : Flat ((Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom A D C) (AlgHom.id A T)).toRingHom) ≫
          (pullbackSpecIso A D T).inv) ≫ (pullbackSpecIso A D T).hom) := inferInstance
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h''
    exact HasRingHomProperty.Spec_iff.mp h''
  -- the base change, read on quotients
  set L : Ideal D := K.map (algebraMap A D)
  have hLC : L.map (algebraMap D C) = K.map (algebraMap A C) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  let eD := Algebra.TensorProduct.quotIdealMapEquivTensorQuot D K
  let eC := Algebra.TensorProduct.quotIdealMapEquivTensorQuot C K
  have heq : algebraMap (D ⧸ L) (C ⧸ L.map (algebraMap D C)) =
      (eC.symm.toRingEquiv.trans (Ideal.quotEquivOfEq hLC).symm).toRingHom.comp
        ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom A D C)
          (AlgHom.id A T)).toRingHom.comp eD.toRingEquiv.toRingHom) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun d => ?_)
    simp only [RingHom.comp_apply, Ideal.Quotient.algebraMap_quotient_map_quotient]
    rw [show eD.toRingHom (Ideal.Quotient.mk L d) = d ⊗ₜ[A] (1 : T) from
      Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk D K d]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      IsScalarTower.coe_toAlgHom', AlgHom.coe_id, id_eq]
    have hC : eC.symm ((algebraMap D C d) ⊗ₜ[A] (1 : T)) =
        Ideal.Quotient.mk _ (algebraMap D C d) := by
      rw [AlgEquiv.symm_apply_eq]
      exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk C K _).symm
    change _ = (Ideal.quotEquivOfEq hLC).symm (eC.symm ((algebraMap D C d) ⊗ₜ[A] (1 : T)))
    rw [hC, Ideal.quotEquivOfEq_symm, Ideal.quotEquivOfEq_mk]
  have hL : Module.Flat (D ⧸ L) (C ⧸ L.map (algebraMap D C)) := by
    rw [← RingHom.flat_algebraMap_iff, heq]
    exact RingHom.Flat.respectsIso.1 _ _ (RingHom.Flat.respectsIso.2 _ _ hspec)
  have hLJ : L = J ^ (n + 1) := Ideal.map_pow _ _ _
  rw [hLJ] at hL
  exact hL

/-- Flatness of the base change of `g : X ⟶ Y` along `ι` is unchanged on replacing `X` and `Y`
by isomorphic schemes. -/
theorem flat_pullbackMap_of_iso {X Y X' Y' S T : Scheme.{u}} (ι : T ⟶ S) (g : X ⟶ Y)
    (p : Y ⟶ S) (g' : X' ⟶ Y') (p' : Y' ⟶ S) (f' : X' ⟶ S) (eX : X ≅ X') (eY : Y ≅ Y')
    (hg : eX.hom ≫ g' = g ≫ eY.hom) (hp : eY.hom ≫ p' = p) (hf' : g' ≫ p' = f')
    (h : Flat (pullback.map (g ≫ p) ι p ι g (𝟙 _) (𝟙 _) (by simp) (by simp))) :
    Flat (pullback.map f' ι p' ι g' (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hf']) (by simp)) := by
  subst hp hf'
  have hg' : eX.inv ≫ g ≫ eY.hom = g' := by rw [← hg, Iso.inv_hom_id_assoc]
  have e : pullback.map (g' ≫ p') ι (g ≫ eY.hom ≫ p') ι eX.inv (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, ← hg', Category.assoc, Category.assoc]) (by simp) ≫
      pullback.map (g ≫ eY.hom ≫ p') ι (eY.hom ≫ p') ι g (𝟙 _) (𝟙 _) (by simp) (by simp) ≫
      pullback.map (eY.hom ≫ p') ι p' ι eY.hom (𝟙 _) (𝟙 _) (by simp) (by simp) =
      pullback.map (g' ≫ p') ι p' ι g' (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext <;>
      simp only [pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, Category.comp_id, hg']
  have : Flat (pullback.map (g' ≫ p') ι (g ≫ eY.hom ≫ p') ι eX.inv (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, ← hg', Category.assoc, Category.assoc]) (by simp) ≫
      pullback.map (g ≫ eY.hom ≫ p') ι (eY.hom ≫ p') ι g (𝟙 _) (𝟙 _) (by simp) (by simp) ≫
      pullback.map (eY.hom ≫ p') ι p' ι eY.hom (𝟙 _) (𝟙 _) (by simp) (by simp)) :=
    inferInstance
  rwa [e] at this

/-- **The affine case.** Let `X`, `Y` be affine with `Y` Noetherian, `g : X ⟶ Y` locally of
finite type and `p : Y ⟶ Spec A`. If the base change of `g` to every `Spec (A / I^{n+1})` is
flat, then `g` is flat on an open neighbourhood of every point of `X` over `V(I)`. -/
theorem exists_isOpenImmersion_flat_of_forall_flat_pullbackMap_of_isAffine {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] [IsLocallyNoetherian Y] (g : X ⟶ Y) [LocallyOfFiniteType g]
    (p : Y ⟶ Spec (.of A))
    (h : ∀ n : ℕ, Flat (pullback.map (g ≫ p) (adicThickeningι A I n) p (adicThickeningι A I n)
      g (𝟙 _) (𝟙 _) (by simp) (by simp)))
    (x : X) (hx : ∃ n, (g ≫ p) x ∈ Set.range (adicThickeningι A I n)) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ X), IsOpenImmersion j ∧ x ∈ Set.range j ∧ Flat (j ≫ g) := by
  let C := Γ(X, ⊤)
  let D := Γ(Y, ⊤)
  let : Algebra D C := g.appTop.hom.toAlgebra
  let : Algebra A D := ((Scheme.ΓSpecIso (.of A)).inv ≫ p.appTop).hom.toAlgebra
  let : Algebra A C := ((Scheme.ΓSpecIso (.of A)).inv ≫ p.appTop ≫ g.appTop).hom.toAlgebra
  have : IsScalarTower A D C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsNoetherianRing D := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  have : Algebra.FiniteType D C := HasRingHomProperty.iff_of_isAffine.mp ‹LocallyOfFiniteType g›
  have hg : X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap D C)) = g ≫ Y.isoSpec.hom :=
    Scheme.isoSpec_hom_naturality g
  have hp : Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A D)) = p := by
    change Y.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of A)).inv ≫ p.appTop) = p
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
  have hf : Spec.map (CommRingCat.ofHom (algebraMap D C)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A D)) =
        Spec.map (CommRingCat.ofHom (algebraMap A C)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have h' := fun n => flat_pullbackMap_of_iso (adicThickeningι A I n) g p _ _ _ X.isoSpec
    Y.isoSpec hg hp hf (h n)
  let q : Ideal C := (X.isoSpec.hom x).asIdeal
  have : q.IsPrime := (X.isoSpec.hom x).isPrime
  have hgp : g ≫ p = X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)) := by
    rw [← hp, ← reassoc_of% hg, hf]
  have hq : I.map (algebraMap A C) ≤ q := by
    obtain ⟨n, y, hy⟩ := hx
    have hK : I ^ (n + 1) ≤ ((g ≫ p) x).asIdeal := by
      rw [← hy]
      intro a ha
      change Ideal.Quotient.mk (I ^ (n + 1)) a ∈ y.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact zero_mem _
    rw [hgp] at hK
    change I ^ (n + 1) ≤ q.comap (algebraMap A C) at hK
    exact Ideal.map_le_iff_le_comap.mpr ((Ideal.comap_isPrime _ q).le_of_pow_le hK)
  obtain ⟨s, hs, hsF⟩ := exists_notMem_flat_away_of_forall_flat_pullbackMap_spec I D C h' q hq
  refine ⟨Spec (.of (Localization.Away s)),
    Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away s))) ≫ X.isoSpec.inv,
    inferInstance, ?_, ?_⟩
  · have hmem : (⟨q, inferInstance⟩ : PrimeSpectrum C) ∈
        Set.range (PrimeSpectrum.comap (algebraMap C (Localization.Away s))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away s) s]
      exact hs
    obtain ⟨z, hz⟩ := hmem
    refine ⟨z, ?_⟩
    change X.isoSpec.inv (PrimeSpectrum.comap (algebraMap C (Localization.Away s)) z) = x
    rw [hz]
    change (X.isoSpec.hom ≫ X.isoSpec.inv) x = x
    rw [Iso.hom_inv_id]
    rfl
  · have e : (Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away s))) ≫
        X.isoSpec.inv) ≫ g =
          Spec.map (CommRingCat.ofHom (algebraMap D (Localization.Away s))) ≫ Y.isoSpec.inv := by
      rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Category.assoc, ← Spec.map_comp,
        IsScalarTower.algebraMap_eq D C (Localization.Away s), CommRingCat.ofHom_comp]
      rfl
    rw [e]
    have : Flat (Spec.map (CommRingCat.ofHom (algebraMap D (Localization.Away s)))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.flat_algebraMap_iff.mpr hsF)
    infer_instance

/-- Flatness of the base change of `g` along `ι` restricts to open subschemes `U ⊆ g⁻¹ V`. -/
theorem flat_pullbackMap_resLE {X Y S T : Scheme.{u}} (ι : T ⟶ S) (g : X ⟶ Y) (p : Y ⟶ S)
    (U : X.Opens) (V : Y.Opens) (hUV : U ≤ g ⁻¹ᵁ V)
    (h : Flat (pullback.map (g ≫ p) ι p ι g (𝟙 _) (𝟙 _) (by simp) (by simp))) :
    Flat (pullback.map (g.resLE V U hUV ≫ V.ι ≫ p) ι (V.ι ≫ p) ι (g.resLE V U hUV) (𝟙 _) (𝟙 _)
      (by simp) (by simp)) := by
  have hg₁ : g.resLE V U hUV ≫ V.ι = U.ι ≫ g := Scheme.Hom.resLE_comp_ι ..
  have hgp₁ : g.resLE V U hUV ≫ V.ι ≫ p = U.ι ≫ g ≫ p := by
    rw [← Category.assoc, hg₁, Category.assoc]
  have ha : IsOpenImmersion (pullback.map (g.resLE V U hUV ≫ V.ι ≫ p) ι (g ≫ p) ι U.ι (𝟙 _)
      (𝟙 _) (by rw [Category.comp_id, hgp₁]) (by simp)) :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) (i₁ := U.ι) (i₂ := 𝟙 _)
      (inferInstanceAs (IsOpenImmersion U.ι)) (inferInstanceAs (IsOpenImmersion (𝟙 _))) hgp₁
      (by simp)
  have hb : IsOpenImmersion (pullback.map (V.ι ≫ p) ι p ι V.ι (𝟙 _) (𝟙 _) (by simp)
      (by simp)) :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) (i₁ := V.ι) (i₂ := 𝟙 _)
      (inferInstanceAs (IsOpenImmersion V.ι)) (inferInstanceAs (IsOpenImmersion (𝟙 _))) rfl
      (by simp)
  have heq : pullback.map (g.resLE V U hUV ≫ V.ι ≫ p) ι (V.ι ≫ p) ι (g.resLE V U hUV) (𝟙 _)
      (𝟙 _) (by simp) (by simp) ≫
      pullback.map (V.ι ≫ p) ι p ι V.ι (𝟙 _) (𝟙 _) (by simp) (by simp) =
      pullback.map (g.resLE V U hUV ≫ V.ι ≫ p) ι (g ≫ p) ι U.ι (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, hgp₁]) (by simp) ≫
      pullback.map (g ≫ p) ι p ι g (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext <;>
      simp only [pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, Category.comp_id, hg₁]
  have : Flat (pullback.map (g.resLE V U hUV ≫ V.ι ≫ p) ι (V.ι ≫ p) ι (g.resLE V U hUV) (𝟙 _)
      (𝟙 _) (by simp) (by simp) ≫
      pullback.map (V.ι ≫ p) ι p ι V.ι (𝟙 _) (𝟙 _) (by simp) (by simp)) := by
    rw [heq]
    infer_instance
  exact flat_of_flat_comp_isOpenImmersion _ (pullback.map (V.ι ≫ p) ι p ι V.ι (𝟙 _) (𝟙 _) _ _)

/-- **A morphism whose adic base changes are flat is flat along the closed fibre.** Let
`p : Y ⟶ Spec A` with `Y` locally Noetherian, `g : X ⟶ Y` locally of finite type, and suppose the
base change of `g` to every adic thickening `Spec (A / I^{n+1})` is flat. Then every point of `X`
lying over `V(I)` has an open neighbourhood on which `g` is flat. -/
theorem exists_isOpenImmersion_flat_of_forall_flat_pullbackMap {X Y : Scheme.{u}}
    [IsLocallyNoetherian Y] (g : X ⟶ Y) [LocallyOfFiniteType g] (p : Y ⟶ Spec (.of A))
    (h : ∀ n : ℕ, Flat (pullback.map (g ≫ p) (adicThickeningι A I n) p (adicThickeningι A I n)
      g (𝟙 _) (𝟙 _) (by simp) (by simp)))
    (x : X) (hx : ∃ n, (g ≫ p) x ∈ Set.range (adicThickeningι A I n)) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ X), IsOpenImmersion j ∧ x ∈ Set.range j ∧ Flat (j ≫ g) := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := g x) (U := ⊤) trivial
  obtain ⟨U, hU, hxU, hUV'⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := g ⁻¹ᵁ V) hxV
  have hUV : U ≤ g ⁻¹ᵁ V := hUV'
  have : IsAffine U := hU
  have : IsAffine V := hV
  have hg₁ : g.resLE V U hUV ≫ V.ι = U.ι ≫ g := Scheme.Hom.resLE_comp_ι ..
  have hx₁ : ∃ n, (g.resLE V U hUV ≫ V.ι ≫ p) ⟨x, hxU⟩ ∈
      Set.range (adicThickeningι A I n) := by
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, by rwa [← Category.assoc, hg₁]⟩
  obtain ⟨Z, j, hj, ⟨z, hz⟩, hjF⟩ :=
    exists_isOpenImmersion_flat_of_forall_flat_pullbackMap_of_isAffine I (g.resLE V U hUV)
      (V.ι ≫ p) (fun n => flat_pullbackMap_resLE _ g p U V hUV (h n)) ⟨x, hxU⟩ hx₁
  refine ⟨Z, j ≫ U.ι, inferInstance, ⟨z, ?_⟩, ?_⟩
  · change U.ι (j z) = x
    rw [hz]
    rfl
  · rw [Category.assoc, ← hg₁, ← Category.assoc]
    infer_instance

end AlgebraicGeometry

end
