module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.Embedding.UpNatZero
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.Algebra.Module.Pure.Ext
public import StacksFrontier.Algebra.Module.Pure.ProjectiveResolution
public import StacksFrontier.Algebra.Module.Pure.ResolutionExistence

/-!
# Pure extensions computed by a pure projective resolution

The pure extension modules `Pext^i_A(M, N)` are the cohomology of `Hom_A(M, Iᐧ)` for a pure
injective resolution `I` of `N`.  This file identifies them with the cohomology of
`Hom_A(Pᐧ, N)` for a pure projective resolution `P` of `M`, by comparing both with the total
complex of the double complex `Hom_A(Pᐧ, Iᐧ)`.

## References

* [Stacks Project, Tag 0706](https://stacks.math.columbia.edu/tag/0706)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open StacksDraft.TotalComplexQuasiIso

namespace Module

section

universe u v

variable {A : Type u} [CommRing A]

/-- The differential of `Hom_A(Pᐧ, N)` is precomposition with the differential of `P`. -/
public lemma homComplexOfChain_d (P : ChainComplex (ModuleCat.{v} A) ℕ)
    (N : Type v) [AddCommGroup N] [Module A N] (n : ℕ) :
    ((Module.homComplexOfChain P N).d n (n + 1)).hom =
      LinearMap.lcomp A N (P.d (n + 1) n).hom := by
  simp only [Module.homComplexOfChain, CochainComplex.of_d, ModuleCat.hom_ofHom]
  rfl

/-- The differential of `Hom_A(M, Iᐧ)` is postcomposition with the differential of `I`. -/
public lemma homComplex_d (M : Type v) [AddCommGroup M] [Module A M]
    (I : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    ((Module.homComplex M I).d n (n + 1)).hom =
      LinearMap.compRight A (I.d n (n + 1)).hom := by
  ext φ
  simp only [Module.homComplex, CochainComplex.of_d, ModuleCat.hom_ofHom]
  rfl

/-- `Hom_A(Pᐧ, -)` as a functor from `A`-modules to cochain complexes of `A`-modules. -/
public noncomputable def homComplexOfChainFunctor (P : ChainComplex (ModuleCat.{v} A) ℕ) :
    ModuleCat.{v} A ⥤ CochainComplex (ModuleCat.{v} A) ℕ where
  obj J := Module.homComplexOfChain P J
  map {J J'} f :=
    { f := fun _ => ModuleCat.ofHom (LinearMap.compRight A f.hom)
      comm' := fun n n' h => by
        obtain rfl : n + 1 = n' := h
        ext φ
        change ((Module.homComplexOfChain P (J' : Type v)).d n (n + 1)).hom
            (LinearMap.compRight A f.hom φ) =
          LinearMap.compRight A f.hom
            (((Module.homComplexOfChain P (J : Type v)).d n (n + 1)).hom φ)
        rw [Module.homComplexOfChain_d, Module.homComplexOfChain_d]
        exact LinearMap.ext fun _ => rfl }
  map_id _ := by
    ext n φ
    exact LinearMap.ext fun _ => rfl
  map_comp _ _ := by
    ext n φ
    exact LinearMap.ext fun _ => rfl

/-- `Hom_A(Pᐧ, -)` is an additive functor. -/
public instance homComplexOfChainFunctor_additive (P : ChainComplex (ModuleCat.{v} A) ℕ) :
    (Module.homComplexOfChainFunctor P).Additive where
  map_add {_ _ _ _} := by
    ext n φ
    exact LinearMap.ext fun _ => rfl

/-- Precomposition with `f : Q →ₗ[A] M` as a map of complexes `Hom_A(M, Iᐧ) ⟶ Hom_A(Q, Iᐧ)`. -/
public noncomputable def homComplexPrecomp {M Q : Type v} [AddCommGroup M] [Module A M]
    [AddCommGroup Q] [Module A Q] (f : Q →ₗ[A] M)
    (I : CochainComplex (ModuleCat.{v} A) ℕ) :
    Module.homComplex M I ⟶ Module.homComplex Q I where
  f n := ModuleCat.ofHom (LinearMap.lcomp A (I.X n) f)
  comm' n n' h := by
    obtain rfl : n + 1 = n' := h
    ext φ
    change ((Module.homComplex (Q : Type v) I).d n (n + 1)).hom
        (LinearMap.lcomp A (I.X n) f φ) =
      LinearMap.lcomp A (I.X (n + 1)) f
        (((Module.homComplex (M : Type v) I).d n (n + 1)).hom φ)
    rw [Module.homComplex_d, Module.homComplex_d]
    exact LinearMap.ext fun _ => rfl

/-- Postcomposition with `g : N →ₗ[A] J` as a map of complexes
`Hom_A(Pᐧ, N) ⟶ Hom_A(Pᐧ, J)`. -/
public noncomputable def homComplexOfChainPostcomp (P : ChainComplex (ModuleCat.{v} A) ℕ)
    {N J : Type v} [AddCommGroup N] [Module A N] [AddCommGroup J] [Module A J]
    (g : N →ₗ[A] J) :
    Module.homComplexOfChain P N ⟶ Module.homComplexOfChain P J where
  f n := ModuleCat.ofHom (LinearMap.compRight A g)
  comm' n n' h := by
    obtain rfl : n + 1 = n' := h
    ext φ
    change ((Module.homComplexOfChain P (J : Type v)).d n (n + 1)).hom
        (LinearMap.compRight A g φ) =
      LinearMap.compRight A g (((Module.homComplexOfChain P (N : Type v)).d n (n + 1)).hom φ)
    rw [Module.homComplexOfChain_d, Module.homComplexOfChain_d]
    exact LinearMap.ext fun _ => rfl

/-- The `ℕ × ℕ` double complex `(p, q) ↦ Hom_A(P_q, Iᵖ)`: the degree in `I` is the outer index
and the degree in `P` the inner one. -/
@[sga "2 VIII 1.4" "The double complex Q^{p"]
public noncomputable def homBicomplexNat (P : ChainComplex (ModuleCat.{v} A) ℕ)
    (I : CochainComplex (ModuleCat.{v} A) ℕ) :
    HomologicalComplex₂ (ModuleCat.{v} A) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  ((Module.homComplexOfChainFunctor P).mapHomologicalComplex (ComplexShape.up ℕ)).obj I

/-- `homBicomplexNat` with the inner index extended by zero to `ℤ`. -/
public noncomputable def homBicomplexInner (P : ChainComplex (ModuleCat.{v} A) ℕ)
    (I : CochainComplex (ModuleCat.{v} A) ℕ) :
    HomologicalComplex (CochainComplex (ModuleCat.{v} A) ℤ) (ComplexShape.up ℕ) :=
  ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{v} A)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (Module.homBicomplexNat P I)

/-- The double complex `Hom_A(Pᐧ, Iᐧ)` over `ℤ × ℤ`: both indices of `homBicomplexNat`
extended by zero. -/
@[sga "2 VIII 1.4" "The double complex Q^{p"]
public noncomputable def homBicomplex (P : ChainComplex (ModuleCat.{v} A) ℕ)
    (I : CochainComplex (ModuleCat.{v} A) ℕ) :
    HomologicalComplex₂ (ModuleCat.{v} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (Module.homBicomplexInner P I).extend ComplexShape.embeddingUpNat

/-- The `p`-th column of `Hom_A(Pᐧ, Iᐧ)` is `Hom_A(Pᐧ, Iᵖ)`, extended by zero. -/
public noncomputable def homBicomplexColumnIso (P : ChainComplex (ModuleCat.{v} A) ℕ)
    (I : CochainComplex (ModuleCat.{v} A) ℕ) (p : ℕ) {p' : ℤ}
    (hp : ComplexShape.embeddingUpNat.f p = p') :
    (Module.homBicomplex P I).X p' ≅
      (Module.homComplexOfChain P (I.X p)).extend ComplexShape.embeddingUpNat :=
  HomologicalComplex.extendXIso (Module.homBicomplexInner P I) ComplexShape.embeddingUpNat hp

/-- The `q`-th row of the `ℕ × ℕ` double complex is `Hom_A(P_q, Iᐧ)`. -/
public noncomputable def homBicomplexNatRowIso (P : ChainComplex (ModuleCat.{v} A) ℕ)
    (I : CochainComplex (ModuleCat.{v} A) ℕ) (q : ℕ) :
    (Module.homBicomplexNat P I).flip.X q ≅ Module.homComplex (P.X q) I :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun p p' h => by
    obtain rfl : p + 1 = p' := h
    apply ModuleCat.hom_ext
    change ((Module.homComplex (P.X q : Type v) I).d p (p + 1)).hom =
      (((Module.homBicomplexNat P I).flip.X q).d p (p + 1)).hom
    rw [Module.homComplex_d]
    rfl)

/-- The `q`-th row of `Hom_A(Pᐧ, Iᐧ)` is `Hom_A(P_q, Iᐧ)`, extended by zero. -/
public noncomputable def homBicomplexRowIso (P : ChainComplex (ModuleCat.{v} A) ℕ)
    (I : CochainComplex (ModuleCat.{v} A) ℕ) (q : ℕ) {q' : ℤ}
    (hq : ComplexShape.embeddingUpNat.f q = q') :
    (Module.homBicomplex P I).flip.X q' ≅
      (Module.homComplex (P.X q) I).extend ComplexShape.embeddingUpNat :=
  (HomologicalComplex.eval (ModuleCat.{v} A) (ComplexShape.up ℤ) q').mapExtendIso
      (Module.homBicomplexInner P I) ComplexShape.embeddingUpNat ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{v} A)).mapIso
      ((NatIso.mapHomologicalComplex
        (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso (ModuleCat.{v} A) hq)
        (ComplexShape.up ℕ)).app (Module.homBicomplexNat P I) ≪≫
          Module.homBicomplexNatRowIso P I q)

/-- `Hom_A(Pᐧ, Iᐧ)` vanishes in negative outer degree. -/
public lemma isZero_homBicomplex_X (P : ChainComplex (ModuleCat.{v} A) ℕ)
    (I : CochainComplex (ModuleCat.{v} A) ℕ) (p : ℤ) (hp : p < 0) :
    IsZero ((Module.homBicomplex P I).X p) :=
  HomologicalComplex.isZero_extend_X (Module.homBicomplexInner P I)
    ComplexShape.embeddingUpNat p (fun n h => by change (n : ℤ) = p at h; omega)

/-- `Hom_A(Pᐧ, Iᐧ)` vanishes outside the first quadrant. -/
public lemma isZero_homBicomplex_X_X (P : ChainComplex (ModuleCat.{v} A) ℕ)
    (I : CochainComplex (ModuleCat.{v} A) ℕ) (p q : ℤ) (h : p < 0 ∨ q < 0) :
    IsZero (((Module.homBicomplex P I).X p).X q) := by
  rcases h with hp | hq
  · exact (HomologicalComplex.eval (ModuleCat.{v} A) (ComplexShape.up ℤ) q).map_isZero
      (Module.isZero_homBicomplex_X P I p hp)
  · by_cases hp : p < 0
    · exact (HomologicalComplex.eval (ModuleCat.{v} A) (ComplexShape.up ℤ) q).map_isZero
        (Module.isZero_homBicomplex_X P I p hp)
    · lift p to ℕ using (by omega : 0 ≤ p)
      refine IsZero.of_iso ?_ ((HomologicalComplex.eval (ModuleCat.{v} A)
        (ComplexShape.up ℤ) q).mapIso (Module.homBicomplexColumnIso P I p rfl))
      exact HomologicalComplex.isZero_extend_X (Module.homComplexOfChain P (I.X p))
        ComplexShape.embeddingUpNat q (fun n h => by change (n : ℤ) = q at h; omega)

/-- Only finitely many terms of `Hom_A(Pᐧ, Iᐧ)` on each diagonal are nonzero. -/
public lemma diagonalFinite_homBicomplex (P : ChainComplex (ModuleCat.{v} A) ℕ)
    (I : CochainComplex (ModuleCat.{v} A) ℕ) :
    DiagonalFinite (Module.homBicomplex P I) := by
  intro n
  refine (Set.finite_Icc (0 : ℤ) n).subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp
  refine Set.mem_Icc.2 ⟨?_, ?_⟩
  · by_contra h
    exact hp (Module.isZero_homBicomplex_X_X P I p (n - p) (Or.inl (by omega)))
  · by_contra h
    exact hp (Module.isZero_homBicomplex_X_X P I p (n - p) (Or.inr (by omega)))

/-- The total complex of `Hom_A(Pᐧ, Iᐧ)` exists. -/
public lemma hasTotal_homBicomplex (P : ChainComplex (ModuleCat.{v} A) ℕ)
    (I : CochainComplex (ModuleCat.{v} A) ℕ) :
    (Module.homBicomplex P I).HasTotal (ComplexShape.up ℤ) :=
  hasTotal_of_bounded (Module.homBicomplex P I) 0
    (fun p q hq => Module.isZero_homBicomplex_X_X P I p q (Or.inr hq))
    (fun p hp => Module.isZero_homBicomplex_X P I p hp)

/-- Only finitely many terms of `Hom_A(Pᐧ, Iᐧ)` on each diagonal of the flipped double complex
are nonzero. -/
public lemma diagonalFinite_homBicomplex_flip (P : ChainComplex (ModuleCat.{v} A) ℕ)
    (I : CochainComplex (ModuleCat.{v} A) ℕ) :
    DiagonalFinite (Module.homBicomplex P I).flip := by
  intro n
  refine (Set.finite_Icc (0 : ℤ) n).subset ?_
  intro q hq
  simp only [Set.mem_setOf_eq] at hq
  refine Set.mem_Icc.2 ⟨?_, ?_⟩
  · by_contra h
    exact hq (Module.isZero_homBicomplex_X_X P I (n - q) q (Or.inr (by omega)))
  · by_contra h
    exact hq (Module.isZero_homBicomplex_X_X P I (n - q) q (Or.inl (by omega)))

/-! ### General facts about kernels -/

/-- A composite of morphisms of modules vanishes as soon as it vanishes on elements. -/
private lemma comp_eq_zero_of_comp_hom {X Y Z : ModuleCat.{v} A} {f : X ⟶ Y} {g : Y ⟶ Z}
    (h : g.hom.comp f.hom = 0) : f ≫ g = 0 := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, h, ModuleCat.hom_zero]

private lemma isIso_kernelLift_of_mono_of_exact {C : Type*} [Category C] [Abelian C]
    {T B₁ B₂ : C} (f : T ⟶ B₁) (g : B₁ ⟶ B₂) (hf : f ≫ g = 0) [Mono f]
    (hex : (ShortComplex.mk f g hf).Exact) :
    IsIso (kernel.lift g f hf) :=
  have : Mono (kernel.lift g f hf) := mono_of_mono_fac (kernel.lift_ι g f hf)
  have : Epi (kernel.lift g f hf) :=
    (ShortComplex.mk f g hf).exact_iff_epi_kernel_lift.1 hex
  isIso_of_mono_of_epi _

private lemma isIso_kernelLift_of_iso {C : Type*} [Category C] [Abelian C]
    {T B₁ B₂ T' B₁' B₂' : C} {f : T ⟶ B₁} {g : B₁ ⟶ B₂} (hf : f ≫ g = 0)
    {f' : T' ⟶ B₁'} {g' : B₁' ⟶ B₂'} (hf' : f' ≫ g' = 0)
    (eT : T ≅ T') (eA : B₁ ≅ B₁') (eB : B₂ ≅ B₂')
    (h1 : f ≫ eA.hom = eT.hom ≫ f') (h2 : g ≫ eB.hom = eA.hom ≫ g')
    (h : IsIso (kernel.lift g f hf)) :
    IsIso (kernel.lift g' f' hf') := by
  have := h
  have hm : Mono f := by rw [← kernel.lift_ι g f hf]; infer_instance
  have hex : (ShortComplex.mk f g hf).Exact :=
    (ShortComplex.mk f g hf).exact_iff_epi_kernel_lift.2 inferInstance
  have hm' : Mono f' := by
    have hf'eq : f' = eT.inv ≫ f ≫ eA.hom := by
      rw [h1, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rw [hf'eq]; infer_instance
  have e : ShortComplex.mk f g hf ≅ ShortComplex.mk f' g' hf' :=
    ShortComplex.isoMk eT eA eB h1.symm h2.symm
  exact isIso_kernelLift_of_mono_of_exact _ _ _ (ShortComplex.exact_of_iso e hex)

private lemma comp_eq_zero_of_iso {C : Type*} [Category C] [Abelian C]
    {T B₁ B₂ T' B₁' B₂' : C} {f : T ⟶ B₁} {g : B₁ ⟶ B₂} (hf : f ≫ g = 0)
    {f' : T' ⟶ B₁'} {g' : B₁' ⟶ B₂'} (eT : T ≅ T') (eA : B₁ ≅ B₁') (eB : B₂ ≅ B₂')
    (h1 : f ≫ eA.hom = eT.hom ≫ f') (h2 : g ≫ eB.hom = eA.hom ≫ g') :
    f' ≫ g' = 0 := by
  have hf' : f' = eT.inv ≫ f ≫ eA.hom := by
    rw [h1, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [hf']
  simp only [Category.assoc]
  rw [← h2, ← Category.assoc f g eB.hom, hf, zero_comp, comp_zero]

/-- A map from a zero object into a zero object lifts to an isomorphism onto the kernel. -/
private lemma exists_isIso_kernelLift_of_isZero {C : Type*} [Category C] [Abelian C]
    {S B₁ B₂ : C} (a : S ⟶ B₁) (d : B₁ ⟶ B₂) (hS : IsZero S) (hB : IsZero B₁) :
    ∃ h : a ≫ d = 0, IsIso (kernel.lift d a h) :=
  ⟨hS.eq_of_src _ _, 0, hS.eq_of_src _ _, (IsZero.of_mono (kernel.ι d) hB).eq_of_src _ _⟩

/-- An integer which is not a natural number is negative. -/
private lemma neg_of_not_exists_natCast {p : ℤ} (hp : ¬∃ n : ℕ, (n : ℤ) = p) : p < 0 := by
  rcases lt_trichotomy p 0 with h | h | h
  · exact h
  · exact absurd ⟨0, by omega⟩ hp
  · exact absurd ⟨p.toNat, by omega⟩ hp

/-- **The kernel clause of [Stacks, Tag 0133] from an `ℕ`-indexed augmentation.**  If `ξ` is a
monomorphism onto the kernel of the first differential of an `ℕ`-indexed complex `C₀`, then any
map into a complex isomorphic to the extension of `C₀` which agrees with `ξ` under the
identifications is a kernel of the first differential there. -/
private lemma isIso_kernelLift_of_extendAugmentation
    {C₀ : CochainComplex (ModuleCat.{v} A) ℕ} {Z : CochainComplex (ModuleCat.{v} A) ℤ}
    (Φ : Z ≅ C₀.extend ComplexShape.embeddingUpNat)
    {T Tz : ModuleCat.{v} A} (eT : T ≅ Tz) (ξ : T ⟶ C₀.X 0)
    (hinj : Function.Injective ξ.hom) (hex : Function.Exact ξ.hom (C₀.d 0 1).hom)
    (a : Tz ⟶ Z.X 0)
    (ha : a ≫ ((HomologicalComplex.eval (ModuleCat.{v} A) (ComplexShape.up ℤ) (0 : ℤ)).mapIso
        Φ).hom =
      eT.inv ≫ ξ ≫ (C₀.extendXIso ComplexShape.embeddingUpNat
        ComplexShape.embeddingUpNat_f_zero).inv) :
    ∃ h : a ≫ Z.d 0 1 = 0, IsIso (kernel.lift (Z.d 0 1) a h) := by
  have hξ : ξ ≫ C₀.d 0 1 = 0 :=
    Module.comp_eq_zero_of_comp_hom (LinearMap.ext fun φ => hex.apply_apply_eq_zero φ)
  have : Mono ξ := (ModuleCat.mono_iff_injective ξ).2 hinj
  have hex' := ModuleCat.shortComplex_exact (ShortComplex.mk ξ (C₀.d 0 1) hξ) hex
  have h₁ : ComplexShape.embeddingUpNat.f 1 = (1 : ℤ) := rfl
  set eA : Z.X 0 ≅ (C₀.extend ComplexShape.embeddingUpNat).X 0 :=
    (HomologicalComplex.eval (ModuleCat.{v} A) (ComplexShape.up ℤ) (0 : ℤ)).mapIso Φ with heA
  set eB : Z.X 1 ≅ (C₀.extend ComplexShape.embeddingUpNat).X 1 :=
    (HomologicalComplex.eval (ModuleCat.{v} A) (ComplexShape.up ℤ) (1 : ℤ)).mapIso Φ with heB
  set ζ : T ⟶ (C₀.extend ComplexShape.embeddingUpNat).X 0 :=
    ξ ≫ (C₀.extendXIso ComplexShape.embeddingUpNat
      ComplexShape.embeddingUpNat_f_zero).inv with hζ
  have hd : (C₀.extend ComplexShape.embeddingUpNat).d 0 1 =
      (C₀.extendXIso ComplexShape.embeddingUpNat
          ComplexShape.embeddingUpNat_f_zero).hom ≫ C₀.d 0 1 ≫
        (C₀.extendXIso ComplexShape.embeddingUpNat h₁).inv :=
    C₀.extend_d_eq ComplexShape.embeddingUpNat ComplexShape.embeddingUpNat_f_zero h₁
  have hζd : ζ ≫ (C₀.extend ComplexShape.embeddingUpNat).d 0 1 = 0 := by
    rw [hζ, hd]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% hξ]
    simp
  have : Mono ζ := by rw [hζ]; infer_instance
  have hiso : IsIso (kernel.lift ((C₀.extend ComplexShape.embeddingUpNat).d 0 1) ζ hζd) := by
    have e : ShortComplex.mk ξ (C₀.d 0 1) hξ ≅
        ShortComplex.mk ζ ((C₀.extend ComplexShape.embeddingUpNat).d 0 1) hζd :=
      ShortComplex.isoMk (Iso.refl _)
        (C₀.extendXIso ComplexShape.embeddingUpNat
          ComplexShape.embeddingUpNat_f_zero).symm
        (C₀.extendXIso ComplexShape.embeddingUpNat h₁).symm (by simp [hζ]) (by simp [hd])
    exact isIso_kernelLift_of_mono_of_exact _ _ _ (ShortComplex.exact_of_iso e hex')
  have hcomm2 : (C₀.extend ComplexShape.embeddingUpNat).d 0 1 ≫ eB.symm.hom =
      eA.symm.hom ≫ Z.d 0 1 := (Φ.inv.comm 0 1).symm
  have ha' : ζ ≫ eA.symm.hom = eT.hom ≫ a := by
    have hstep : eT.hom ≫ a ≫ eA.hom = ζ := by
      rw [ha, ← Category.assoc, Iso.hom_inv_id, Category.id_comp, hζ]
    rw [← hstep]
    simp
  exact ⟨comp_eq_zero_of_iso hζd eT eA.symm eB.symm ha' hcomm2,
    isIso_kernelLift_of_iso hζd _ eT eA.symm eB.symm ha' hcomm2 hiso⟩

/-! ### Exactness of the rows and the columns -/

/-- A complex isomorphic to the extension by zero of an `ℕ`-indexed complex `K` is exact away from
degree `0` as soon as `K` is exact in positive degrees. -/
private lemma exactAt_of_iso_extend {X : CochainComplex (ModuleCat.{v} A) ℤ}
    {K : CochainComplex (ModuleCat.{v} A) ℕ} (e : X ≅ K.extend ComplexShape.embeddingUpNat)
    (hK : ∀ k : ℕ, K.ExactAt (k + 1)) (q : ℤ) (hq : q ≠ 0) : X.ExactAt q := by
  refine (HomologicalComplex.exactAt_iff_isZero_homology _ q).2 ?_
  refine (Iso.isZero_iff ((HomologicalComplex.homologyFunctor (ModuleCat.{v} A)
    (ComplexShape.up ℤ) q).mapIso e)).2 ?_
  refine (HomologicalComplex.exactAt_iff_isZero_homology _ q).1 ?_
  rcases lt_trichotomy q 0 with h | h | h
  · exact HomologicalComplex.extend_exactAt _ ComplexShape.embeddingUpNat q
      (fun j => by change ((j : ℕ) : ℤ) ≠ q; omega)
  · exact absurd h hq
  · have hk : ComplexShape.embeddingUpNat.f q.toNat = q := by
      change ((q.toNat : ℕ) : ℤ) = q; omega
    refine (HomologicalComplex.extend_exactAt_iff _ ComplexShape.embeddingUpNat hk).2 ?_
    obtain ⟨k, hk'⟩ : ∃ k : ℕ, q.toNat = k + 1 := ⟨q.toNat - 1, by omega⟩
    rw [hk']
    exact hK k

/-- **The columns of `Hom_A(Pᐧ, Iᐧ)` are exact away from degree `0`.** -/
public lemma exactAt_homBicomplex_X
    {M N : Type (max u v)} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {P : ChainComplex (ModuleCat.{max u v} A) ℕ} {ε : P.X 0 →ₗ[A] M}
    (hP : Module.PureProjectiveResolution.IsPureProjectiveResolution P ε)
    {I : CochainComplex (ModuleCat.{max u v} A) ℕ} {η : N →ₗ[A] I.X 0}
    (hI : Module.PureInjectiveResolution.IsPureInjectiveResolution I η)
    (p q : ℤ) (hq : q ≠ 0) :
    ((Module.homBicomplex P I).X p).ExactAt q := by
  by_cases hp : ∃ n : ℕ, (n : ℤ) = p
  · obtain ⟨n, hn⟩ := hp
    exact Module.exactAt_of_iso_extend (Module.homBicomplexColumnIso P I n hn)
      (Module.homComplexOfChain_exactAt_of_pureInjective (hI.pureInjective n) P ε hP) q hq
  · exact HomologicalComplex.ExactAt.of_isZero
      (Module.isZero_homBicomplex_X_X P I p q (Or.inl (Module.neg_of_not_exists_natCast hp)))

/-- **The rows of `Hom_A(Pᐧ, Iᐧ)` are exact away from degree `0`.** -/
public lemma exactAt_homBicomplex_flip_X
    {M N : Type (max u v)} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {P : ChainComplex (ModuleCat.{max u v} A) ℕ} {ε : P.X 0 →ₗ[A] M}
    (hP : Module.PureProjectiveResolution.IsPureProjectiveResolution P ε)
    {I : CochainComplex (ModuleCat.{max u v} A) ℕ} {η : N →ₗ[A] I.X 0}
    (hI : Module.PureInjectiveResolution.IsPureInjectiveResolution I η)
    (q p : ℤ) (hp : p ≠ 0) :
    ((Module.homBicomplex P I).flip.X q).ExactAt p := by
  by_cases hq : ∃ n : ℕ, (n : ℤ) = q
  · obtain ⟨n, hn⟩ := hq
    exact Module.exactAt_of_iso_extend (Module.homBicomplexRowIso P I n hn)
      (Module.homComplex_exactAt_of_pureProjective (hP.pureProjective n) I η hI) p hp
  · exact HomologicalComplex.ExactAt.of_isZero
      (Module.isZero_homBicomplex_X_X P I p q (Or.inr (Module.neg_of_not_exists_natCast hq)))

/-! ### The row and column identifications agree -/

/-- **The row and the column identification of `Hom_A(Pᐧ, Iᐧ)` agree in each bidegree.** -/
public lemma homBicomplexRowIso_hom_f_comp (P : ChainComplex (ModuleCat.{v} A) ℕ)
    (I : CochainComplex (ModuleCat.{v} A) ℕ) (p q : ℕ) {p' q' : ℤ}
    (hp : ComplexShape.embeddingUpNat.f p = p')
    (hq : ComplexShape.embeddingUpNat.f q = q') :
    (Module.homBicomplexRowIso P I q hq).hom.f p' ≫
        (HomologicalComplex.extendXIso (Module.homComplex (P.X q) I)
          ComplexShape.embeddingUpNat hp).hom =
      ((HomologicalComplex.eval (ModuleCat.{v} A) (ComplexShape.up ℤ) q').mapIso
          (Module.homBicomplexColumnIso P I p hp)).hom ≫
        (HomologicalComplex.extendXIso (Module.homComplexOfChain P (I.X p))
          ComplexShape.embeddingUpNat hq).hom := by
  have key := CategoryTheory.Functor.mapExtendIso_hom_comp_extendFunctor_map_f
    (HomologicalComplex.eval (ModuleCat.{v} A) (ComplexShape.up ℤ) q')
    (Module.homBicomplexInner P I) ComplexShape.embeddingUpNat
    ((NatIso.mapHomologicalComplex
        (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso (ModuleCat.{v} A) hq)
        (ComplexShape.up ℕ)).app (Module.homBicomplexNat P I) ≪≫
      Module.homBicomplexNatRowIso P I q).hom hp
  refine key.trans ?_
  have h2 : ((NatIso.mapHomologicalComplex
        (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso (ModuleCat.{v} A) hq)
        (ComplexShape.up ℕ)).app (Module.homBicomplexNat P I) ≪≫
      Module.homBicomplexNatRowIso P I q).hom.f p =
      (HomologicalComplex.extendXIso (Module.homComplexOfChain P (I.X p))
        ComplexShape.embeddingUpNat hq).hom := by
    simp only [Module.homBicomplexNatRowIso, HomologicalComplex.Hom.isoOfComponents, Iso.refl_hom]
    rfl
  rw [h2]
  rfl

/-- **The `inv` form of `homBicomplexRowIso_hom_f_comp`**: the inverses of the row and the column
identification of `Hom_A(Pᐧ, Iᐧ)` agree in each bidegree. -/
public lemma homBicomplexRowIso_inv_f_comp (P : ChainComplex (ModuleCat.{v} A) ℕ)
    (I : CochainComplex (ModuleCat.{v} A) ℕ) (p q : ℕ) {p' q' : ℤ}
    (hp : ComplexShape.embeddingUpNat.f p = p')
    (hq : ComplexShape.embeddingUpNat.f q = q') :
    (HomologicalComplex.extendXIso (Module.homComplex (P.X q) I)
          ComplexShape.embeddingUpNat hp).inv ≫
        (Module.homBicomplexRowIso P I q hq).inv.f p' =
      (HomologicalComplex.extendXIso (Module.homComplexOfChain P (I.X p))
          ComplexShape.embeddingUpNat hq).inv ≫
        ((HomologicalComplex.eval (ModuleCat.{v} A) (ComplexShape.up ℤ) q').mapIso
          (Module.homBicomplexColumnIso P I p hp)).inv := by
  have h : ((HomologicalComplex.eval (ModuleCat.{v} A) (ComplexShape.up ℤ) p').mapIso
          (Module.homBicomplexRowIso P I q hq)) ≪≫
        HomologicalComplex.extendXIso (Module.homComplex (P.X q) I)
          ComplexShape.embeddingUpNat hp =
      ((HomologicalComplex.eval (ModuleCat.{v} A) (ComplexShape.up ℤ) q').mapIso
          (Module.homBicomplexColumnIso P I p hp)) ≪≫
        HomologicalComplex.extendXIso (Module.homComplexOfChain P (I.X p))
          ComplexShape.embeddingUpNat hq :=
    Iso.ext (Module.homBicomplexRowIso_hom_f_comp P I p q hp hq)
  exact congrArg Iso.inv h

/-! ### The two augmentations -/

/-- **The augmentation of the columns of `Hom_A(Pᐧ, Iᐧ)`**: precomposition with `ε : P₀ → M`
identifies `Hom_A(M, Iᐧ)` with the kernel of the first differential of each column. -/
public noncomputable def homBicomplexAugmentation {M : Type v} [AddCommGroup M] [Module A M]
    (P : ChainComplex (ModuleCat.{v} A) ℕ) (ε : P.X 0 →ₗ[A] M)
    (I : CochainComplex (ModuleCat.{v} A) ℕ) :
    (Module.homComplex M I).extend ComplexShape.embeddingUpNat ⟶
      rowZero (Module.homBicomplex P I) :=
  HomologicalComplex.extendMap (Module.homComplexPrecomp ε I) ComplexShape.embeddingUpNat ≫
    (Module.homBicomplexRowIso P I 0 ComplexShape.embeddingUpNat_f_zero).inv

/-- **The augmentation of the rows of `Hom_A(Pᐧ, Iᐧ)`**: postcomposition with `η : N → I⁰`
identifies `Hom_A(Pᐧ, N)` with the kernel of the first differential of each row. -/
public noncomputable def homBicomplexFlipAugmentation {N : Type v} [AddCommGroup N] [Module A N]
    (P : ChainComplex (ModuleCat.{v} A) ℕ)
    (I : CochainComplex (ModuleCat.{v} A) ℕ) (η : N →ₗ[A] I.X 0) :
    (Module.homComplexOfChain P N).extend ComplexShape.embeddingUpNat ⟶
      rowZero (Module.homBicomplex P I).flip :=
  HomologicalComplex.extendMap (Module.homComplexOfChainPostcomp P η)
      ComplexShape.embeddingUpNat ≫
    (Module.homBicomplexColumnIso P I 0 ComplexShape.embeddingUpNat_f_zero).inv

/-! ### The kernel clauses -/

/-- Any map between zero objects is an isomorphism. -/
private lemma isIso_of_isZero_of_isZero {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    {X Y : C} (hX : IsZero X) (hY : IsZero Y) (f : X ⟶ Y) : IsIso f :=
  ⟨0, hX.eq_of_src _ _, hY.eq_of_src _ _⟩


/-! ### The kernel clauses -/

/-- Exactness of a pair of morphisms of modules from exactness of a different spelling of the
second one. -/
private lemma exact_of_hom_eq {X Y Z : ModuleCat.{v} A} {f : X ⟶ Y} {g : Y ⟶ Z}
    {g' : Y →ₗ[A] Z} (hg : g.hom = g') (h : Function.Exact f.hom g') :
    Function.Exact f.hom g.hom := by
  rw [hg]
  exact h

/-- `(u ≫ v) ≫ c = eK ≫ x ≫ cex` whenever `u = eK ≫ x ≫ r`, `r ≫ v = cex ≫ ci` and
`ci ≫ c = 𝟙 _`. -/
private lemma comp_eq_comp_of_inv_comp {C : Type*} [Category C] {W T R Rz V Cz : C}
    {u : W ⟶ Rz} {eK : W ⟶ T} {x : T ⟶ R} {r : R ⟶ Rz} (h1 : u = eK ≫ x ≫ r)
    {v : Rz ⟶ V} {c : V ⟶ Cz} {cex : R ⟶ Cz} {ci : Cz ⟶ V}
    (h2 : r ≫ v = cex ≫ ci) (h3 : ci ≫ c = 𝟙 Cz) :
    (u ≫ v) ≫ c = eK ≫ x ≫ cex := by
  rw [h1]
  simp only [Category.assoc]
  rw [← Category.assoc r v c, h2, Category.assoc, h3, Category.comp_id]

/-- **The kernel clause of [Stacks, Tag 0133] for the columns of `Hom_A(Pᐧ, Iᐧ)`**:
`Hom_A(M, Iᵖ)` is the kernel of `Hom_A(P₀, Iᵖ) → Hom_A(P₁, Iᵖ)`. -/
public lemma inducesIsoKernel_homBicomplex {M : Type v} [AddCommGroup M] [Module A M]
    (P : ChainComplex (ModuleCat.{v} A) ℕ) (ε : P.X 0 →ₗ[A] M)
    (hε : Function.Surjective ε) (hd : Function.Exact (P.d 1 0) ε)
    (I : CochainComplex (ModuleCat.{v} A) ℕ) (p : ℤ) :
    ∃ hα : (Module.homBicomplexAugmentation P ε I).f p ≫
        ((Module.homBicomplex P I).X p).d 0 1 = 0,
      IsIso (kernel.lift (((Module.homBicomplex P I).X p).d 0 1)
        ((Module.homBicomplexAugmentation P ε I).f p) hα) := by
  by_cases hp : ∃ n : ℕ, (n : ℤ) = p
  · obtain ⟨n, hn⟩ := hp
    have hn' : ComplexShape.embeddingUpNat.f n = p := hn
    have hfex : Function.Exact (LinearMap.lcomp A (I.X n) ε)
        (LinearMap.lcomp A (I.X n) (P.d 1 0).hom) :=
      Module.homComplexOfChain_augmentation_exact (P.d 1 0).hom ε hε hd.linearMap_ker_eq.symm
    exact Module.isIso_kernelLift_of_extendAugmentation
      (Module.homBicomplexColumnIso P I n hn')
      (HomologicalComplex.extendXIso (Module.homComplex M I)
        ComplexShape.embeddingUpNat hn').symm
      (ModuleCat.ofHom (LinearMap.lcomp A (I.X n) ε))
      (LinearMap.lcomp_injective_of_surjective ε hε)
      (Module.exact_of_hom_eq (Module.homComplexOfChain_d P (I.X n) 0) hfex)
      ((Module.homBicomplexAugmentation P ε I).f p)
      (Module.comp_eq_comp_of_inv_comp
        (u := (HomologicalComplex.extendMap (Module.homComplexPrecomp ε I)
          ComplexShape.embeddingUpNat).f p)
        (v := (Module.homBicomplexRowIso P I 0
          ComplexShape.embeddingUpNat_f_zero).inv.f p)
        (HomologicalComplex.extendMap_f (Module.homComplexPrecomp ε I)
          ComplexShape.embeddingUpNat hn')
        (Module.homBicomplexRowIso_inv_f_comp P I n 0 hn'
          ComplexShape.embeddingUpNat_f_zero)
        (Iso.inv_hom_id _))
  · exact Module.exists_isIso_kernelLift_of_isZero _ _
      (HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat p
        (fun n h => hp ⟨n, h⟩))
      (Module.isZero_homBicomplex_X_X P I p 0 (Or.inl (Module.neg_of_not_exists_natCast hp)))
/-- Postcomposition with an injective map is injective on `Hom`s. -/
public theorem compRight_injective_of_injective {N J Q : Type v}
    [AddCommGroup N] [Module A N] [AddCommGroup J] [Module A J] [AddCommGroup Q] [Module A Q]
    (η : N →ₗ[A] J) (hη : Function.Injective η) :
    Function.Injective (LinearMap.compRight A η : (Q →ₗ[A] N) →ₗ[A] (Q →ₗ[A] J)) :=
  fun _ _ h => LinearMap.ext fun x => hη (DFunLike.congr_fun h x)

/-- **The kernel clause of [Stacks, Tag 0133] for the rows of `Hom_A(Pᐧ, Iᐧ)`**:
`Hom_A(P_q, N)` is the kernel of `Hom_A(P_q, I⁰) → Hom_A(P_q, I¹)`. -/
public lemma inducesIsoKernel_homBicomplex_flip {N : Type v} [AddCommGroup N] [Module A N]
    (P : ChainComplex (ModuleCat.{v} A) ℕ) (I : CochainComplex (ModuleCat.{v} A) ℕ)
    (η : N →ₗ[A] I.X 0) (hη : Function.Injective η) (hd : Function.Exact η (I.d 0 1))
    (q : ℤ) :
    ∃ hβ : (Module.homBicomplexFlipAugmentation P I η).f q ≫
        ((Module.homBicomplex P I).flip.X q).d 0 1 = 0,
      IsIso (kernel.lift (((Module.homBicomplex P I).flip.X q).d 0 1)
        ((Module.homBicomplexFlipAugmentation P I η).f q) hβ) := by
  by_cases hq : ∃ n : ℕ, (n : ℤ) = q
  · obtain ⟨n, hn⟩ := hq
    have hn' : ComplexShape.embeddingUpNat.f n = q := hn
    have hfex : Function.Exact
        (LinearMap.compRight A η : (P.X n →ₗ[A] N) →ₗ[A] (P.X n →ₗ[A] I.X 0))
        (LinearMap.compRight A (I.d 0 1).hom) :=
      Module.homComplex_augmentation_exact η (I.d 0 1).hom hη hd.linearMap_ker_eq.symm
    exact Module.isIso_kernelLift_of_extendAugmentation
      (Module.homBicomplexRowIso P I n hn')
      (HomologicalComplex.extendXIso (Module.homComplexOfChain P N)
        ComplexShape.embeddingUpNat hn').symm
      (ModuleCat.ofHom (LinearMap.compRight A η))
      (Module.compRight_injective_of_injective η hη)
      (Module.exact_of_hom_eq (Module.homComplex_d (P.X n) I 0) hfex)
      ((Module.homBicomplexFlipAugmentation P I η).f q)
      (Module.comp_eq_comp_of_inv_comp
        (u := (HomologicalComplex.extendMap (Module.homComplexOfChainPostcomp P η)
          ComplexShape.embeddingUpNat).f q)
        (v := (Module.homBicomplexColumnIso P I 0
          ComplexShape.embeddingUpNat_f_zero).inv.f q)
        (HomologicalComplex.extendMap_f (Module.homComplexOfChainPostcomp P η)
          ComplexShape.embeddingUpNat hn')
        (Module.homBicomplexRowIso_inv_f_comp P I 0 n
          ComplexShape.embeddingUpNat_f_zero hn').symm
        (Iso.inv_hom_id ((HomologicalComplex.eval (ModuleCat.{v} A) (ComplexShape.up ℤ)
          (0 : ℤ)).mapIso (Module.homBicomplexRowIso P I n hn'))))
  · exact Module.exists_isIso_kernelLift_of_isZero _ _
      (HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat q
        (fun n h => hq ⟨n, h⟩))
      (Module.isZero_homBicomplex_X_X P I 0 q (Or.inr (Module.neg_of_not_exists_natCast hq)))

/-! ### The hypotheses of [Stacks, Tag 0133] -/

/-- **`Hom_A(Pᐧ, Iᐧ)` resolves `Hom_A(M, Iᐧ)` column by column.** -/
public lemma hypotheses_homBicomplex
    {M N : Type (max u v)} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {P : ChainComplex (ModuleCat.{max u v} A) ℕ} {ε : P.X 0 →ₗ[A] M}
    (hP : Module.PureProjectiveResolution.IsPureProjectiveResolution P ε)
    {I : CochainComplex (ModuleCat.{max u v} A) ℕ} {η : N →ₗ[A] I.X 0}
    (hI : Module.PureInjectiveResolution.IsPureInjectiveResolution I η) :
    Hypotheses ((Module.homComplex M I).extend ComplexShape.embeddingUpNat)
      (Module.homBicomplex P I) (Module.homBicomplexAugmentation P ε I) where
  diagonalFinite := Module.diagonalFinite_homBicomplex P I
  zero_of_neg p q hq := Module.isZero_homBicomplex_X_X P I p q (Or.inr hq)
  exactAt_of_ne_zero p q hq := Module.exactAt_homBicomplex_X hP hI p q hq
  inducesIsoKernel p := Module.inducesIsoKernel_homBicomplex P ε
    hP.surjective_augmentation hP.exact_zero I p

/-- **`Hom_A(Pᐧ, Iᐧ)` resolves `Hom_A(Pᐧ, N)` row by row.** -/
public lemma hypotheses_homBicomplex_flip
    {M N : Type (max u v)} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {P : ChainComplex (ModuleCat.{max u v} A) ℕ} {ε : P.X 0 →ₗ[A] M}
    (hP : Module.PureProjectiveResolution.IsPureProjectiveResolution P ε)
    {I : CochainComplex (ModuleCat.{max u v} A) ℕ} {η : N →ₗ[A] I.X 0}
    (hI : Module.PureInjectiveResolution.IsPureInjectiveResolution I η) :
    Hypotheses ((Module.homComplexOfChain P N).extend ComplexShape.embeddingUpNat)
      (Module.homBicomplex P I).flip (Module.homBicomplexFlipAugmentation P I η) where
  diagonalFinite := Module.diagonalFinite_homBicomplex_flip P I
  zero_of_neg p q hq := Module.isZero_homBicomplex_X_X P I q p (Or.inl hq)
  exactAt_of_ne_zero p q hq := Module.exactAt_homBicomplex_flip_X hP hI p q hq
  inducesIsoKernel q := Module.inducesIsoKernel_homBicomplex_flip P I η
    hI.injective_augmentation hI.exact_zero q

/-! ### The two computations of the pure extension modules agree -/

/-- **The two computations of `Pext` agree, for given pure resolutions**: the `n`th cohomology
of `Hom_A(M, Iᐧ)` is isomorphic to that of `Hom_A(Pᐧ, N)`, through the total complex of
`Hom_A(Pᐧ, Iᐧ)`. -/
public noncomputable def homologyIsoOfPureResolutions
    {M N : Type (max u v)} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {P : ChainComplex (ModuleCat.{max u v} A) ℕ} {ε : P.X 0 →ₗ[A] M}
    (hP : Module.PureProjectiveResolution.IsPureProjectiveResolution P ε)
    {I : CochainComplex (ModuleCat.{max u v} A) ℕ} {η : N →ₗ[A] I.X 0}
    (hI : Module.PureInjectiveResolution.IsPureInjectiveResolution I η) (n : ℕ) :
    (Module.homComplex M I).homology n ≅ (Module.homComplexOfChain P N).homology n :=
  haveI htot : (Module.homBicomplex P I).HasTotal (ComplexShape.up ℤ) :=
    Module.hasTotal_homBicomplex P I
  have hwit := exists_comparisonMap_q
    ((Module.homComplexOfChain P N).extend ComplexShape.embeddingUpNat)
    (Module.homBicomplex P I) (Module.homBicomplexFlipAugmentation P I η)
    (Module.hypotheses_homBicomplex_flip hP hI) htot
  haveI : QuasiIso hwit.choose := hwit.choose_spec.2
  haveI : IsIso (HomologicalComplex.homologyMap hwit.choose (n : ℤ)) :=
    (quasiIsoAt_iff_isIso_homologyMap hwit.choose (n : ℤ)).1 inferInstance
  ((Module.homComplex M I).extendHomologyIso ComplexShape.embeddingUpNat
      (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ))).symm ≪≫
    comparisonHomologyIso ((Module.homComplex M I).extend ComplexShape.embeddingUpNat)
        (Module.homBicomplex P I) (Module.homBicomplexAugmentation P ε I)
        (Module.hypotheses_homBicomplex hP hI) (n : ℤ) ≪≫
      (asIso (HomologicalComplex.homologyMap hwit.choose (n : ℤ))).symm ≪≫
        (Module.homComplexOfChain P N).extendHomologyIso ComplexShape.embeddingUpNat
          (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ))

/-- **Pure extensions are computed by a pure projective resolution of the first variable**:
`Pext^i_A(M, N)` is the `i`th cohomology module of `Hom_A(Pᐧ, N)` for every pure projective
resolution `Pᐧ ⟶ M`. -/
@[stacks 0706 "pure_projective_resolution"]
public noncomputable def pureExtIsoHomologyOfPureProjectiveResolution
    (M N : Type (max u v)) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {P : ChainComplex (ModuleCat.{max u v} A) ℕ} {ε : P.X 0 →ₗ[A] M}
    (hP : Module.PureProjectiveResolution.IsPureProjectiveResolution P ε) (i : ℕ) :
    Module.pureExt (A := A) M N i ≅ (Module.homComplexOfChain P N).homology i :=
  let hExists := Module.PureInjectiveResolution.exists_pureInjectiveResolution A N
  let I := Classical.choose hExists
  let hAugExists : ∃ augmentation : N →ₗ[A] I.X 0,
      Module.PureInjectiveResolution.IsPureInjectiveResolution I augmentation :=
    Classical.choose_spec hExists
  Module.homologyIsoOfPureResolutions hP (Classical.choose_spec hAugExists) i

/-- **Pure extensions are computed by every pure injective resolution of the second variable**:
`Pext^i_A(M, N)` is the `i`th cohomology module of `Hom_A(M, Iᐧ)` for every pure injective
resolution `N ⟶ Iᐧ`, not only for the one chosen in the definition of `Module.pureExt`. -/
public noncomputable def pureExtIsoHomologyOfPureInjectiveResolution
    (M N : Type (max u v)) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {I : CochainComplex (ModuleCat.{max u v} A) ℕ} {η : N →ₗ[A] I.X 0}
    (hI : Module.PureInjectiveResolution.IsPureInjectiveResolution I η) (i : ℕ) :
    Module.pureExt (A := A) M N i ≅ (Module.homComplex M I).homology i :=
  let hExists := Module.PureProjectiveResolution.exists_isPureProjectiveResolution A M
  let hP := Classical.choose_spec (Classical.choose_spec hExists)
  Module.pureExtIsoHomologyOfPureProjectiveResolution M N hP i ≪≫
    (Module.homologyIsoOfPureResolutions hP hI i).symm

/-! ### Degree zero -/

/-- The degree-zero cochain of `Hom_A(M, Iᐧ)` attached to a homomorphism `M → N`: its
composite with the augmentation `η : N → I⁰`. -/
public noncomputable def homComplexZeroCochain (M : Type v) [AddCommGroup M] [Module A M]
    {N : Type v} [AddCommGroup N] [Module A N]
    {I : CochainComplex (ModuleCat.{v} A) ℕ} (η : N →ₗ[A] I.X 0) :
    ModuleCat.of A (M →ₗ[A] N) ⟶ (Module.homComplex M I).X 0 :=
  ModuleCat.ofHom (LinearMap.compRight A η)

/-- Composing with the augmentation of a resolution lands in the degree-zero cocycles of
`Hom_A(M, Iᐧ)`. -/
public lemma homComplexZeroCochain_comp_d (M : Type v) [AddCommGroup M] [Module A M]
    {N : Type v} [AddCommGroup N] [Module A N]
    {I : CochainComplex (ModuleCat.{v} A) ℕ} (η : N →ₗ[A] I.X 0)
    (hη : (I.d 0 1).hom.comp η = 0) :
    Module.homComplexZeroCochain M η ≫ (Module.homComplex M I).d 0 1 = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun f => ?_)
  show ((Module.homComplex M I).d 0 1).hom (LinearMap.compRight A η f) = 0
  rw [show ((Module.homComplex M I).d 0 1).hom
      = LinearMap.compRight A (I.d 0 1).hom from by simpa using Module.homComplex_d M I 0]
  exact LinearMap.ext fun x => congr($hη (f x))

/-- **The canonical map `Hom_A(M, N) ⟶ H⁰(Hom_A(M, Iᐧ))`** attached to an augmentation
`η : N → I⁰` killed by the first differential: a homomorphism `M → N` composed with `η` is a
degree-zero cocycle, and this is its cohomology class. -/
public noncomputable def homComplexZeroHom (M : Type v) [AddCommGroup M] [Module A M]
    {N : Type v} [AddCommGroup N] [Module A N]
    {I : CochainComplex (ModuleCat.{v} A) ℕ} (η : N →ₗ[A] I.X 0)
    (hη : (I.d 0 1).hom.comp η = 0) :
    ModuleCat.of A (M →ₗ[A] N) ⟶ (Module.homComplex M I).homology 0 :=
  (Module.homComplex M I).liftCycles (Module.homComplexZeroCochain M η) 1 (by simp)
      (Module.homComplexZeroCochain_comp_d M η hη) ≫
    (Module.homComplex M I).homologyπ 0

/-- Postcomposition with a map of complexes `F : Iᐧ ⟶ Jᐧ`, as a map of Hom complexes
`Hom_A(M, Iᐧ) ⟶ Hom_A(M, Jᐧ)`. -/
public noncomputable def homComplexPostcomp (M : Type v) [AddCommGroup M] [Module A M]
    {I J : CochainComplex (ModuleCat.{v} A) ℕ} (F : I ⟶ J) :
    Module.homComplex M I ⟶ Module.homComplex M J where
  f n := ModuleCat.ofHom (LinearMap.compRight A (F.f n).hom)
  comm' n n' h := by
    obtain rfl : n + 1 = n' := h
    have hc := congrArg ModuleCat.Hom.hom (F.comm n (n + 1))
    simp only [ModuleCat.hom_comp] at hc
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun ψ : M →ₗ[A] I.X n => ?_
    change ((Module.homComplex M J).d n (n + 1)).hom
        (LinearMap.compRight A (F.f n).hom ψ) =
      LinearMap.compRight A (F.f (n + 1)).hom
        (((Module.homComplex M I).d n (n + 1)).hom ψ)
    rw [Module.homComplex_d, Module.homComplex_d]
    exact LinearMap.ext fun x => congr($hc (ψ x))

/-- The class of a degree-zero cocycle is natural: if `F : K ⟶ L` carries `a` to `u ≫ b`, then the
cohomology classes of `a` and `b` are related by `F` and `u`. -/
private lemma liftCycles_homologyπ_homologyMap {K L : CochainComplex (ModuleCat.{v} A) ℕ}
    (F : K ⟶ L) {T T' : ModuleCat.{v} A} (a : T ⟶ K.X 0) (b : T' ⟶ L.X 0) (u : T ⟶ T')
    (ha : a ≫ K.d 0 1 = 0) (hb : b ≫ L.d 0 1 = 0) (h : a ≫ F.f 0 = u ≫ b) :
    (K.liftCycles a 1 (by simp) ha ≫ K.homologyπ 0) ≫ HomologicalComplex.homologyMap F 0 =
      u ≫ L.liftCycles b 1 (by simp) hb ≫ L.homologyπ 0 := by
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap, ← Category.assoc]
  congr 1
  rw [← cancel_mono (L.iCycles 0), HomologicalComplex.liftCycles_i, Category.assoc,
    HomologicalComplex.liftCycles_i, h]

/-- **The canonical degree-zero map is natural in the first variable**: precomposition with
`f : Q → M` on homomorphisms corresponds to the map of Hom complexes that `f` induces. -/
public lemma homComplexZeroHom_naturality_left
    {M Q : Type v} [AddCommGroup M] [Module A M] [AddCommGroup Q] [Module A Q]
    (f : Q →ₗ[A] M) {N : Type v} [AddCommGroup N] [Module A N]
    {I : CochainComplex (ModuleCat.{v} A) ℕ} (η : N →ₗ[A] I.X 0)
    (hη : (I.d 0 1).hom.comp η = 0) :
    Module.homComplexZeroHom M η hη ≫
        HomologicalComplex.homologyMap (Module.homComplexPrecomp f I) 0 =
      ModuleCat.ofHom (LinearMap.lcomp A N f) ≫ Module.homComplexZeroHom Q η hη := by
  exact Module.liftCycles_homologyπ_homologyMap _ _ _ _ _ _
    (ModuleCat.hom_ext (LinearMap.ext fun c => rfl))

/-- **The canonical degree-zero map is natural in the second variable**: postcomposition with
`g : N → N'` on homomorphisms corresponds to the map of Hom complexes induced by any comparison
map `F : Iᐧ ⟶ Jᐧ` of resolutions lying over `g`. -/
public lemma homComplexZeroHom_naturality_right
    (M : Type v) [AddCommGroup M] [Module A M]
    {N N' : Type v} [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
    {I J : CochainComplex (ModuleCat.{v} A) ℕ}
    (η : N →ₗ[A] I.X 0) (hη : (I.d 0 1).hom.comp η = 0)
    (η' : N' →ₗ[A] J.X 0) (hη' : (J.d 0 1).hom.comp η' = 0)
    (g : N →ₗ[A] N') (F : I ⟶ J) (hF : (F.f 0).hom.comp η = η'.comp g) :
    Module.homComplexZeroHom M η hη ≫
        HomologicalComplex.homologyMap (Module.homComplexPostcomp M F) 0 =
      ModuleCat.ofHom (LinearMap.compRight A g) ≫ Module.homComplexZeroHom M η' hη' := by
  exact Module.liftCycles_homologyπ_homologyMap _ _ _ _ _ _
    (ModuleCat.hom_ext (LinearMap.ext fun c => LinearMap.ext fun x => congr($hF (c x))))

/-- **The canonical degree-zero map of a pure injective resolution is an isomorphism.** -/
public theorem isIso_homComplexZeroHom
    (M : Type v) [AddCommGroup M] [Module A M] {N : Type v} [AddCommGroup N] [Module A N]
    {I : CochainComplex (ModuleCat.{v} A) ℕ} {η : N →ₗ[A] I.X 0}
    (hI : Module.PureInjectiveResolution.IsPureInjectiveResolution I η) :
    IsIso (Module.homComplexZeroHom M η hI.exact_zero.linearMap_comp_eq_zero) := by
  have hd : ((Module.homComplex M I).d 0 1).hom =
      LinearMap.compRight A (I.d 0 1).hom := by
    simpa using Module.homComplex_d M I 0
  dsimp only [Module.homComplexZeroHom]
  have : IsIso ((Module.homComplex M I).liftCycles (Module.homComplexZeroCochain M η) 1
      (by simp) (Module.homComplexZeroCochain_comp_d M η
        hI.exact_zero.linearMap_comp_eq_zero)) := by
    rw [CochainComplex.isIso_liftCycles_iff]
    refine ⟨?_, ?_⟩
    · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
      show LinearMap.range (LinearMap.compRight A η)
        = LinearMap.ker ((Module.homComplex M I).d 0 1).hom
      rw [hd]
      exact (Module.homComplex_augmentation_exact η (I.d 0 1).hom hI.injective_augmentation
        hI.exact_zero.linearMap_ker_eq.symm).linearMap_ker_eq.symm
    · rw [ModuleCat.mono_iff_injective]
      exact Module.compRight_injective_of_injective η hI.injective_augmentation
  infer_instance

/-- **The degree-zero cohomology of `Hom_A(M, Iᐧ)` is `Hom_A(M, N)`**, for a pure injective
resolution `N ⟶ Iᐧ`. -/
public noncomputable def homComplexHomologyZeroIso
    (M : Type v) [AddCommGroup M] [Module A M] {N : Type v} [AddCommGroup N] [Module A N]
    {I : CochainComplex (ModuleCat.{v} A) ℕ} {η : N →ₗ[A] I.X 0}
    (hI : Module.PureInjectiveResolution.IsPureInjectiveResolution I η) :
    ModuleCat.of A (M →ₗ[A] N) ≅ (Module.homComplex M I).homology 0 :=
  haveI := Module.isIso_homComplexZeroHom M hI
  asIso (Module.homComplexZeroHom M η hI.exact_zero.linearMap_comp_eq_zero)

/-- **Degree-zero pure extensions are homomorphisms**: `Pext⁰_A(M, N) = Hom_A(M, N)`.  The
inverse sends a homomorphism to its composite with the augmentation of the pure injective
resolution of `N` chosen in the definition of `Module.pureExt`. -/
public noncomputable def pureExtZeroIsoHom (M N : Type v) [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] :
    Module.pureExt (A := A) M N 0 ≅ ModuleCat.of A (M →ₗ[A] N) :=
  (Module.homComplexHomologyZeroIso M (Classical.choose_spec (Classical.choose_spec
    (Module.PureInjectiveResolution.exists_pureInjectiveResolution A N)))).symm

end

end Module

end
