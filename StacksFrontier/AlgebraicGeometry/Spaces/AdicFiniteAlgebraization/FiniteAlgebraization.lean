module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.FiniteTowerEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.ClosedAlgebraization

/-!
# Algebraization of a finite tower over the adic fibres

Stacks 0A01: over a Noetherian ring `A` complete along `I`, a tower of finite morphisms over the
adic fibres of a separated morphism of finite type `X ⟶ Spec A`, with cartesian squares and
proper first term, is the system of adic fibres of a finite `Y ⟶ X`, and `Y` is proper over
`Spec A`.

## Main results

* `AlgebraicGeometry.Space.exists_isFinite_adicFibre_iso_of_tower`: such a tower is the system of
  adic fibres of a finite `Y ⟶ X` with `Y` proper over `Spec A`.

## References

* [Stacks Project, Tag 0A01](https://stacks.math.columbia.edu/tag/0A01)
* [Stacks Project, Tag 08BG](https://stacks.math.columbia.edu/tag/08BG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (A : Type u) [CommRing A] (I : Ideal A) (B : BigFppfSite.{u})
  (hA : B.Contains (Spec (.of A)))

/-- The adic fibre of a monomorphism over the base is a monomorphism. -/
theorem mono_adicFibreMap_of_mono {F G : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
    {fF : F ⟶ yoneda.obj (baseObject A B hA)} {fG : G ⟶ yoneda.obj (baseObject A B hA)}
    (g : F ⟶ G) [Mono g] (hg : g ≫ fG = fF) (n : ℕ) :
    Mono (adicFibreMap A I B hA (contains_adicThickening A I B hA) g hg n) := by
  refine ⟨fun a b h => pullback.hom_ext ((cancel_mono g).1 ?_) ?_⟩
  · simpa using congrArg (· ≫ pullback.fst _ _) h
  · simpa using congrArg (· ≫ pullback.snd _ _) h

variable [IsNoetherianRing A] {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
  (hX : IsAlgebraicSpace B (Spec (.of A)) hA X) (f : X ⟶ yoneda.obj (baseObject A B hA))

/-- **Algebraization of a finite tower over the adic fibres.**  Let `A` be a Noetherian ring
complete along `I`, `S = Spec A`, and `f : X ⟶ S` a separated morphism of finite type of algebraic
spaces with adic fibres `X_n = X ×_S S_n`.  Let `y_n : Y_n ⟶ X_n` be algebraic spaces over the
adic fibres with transitions `t_n : Y_n ⟶ Y_{n + 1}` making cartesian squares over the transitions
`X_n ⟶ X_{n + 1}`, with `Y_0 ⟶ X_0` finite and `Y_0 ⟶ S_0` proper.  Then there is a finite
`π : Y ⟶ X` with `Y` proper over `S`, and isomorphisms `Y_n ≅ Y ×_S S_n` lying over `X_n`,
compatible with the transitions, and exhibiting `Y_n` as `Y ×_X X_n`.

The tower is indexed from `0`: `S_n` is `Spec (A / I ^ (n + 1))`, so the `n`-th term here is the
`(n + 1)`-st term `Y_{n + 1}` of Stacks, and `Y_0 ⟶ X_0`, `Y_0 ⟶ S_0` are Stacks' `Y_1 ⟶ X_1`,
`Y_1 ⟶ S_1`. -/
@[stacks 0A01]
theorem exists_isFinite_adicFibre_iso_of_tower [IsAdicComplete I A]
    (hsep : IsSeparated B (Spec (.of A)) hA f) (hft : IsFiniteType B (Spec (.of A)) hA f)
    (Y : ℕ → AlgebraicSpaces B (Spec (.of A)) hA) (y : ∀ n, Y n ⟶ adicFibreSpace A I B hA hX f n)
    (tY : ∀ n, Y n ⟶ Y (n + 1))
    (hcart : ∀ n, IsPullback (tY n) (y n) (y (n + 1)) (adicFibreSuccHom A I B hA hX f n))
    (hfin0 : IsFinite B (Spec (.of A)) hA (y 0).hom)
    (hprop : IsProper B (Spec (.of A)) hA ((y 0).hom ≫ adicFibreSnd A I B hA f 0)) :
    ∃ (Z : AlgebraicSpaces B (Spec (.of A)) hA) (π : Z ⟶ ⟨X, hX⟩),
      IsFinite B (Spec (.of A)) hA π.hom ∧ IsProper B (Spec (.of A)) hA (π.hom ≫ f) ∧
      ∃ e : ∀ n, Y n ≅ adicFibreSpace A I B hA Z.2 (π.hom ≫ f) n,
        (∀ n, (e n).hom.hom ≫
          adicFibreMap A I B hA (contains_adicThickening A I B hA) π.hom rfl n = (y n).hom) ∧
        (∀ n, tY n ≫ (e (n + 1)).hom =
          (e n).hom ≫ adicFibreSuccHom A I B hA Z.2 (π.hom ≫ f) n) ∧
        (∀ n, IsPullback ((e n).hom ≫ adicFibreFst A I B hA Z.2 (π.hom ≫ f) n) (y n) π
          (adicFibreFstHom A I B hA hX f n)) := by
  obtain ⟨P, p, hpaff, hpfp, g, hg, hgcl, hgcomp⟩ :=
    exists_isClosedImmersion_tower_of_isFinite A I B hA hX f hsep hft Y y tY hcart hfin0 hprop
  obtain ⟨c, hccl, hccart, hcy⟩ := exists_adicFibre_isClosedImmersion_of_comp_eq A I B hA hX f
    (y := y) (tY := tY) (hcart := hcart) (p := p) (g := g) (hg := hg) (hgcl := hgcl)
    (hcomp := hgcomp)
  have hpsep : IsSeparated B (Spec (.of A)) hA p.hom :=
    isSeparated_of_isAffineHom B (Spec (.of A)) hA p.hom P.2 hX hpaff
  have hPsep : IsSeparated B (Spec (.of A)) hA (p.hom ≫ f) :=
    isSeparated_comp B (Spec (.of A)) hA p.hom f hpsep hsep
  have hPft : IsFiniteType B (Spec (.of A)) hA (p.hom ≫ f) :=
    isFiniteType_comp' B (Spec (.of A)) hA p.hom f hX (isAlgebraicSpace_yoneda B _ hA _)
      (isFiniteType_of_isFinitePresentation B (Spec (.of A)) hA hpfp) hft
  have hproper :
      IsProper B (Spec (.of A)) hA ((c 0).hom ≫ adicFibreSnd A I B hA (p.hom ≫ f) 0) := by
    rwa [← hcy 0, Category.assoc, adicFibreMap_snd] at hprop
  obtain ⟨Z, j, hjcl, hjprop, e, he⟩ := exists_closedSubspace_algebraization_of_existence A I B hA
    P.2 (p.hom ≫ f) hPsep hPft (existenceEssSurj_holds A I B hA P.2 (p.hom ≫ f) hPsep hPft)
    (existenceFullyFaithful_holds A I B hA P.2 (p.hom ≫ f) hPsep hPft) Y c tY hccart hccl hproper
  have hjmono : Mono j.hom := mono_of_isClosedImmersion B (Spec (.of A)) hA _ hjcl
  have hπaff : IsAffineHom B (Spec (.of A)) hA (j ≫ p).hom :=
    isAffineHom_comp B (Spec (.of A)) hA j.hom p.hom
      (isAffineHom_of_isClosedImmersion B (Spec (.of A)) hA _ hjcl) hpaff
  have hπprop : IsProper B (Spec (.of A)) hA ((j ≫ p).hom ≫ f) := by
    rwa [ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
  have hπfin : IsFinite B (Spec (.of A)) hA (j ≫ p).hom :=
    (isFinite_iff_isAffineHom_and_isProper B (Spec (.of A)) hA Z.2 hX _).2 ⟨hπaff,
      isProper_of_comp_of_isSeparated B (Spec (.of A)) hA Z.2 hX (isAlgebraicSpace_yoneda B _ hA _)
        _ f hπprop hsep⟩
  have ha : ∀ n, (e n).hom.hom ≫
      adicFibreMap A I B hA (contains_adicThickening A I B hA) (j ≫ p).hom rfl n = (y n).hom := by
    intro n
    refine (congrArg _ (adicFibreMap_comp A I B hA (contains_adicThickening A I B hA)
      (fG := p.hom ≫ f) (fH := f) j.hom rfl p.hom rfl n)).trans ?_
    rw [← Category.assoc, he n, hcy n]
  refine ⟨Z, j ≫ p, hπfin, hπprop, e, ha, fun n => ?_, fun n => ?_⟩
  · apply ObjectProperty.hom_ext
    have := mono_adicFibreMap_of_mono A I B hA j.hom (fG := p.hom ≫ f) rfl (n + 1)
    refine (cancel_mono (adicFibreMap A I B hA (contains_adicThickening A I B hA)
      (fG := p.hom ≫ f) j.hom rfl (n + 1))).1 ?_
    simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc, he]
    have hw := congrArg (·.hom) (hccart n).w
    simp only [ObjectProperty.FullSubcategory.comp_hom] at hw
    rw [hw, ← he n, Category.assoc]
    exact congrArg _ (adicFibreSucc_adicFibreMap A I B hA (contains_adicThickening A I B hA)
      j.hom rfl n).symm
  · have h0 := isPullback_adicFibreMap_adicFibreFst A I B hA (P := ⟨X, hX⟩) f (j ≫ p) n
    have h1 : IsPullback (adicFibreFst A I B hA Z.2 ((j ≫ p).hom ≫ f) n)
        (ObjectProperty.homMk (adicFibreMap A I B hA (contains_adicThickening A I B hA)
          (j ≫ p).hom rfl n) :
          adicFibreSpace A I B hA Z.2 ((j ≫ p).hom ≫ f) n ⟶ adicFibreSpace A I B hA hX f n)
        (j ≫ p) (adicFibreFstHom A I B hA hX f n) :=
      IsPullback.of_map_of_faithful
        (F := ObjectProperty.ι
          (fun F : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u =>
            IsAlgebraicSpace B (Spec (.of A)) hA F)) h0
    simpa only [Category.id_comp] using
      (IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact ObjectProperty.hom_ext _ (ha n)⟩ :
        IsPullback (e n).hom (y n) _ (𝟙 _)).paste_horiz h1

end AlgebraicGeometry.Space

end
