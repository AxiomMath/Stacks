module

public import StacksFrontier.RingTheory.Flat.HenselianFlattening

/-!
# Approximating a flattening ideal by a finitely generated one

An ideal `I` of `R` is the filtered union of its finitely generated subideals, so `R ⧸ I` is the
filtered colimit of the `R`-algebras `R ⧸ K` with `K ⊆ I` finitely generated. When `R → S` is
essentially of finite presentation and `M` is a finitely presented `S`-module, the flatness
condition of Stacks Tag 05LQ is limit preserving (Stacks Tag 05LT, available as
`Module.exists_isFlatAtPrimesOver_of_isColimit`), so if it holds over `R ⧸ I` it already holds
over `R ⧸ K` for some finitely generated `K ⊆ I`.

For the local flattening problem of Stacks Tag 05MK this says that a flattening ideal contains a
finitely generated flattening ideal, which is `Module.FlatAtPointSituation.FlattensFGApprox`.

## Main definitions

* `Ideal.quotientDiagram` is the diagram of quotients of `R` attached to a monotone family of
  ideals, and `Ideal.quotientCocone` its cocone over the quotient by a larger ideal.

## Main results

* `Ideal.isColimitQuotientCocone` and `Ideal.isColimitForgetQuotientCocone`: the cocone is a
  colimit in `CommAlgCat R` and remains one after passing to types, as soon as the family is
  directed and exhausts the larger ideal; hence
  `Ideal.preservesColimit_forget_quotientDiagram`.
* `Module.exists_fg_isFlatAtPrimesOver`: the condition of Stacks Tag 05LQ over `R ⧸ I` descends to
  `R ⧸ K` for some finitely generated `K ⊆ I`.
* `Module.FlatAtPointSituation.flattensFGApprox`: `Module.FlatAtPointSituation.FlattensFGApprox`
  holds when `A → B` is essentially of finite presentation and `M` is finitely presented.
* `Module.FlatAtPointSituation.exists_fg_ideal_conditionOn_iff_map_eq_bot_of_essFP`: the
  finite-generation part of Stacks Tag 05PG, under `FlattensSInf` and `FlattensKer`.

## References

* [Stacks Project, Tag 05LT](https://stacks.math.columbia.edu/tag/05LT)
* [Stacks Project, Tag 05MN](https://stacks.math.columbia.edu/tag/05MN)
* [Stacks Project, Tag 05PG](https://stacks.math.columbia.edu/tag/05PG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v w x y

namespace Ideal

variable {A : Type u} [CommRing A]

/-- There is at most one `A`-algebra homomorphism out of a quotient of `A`. -/
theorem algHom_quotient_eq {K : Ideal A} {T : Type v} [CommRing T] [Algebra A T]
    (f g : (A ⧸ K) →ₐ[A] T) : f = g := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact (f.commutes a).trans (g.commutes a).symm

variable {Λ : Type y} [Preorder Λ] (K : Λ → Ideal A) (hK : Monotone K)

/-- The diagram of commutative `A`-algebras `l ↦ A ⧸ K l` attached to a monotone family of
ideals of `A`. -/
def quotientDiagram : Λ ⥤ CommAlgCat.{u} A where
  obj l := CommAlgCat.of A (A ⧸ K l)
  map {_ _} f := CommAlgCat.ofHom (Ideal.Quotient.factorₐ A (hK (leOfHom f)))
  map_id _ := CommAlgCat.hom_ext (algHom_quotient_eq _ _)
  map_comp _ _ := CommAlgCat.hom_ext (algHom_quotient_eq _ _)

variable (I : Ideal A) (hle : ∀ l, K l ≤ I)

/-- The cocone on `Ideal.quotientDiagram` with apex `A ⧸ I`, for an ideal `I` containing every
member of the family. -/
def quotientCocone : Cocone (quotientDiagram K hK) where
  pt := CommAlgCat.of A (A ⧸ I)
  ι :=
    { app := fun l ↦ CommAlgCat.ofHom (Ideal.Quotient.factorₐ A (hle l))
      naturality := fun _ _ _ ↦ CommAlgCat.hom_ext (algHom_quotient_eq _ _) }

/-- If the family exhausts `I`, then `A ⧸ I` is the colimit of the `A ⧸ K l` in the category of
commutative `A`-algebras. -/
def isColimitQuotientCocone [Nonempty Λ] (hsup : ∀ a ∈ I, ∃ l, a ∈ K l) :
    IsColimit (quotientCocone K hK I hle) where
  desc s := CommAlgCat.ofHom (Ideal.Quotient.liftₐ I (Algebra.ofId A s.pt) (by
    intro a ha
    obtain ⟨l, hl⟩ := hsup a ha
    have hz : (algebraMap A (((quotientDiagram K hK).obj l : Type u))) a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hl
    have h := (s.ι.app l).hom.commutes a
    rw [hz, map_zero] at h
    exact h.symm))
  fac _ _ := CommAlgCat.hom_ext (algHom_quotient_eq _ _)
  uniq _ _ _ := CommAlgCat.hom_ext (algHom_quotient_eq _ _)

include hle in
/-- For a directed family exhausting `I`, the image of `Ideal.quotientCocone` under the
forgetful functor to types is a colimit cocone. -/
noncomputable def isColimitForgetQuotientCocone [Nonempty Λ] [IsDirectedOrder Λ]
    (hsup : ∀ a ∈ I, ∃ l, a ∈ K l) :
    IsColimit ((forget (CommAlgCat.{u} A)).mapCocone (quotientCocone K hK I hle)) := by
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Classical.arbitrary Λ, Ideal.Quotient.mk _ a, rfl⟩
  · intro l x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hab : a - b ∈ I := by
      have h : Ideal.Quotient.mk I a = Ideal.Quotient.mk I b := hxy
      rwa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at h
    obtain ⟨n, hn⟩ := hsup _ hab
    obtain ⟨m, hlm, hnm⟩ := exists_ge_ge l n
    refine ⟨m, homOfLE hlm, ?_⟩
    change Ideal.Quotient.mk (K m) a = Ideal.Quotient.mk (K m) b
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact hK hnm hn

include hle in
/-- The forgetful functor to types preserves the colimits of `Ideal.quotientDiagram` for a
directed family exhausting an ideal. -/
theorem preservesColimit_forget_quotientDiagram [Nonempty Λ] [IsDirectedOrder Λ]
    (hsup : ∀ a ∈ I, ∃ l, a ∈ K l) :
    PreservesColimit (quotientDiagram K hK) (forget (CommAlgCat.{u} A)) :=
  preservesColimit_of_preserves_colimit_cocone (isColimitQuotientCocone K hK I hle hsup)
    (isColimitForgetQuotientCocone K hK I hle hsup)

/-- Extending an ideal to `A ⧸ K` and then pushing forward to `A ⧸ L` is extending it to
`A ⧸ L`. -/
theorem map_factor_map_quotient_mk {K L : Ideal A} (h : K ≤ L) (I₀ : Ideal A) :
    Ideal.map (Ideal.Quotient.factor h) (Ideal.map (Ideal.Quotient.mk K) I₀) =
      Ideal.map (Ideal.Quotient.mk L) I₀ := by
  rw [Ideal.map_map]
  exact congrArg (Ideal.map · I₀) (RingHom.ext fun _ ↦ rfl)

end Ideal

namespace Module

/-- **Stacks Project, Tag 05LT for a quotient of the base.** Let `R → S` be essentially of finite
presentation and let `M` be a finitely presented `S`-module. If the flatness condition of
Stacks Tag 05LQ holds over `R ⧸ I` for the extension of an ideal `I₀ ⊆ R`, then it already holds
over `R ⧸ K` for some finitely generated `K ⊆ I`. -/
theorem exists_fg_isFlatAtPrimesOver {R : Type u} {Sr : Type v} {M : Type w} [CommRing R]
    [CommRing Sr] [Algebra R Sr] [AddCommGroup M] [Module R M] [Module Sr M]
    [IsScalarTower R Sr M] [Module.FinitePresentation Sr M] (J : Ideal Sr)
    (hS : (algebraMap R Sr).EssentiallyOfFinitePresentation) (I₀ I : Ideal R)
    (hflat : Module.IsFlatAtPrimesOver (R := R) (S := Sr) (M := M) J (R ⧸ I)
      (I₀.map (Ideal.Quotient.mk I))) :
    ∃ K ≤ I, K.FG ∧ Module.IsFlatAtPrimesOver (R := R) (S := Sr) (M := M) J (R ⧸ K)
      (I₀.map (Ideal.Quotient.mk K)) := by
  have : Nonempty {L : Ideal R // L ≤ I ∧ L.FG} := ⟨⟨⊥, bot_le, Submodule.fg_bot⟩⟩
  have : IsDirectedOrder {L : Ideal R // L ≤ I ∧ L.FG} :=
    ⟨fun x y ↦ ⟨⟨x.1 ⊔ y.1, sup_le x.2.1 y.2.1, Submodule.FG.sup x.2.2 y.2.2⟩,
      (le_sup_left : x.1 ≤ x.1 ⊔ y.1), (le_sup_right : y.1 ≤ x.1 ⊔ y.1)⟩⟩
  have hK : Monotone (fun l : {L : Ideal R // L ≤ I ∧ L.FG} ↦ l.1) := fun _ _ h ↦ h
  have hle : ∀ l : {L : Ideal R // L ≤ I ∧ L.FG}, l.1 ≤ I := fun l ↦ l.2.1
  have hsup : ∀ a ∈ I, ∃ l : {L : Ideal R // L ≤ I ∧ L.FG}, a ∈ l.1 := fun a ha ↦
    ⟨⟨Ideal.span {a}, (Ideal.span_singleton_le_iff_mem I).mpr ha, Submodule.fg_span_singleton a⟩,
      Ideal.mem_span_singleton_self a⟩
  have := Ideal.preservesColimit_forget_quotientDiagram
    (fun l : {L : Ideal R // L ≤ I ∧ L.FG} ↦ l.1) hK I hle hsup
  have hsupeq : ((⨆ l : {L : Ideal R // L ≤ I ∧ L.FG},
      Ideal.map (Ideal.Quotient.factor (hle l)) (I₀.map (Ideal.Quotient.mk l.1))) :
        Ideal (R ⧸ I)) = I₀.map (Ideal.Quotient.mk I) :=
    le_antisymm (iSup_le fun l ↦ le_of_eq (Ideal.map_factor_map_quotient_mk (hle l) I₀))
      (le_iSup_of_le ⟨⊥, bot_le, Submodule.fg_bot⟩
        (le_of_eq (Ideal.map_factor_map_quotient_mk (hle _) I₀).symm))
  obtain ⟨l, hl⟩ := Module.exists_isFlatAtPrimesOver_of_isColimit (R := R) (S := Sr) (M := M) J hS
    (Ideal.quotientDiagram (fun l : {L : Ideal R // L ≤ I ∧ L.FG} ↦ l.1) hK)
    (Ideal.quotientCocone _ hK I hle)
    (Ideal.isColimitQuotientCocone _ hK I hle hsup)
    (fun l ↦ I₀.map (Ideal.Quotient.mk l.1)) (fun {_ _} f ↦
      le_of_eq (Ideal.map_factor_map_quotient_mk (hK (leOfHom f)) I₀)) (hsupeq ▸ hflat)
  exact ⟨l.1, l.2.1, l.2.2, hl⟩

namespace FlatAtPointSituation

/-- **Flattening ideals contain finitely generated ones.** If `A → B` is essentially of finite
presentation and `M` is a finitely presented `B`-module, every flattening ideal contains a
finitely generated flattening ideal. -/
theorem flattensFGApprox (S : FlatAtPointSituation.{u, v, w})
    (hS : (algebraMap S.A S.B).EssentiallyOfFinitePresentation)
    [Module.FinitePresentation S.B S.M] : S.FlattensFGApprox :=
  fun I hI ↦ Module.exists_fg_isFlatAtPrimesOver (maximalIdeal S.B) hS (maximalIdeal S.A) I hI

/-- **Stacks Project, Tag 05PG**, finite generation. Under `FlattensSInf` and `FlattensKer`, if
`A → B` is essentially of finite presentation and `M` is finitely presented, there is a finitely
generated ideal `I ⊆ A` such that a local `A`-algebra `R` satisfies the condition exactly when
`I R = 0`. -/
theorem exists_fg_ideal_conditionOn_iff_map_eq_bot_of_essFP (S : FlatAtPointSituation.{u, v, w})
    (h₁ : S.FlattensSInf) (h₂ : S.FlattensKer.{u, v, w, x})
    (hS : (algebraMap S.A S.B).EssentiallyOfFinitePresentation)
    [Module.FinitePresentation S.B S.M] :
    ∃ I : Ideal S.A, I.FG ∧ ∀ R : LocalAlgCat.{u, x} S.A,
      S.Condition R ↔ Ideal.map (algebraMap S.A R) I = ⊥ :=
  S.exists_fg_ideal_conditionOn_iff_map_eq_bot h₁ h₂ (S.flattensFGApprox hS)

end FlatAtPointSituation

end Module

end
