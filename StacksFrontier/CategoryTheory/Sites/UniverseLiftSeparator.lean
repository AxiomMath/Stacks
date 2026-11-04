module

public import Mathlib.CategoryTheory.Generator.Preadditive
public import Mathlib.CategoryTheory.Generator.Sheaf
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftColimits
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftInjective

/-!
# The universe lift of a separator of abelian sheaves is a separator

Let `J` be a Grothendieck topology on a category `C` and let
`L : Sheaf J AddCommGrpCat.{t} ⥤ Sheaf J AddCommGrpCat.{max t s}` be the universe lift of abelian
sheaves. This file shows that `L` carries a separator to a separator, and deduces that `L`
carries injective abelian sheaves to injective abelian sheaves as soon as abelian sheaves in the
smaller universe have a separator and those in the larger universe form a Grothendieck abelian
category (sheafification being available in both universes).

The argument has two halves.

* The free abelian sheaves `ℤ[h_X]`, for `X` an object of `C`, separate abelian sheaves in every
  coefficient universe, and the free abelian sheaf in the larger universe is the universe lift
  of the one in the smaller universe: lifting the universe commutes with the coproducts which
  form the free abelian presheaf, and with sheafification. So the larger sheaf category has a
  separating family of universe lifts.
* A fully faithful functor between abelian categories whose essential image is closed under
  subobjects, and contains a separating family, carries every separator to a separator. If
  `φ : F ⟶ F'` is killed by every map out of `L G`, then for a map `a : L A ⟶ F` the kernel of
  `a ≫ φ` is a subobject of `L A`, hence the lift of a subobject `A' ⊆ A`; every map `G ⟶ A`
  factors through `A'`, so `A' = A` because `G` is a separator, and `a ≫ φ = 0`.

## Main results

* `CategoryTheory.Functor.isSeparator_obj_of_isSeparating` — the abstract statement of the
  second half.
* `Stacks.Sheaves.UniverseLift.freeYonedaULiftIso` — the free abelian sheaf on `X` with
  coefficients in a lifted group is the lift of the free abelian sheaf in the smaller universe.
* `Stacks.Sheaves.UniverseLift.isSeparator_uliftSheafFunctor_obj` — the universe lift of a
  separator of abelian sheaves is a separator.
* `Stacks.Sheaves.UniverseLift.preservesInjectiveObjects_uliftSheafFunctor_of_hasSeparator` —
  the universe lift of abelian sheaves preserves injective objects.

## Implementation notes

`Stacks.Sheaves.UniverseLift.preservesInjectiveObjects_uliftSheafFunctor` proves the
preservation of injectives through Baer's criterion at a separator of the larger category which
is itself a lift, and takes that separator as a hypothesis. This file supplies it as the lift of
*any* separator of the smaller category, rather than by exhibiting a coproduct of free sheaves
as a lift: the coproduct over all objects of `C` is in general too large for the smaller
universe, whereas the separating family of free sheaves is indexed by the objects of `C` and
needs no coproduct at all.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe z s t v u

namespace CategoryTheory.Functor

variable {𝒜 ℬ : Type*} [Category* 𝒜] [Category* ℬ] [Abelian 𝒜] [Preadditive ℬ] [HasKernels ℬ]
  (L : 𝒜 ⥤ ℬ) [L.Full] [L.Faithful]

/-- **A fully faithful functor whose essential image is closed under subobjects and contains a
separating family carries separators to separators.** The closure under subobjects is phrased
as: every monomorphism into `L.obj A` is, up to isomorphism, `L` applied to a morphism into
`A`. -/
theorem isSeparator_obj_of_isSeparating
    (hsub : ∀ {A : 𝒜} {S : ℬ} (i : S ⟶ L.obj A) [Mono i],
      ∃ (S' : 𝒜) (i' : S' ⟶ A) (e : L.obj S' ≅ S), e.hom ≫ i = L.map i')
    {P : ObjectProperty ℬ} (hP : P.IsSeparating) (hPL : P ≤ L.essImage)
    {G : 𝒜} (hG : IsSeparator G) : IsSeparator (L.obj G) := by
  rw [Preadditive.isSeparator_iff]
  intro F F' φ hφ
  refine (Preadditive.isSeparating_iff P).1 hP φ fun T hT a ↦ ?_
  obtain ⟨A, ⟨eA⟩⟩ := hPL T hT
  let ψ : L.obj A ⟶ F' := eA.hom ≫ a ≫ φ
  obtain ⟨S', i', e, he⟩ := hsub (kernel.ι ψ)
  have hmono : Mono i' := L.mono_of_mono_map (by rw [← he]; infer_instance)
  have hepi : Epi i' := by
    refine Abelian.epi_of_cokernel_π_eq_zero _
      ((Preadditive.isSeparator_iff G).1 hG _ fun h ↦ ?_)
    have hh : L.map h ≫ ψ = 0 := by
      simpa only [ψ, Category.assoc] using hφ (L.map h ≫ eA.hom ≫ a)
    have hfac : L.map (L.preimage (kernel.lift ψ (L.map h) hh ≫ e.inv) ≫ i') = L.map h := by
      rw [Functor.map_comp, Functor.map_preimage, Category.assoc, ← he, Iso.inv_hom_id_assoc,
        kernel.lift_ι]
    rw [← L.map_injective hfac, Category.assoc, cokernel.condition, comp_zero]
  have : IsIso i' := isIso_of_mono_of_epi i'
  have : IsIso (kernel.ι ψ) := by
    rw [show kernel.ι ψ = e.inv ≫ L.map i' by rw [← he, Iso.inv_hom_id_assoc]]
    infer_instance
  have hψ : ψ = 0 := by
    rw [← cancel_epi (kernel.ι ψ), kernel.condition, comp_zero]
  rw [show a ≫ φ = eA.inv ≫ ψ by simp only [ψ, Iso.inv_hom_id_assoc], hψ, comp_zero]

end CategoryTheory.Functor

namespace Stacks.Sheaves.UniverseLift

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Comparison maps of coproducts of copies of one object are natural in the index set. -/
@[reassoc]
theorem _root_.CategoryTheory.Limits.map'_comp_sigmaComparison {𝒜 ℬ : Type*} [Category* 𝒜]
    [Category* ℬ] (Φ : 𝒜 ⥤ ℬ) {α β : Type*} (p : α → β) (M : 𝒜)
    [HasCoproduct fun _ : α ↦ M] [HasCoproduct fun _ : β ↦ M]
    [HasCoproduct fun _ : α ↦ Φ.obj M] [HasCoproduct fun _ : β ↦ Φ.obj M] :
    Sigma.map' p (fun _ ↦ 𝟙 (Φ.obj M)) ≫ sigmaComparison Φ (fun _ : β ↦ M) =
      sigmaComparison Φ (fun _ : α ↦ M) ≫ Φ.map (Sigma.map' p fun _ ↦ 𝟙 M) :=
  Sigma.hom_ext _ _ fun b ↦ by
    rw [Sigma.ι_comp_map'_assoc, Category.id_comp, ι_comp_sigmaComparison,
      ι_comp_sigmaComparison_assoc, ← Functor.map_comp, Sigma.ι_comp_map', Category.id_comp]

section FreeYoneda

variable [HasCoproducts.{v} AddCommGrpCat.{t}] [HasCoproducts.{v} AddCommGrpCat.{max t s}]

/-- The free abelian presheaf on `X` with coefficients in a lifted group is the objectwise lift
of the free abelian presheaf on `X`: lifting the universe commutes with coproducts. -/
def presheafFreeYonedaULiftIso (X : C) (M : AddCommGrpCat.{t}) :
    Presheaf.freeYoneda X (AddCommGrpCat.uliftFunctor.{s, t}.obj M) ≅
      Presheaf.freeYoneda X M ⋙ AddCommGrpCat.uliftFunctor.{s, t} :=
  have : PreservesColimitsOfSize.{v, v} AddCommGrpCat.uliftFunctor.{s, t} := inferInstance
  NatIso.ofComponents
    (fun Y ↦ (PreservesCoproduct.iso AddCommGrpCat.uliftFunctor.{s, t}
      (fun _ : (yoneda.obj X).obj Y ↦ M)).symm)
    (fun {_ _} f ↦ map'_comp_sigmaComparison AddCommGrpCat.uliftFunctor.{s, t}
      ((yoneda.obj X).map f) M)

variable [HasWeakSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  [HasWeakSheafify J AddCommGrpCat.{max t s}] [J.WEqualsLocallyBijective AddCommGrpCat.{max t s}]

/-- **The free abelian sheaf on `X` with coefficients in a lifted group is the universe lift of
the free abelian sheaf on `X`.** Lifting the universe commutes with the coproducts forming the
free abelian presheaf and with sheafification. -/
def freeYonedaULiftIso (X : C) (M : AddCommGrpCat.{t}) :
    Sheaf.freeYoneda J X (AddCommGrpCat.uliftFunctor.{s, t}.obj M) ≅
      (uliftSheafFunctor.{s, t} J).obj (Sheaf.freeYoneda J X M) :=
  have := preservesSheafification_uliftFunctor.{u, v, t, s} (J := J)
  (presheafToSheaf J AddCommGrpCat.{max t s}).mapIso (presheafFreeYonedaULiftIso X M) ≪≫
    (sheafComposeNatIso J AddCommGrpCat.uliftFunctor.{s, t}
      (sheafificationAdjunction J AddCommGrpCat.{t})
      (sheafificationAdjunction J AddCommGrpCat.{max t s})).app (Presheaf.freeYoneda X M)

omit [HasCoproducts.{v} AddCommGrpCat.{t}] [HasCoproducts.{v} AddCommGrpCat.{max t s}] in
/-- The universe lift of `ℤ` separates abelian groups in the larger universe. -/
theorem isSeparating_uliftFunctor_obj_ulift_int :
    ObjectProperty.IsSeparating (.ofObj fun _ : Unit ↦
      AddCommGrpCat.uliftFunctor.{s, t}.obj (AddCommGrpCat.of (ULift.{t} ℤ))) := by
  refine (Preadditive.isSeparating_iff _).2 fun A B f hf ↦ ?_
  ext x
  let h : AddCommGrpCat.uliftFunctor.{s, t}.obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ A :=
    AddCommGrpCat.ofHom
      { toFun := fun n ↦ n.down.down • x
        map_zero' := zero_smul ℤ x
        map_add' := fun m n ↦ add_smul m.down.down n.down.down x }
  have e : (h ≫ f).hom (ULift.up (ULift.up 1)) = f.hom ((1 : ℤ) • x) := rfl
  rw [hf _ (ObjectProperty.ofObj_apply _ ()) h, one_smul] at e
  exact e.symm

omit [HasCoproducts.{v} AddCommGrpCat.{t}] [HasWeakSheafify J AddCommGrpCat.{t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max t s}] in
/-- **The free abelian sheaves of the larger universe form a separating family of universe
lifts.** -/
theorem isSeparating_freeYoneda_ulift :
    ObjectProperty.IsSeparating (.ofObj fun (⟨X, _⟩ : C × Unit) ↦
      Sheaf.freeYoneda J X
        (AddCommGrpCat.uliftFunctor.{s, t}.obj (AddCommGrpCat.of (ULift.{t} ℤ)))) :=
  Sheaf.isSeparating J isSeparating_uliftFunctor_obj_ulift_int.{s, t}

omit [HasWeakSheafify J AddCommGrpCat.{t}] in
/-- **The universe lift of a separator of abelian sheaves is a separator.** -/
theorem isSeparator_uliftSheafFunctor_obj [HasSheafify J AddCommGrpCat.{t}]
    {G : Sheaf J AddCommGrpCat.{t}} (hG : IsSeparator G) :
    IsSeparator ((uliftSheafFunctor.{s, t} J).obj G) := by
  have : (uliftSheafFunctor.{s, t} J).Full := (fullyFaithfulUliftSheafFunctor J).full
  refine (uliftSheafFunctor.{s, t} J).isSeparator_obj_of_isSeparating (fun i _ ↦ ?_)
    (isSeparating_freeYoneda_ulift.{s, t} J) ?_ hG
  · obtain ⟨S', i', _, e, he⟩ := exists_uliftDescent J i
    exact ⟨S', i', e, he⟩
  · rintro _ ⟨⟨X, _⟩⟩
    exact ⟨_, ⟨(freeYonedaULiftIso.{s, t} J X _).symm⟩⟩

omit [HasWeakSheafify J AddCommGrpCat.{t}] [HasWeakSheafify J AddCommGrpCat.{max t s}] in
/-- **The universe lift of abelian sheaves preserves injective objects**, as soon as abelian
sheaves in the smaller universe have a separator and those in the larger universe form a
Grothendieck abelian category. -/
theorem preservesInjectiveObjects_uliftSheafFunctor_of_hasSeparator
    [HasSheafify J AddCommGrpCat.{t}] [HasSeparator (Sheaf J AddCommGrpCat.{t})]
    [HasSheafify J AddCommGrpCat.{max t s}]
    [IsGrothendieckAbelian.{z} (Sheaf J AddCommGrpCat.{max t s})] :
    (uliftSheafFunctor.{s, t} J).PreservesInjectiveObjects :=
  preservesInjectiveObjects_uliftSheafFunctor J
    (isSeparator_uliftSheafFunctor_obj.{s, t} J (isSeparator_separator (Sheaf J AddCommGrpCat.{t})))

end FreeYoneda

end Stacks.Sheaves.UniverseLift
