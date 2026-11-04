module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.FiniteDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystemIdentity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsClopen
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.NormalizationReduction
public import StacksFrontier.AlgebraicGeometry.FiniteFactorization.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.Reduction

/-!
# Extending a finite morphism over an open to a finite morphism, for Lemma 03SD

In the proof of Lemma 03SD a finite étale `f : V ⟶ U` over an open `j : U ⟶ X` is extended by
Zariski's Main Theorem (Tag 05K0) to a finite `f̄ : Y ⟶ X` with an open immersion `j' : V ⟶ Y`,
and Tag 0GJ1 identifies `j_! f_*` with `f̄_* j'_!`. The source arranges `V` to be dense in `Y`
so that `V = U ×_X Y`; here no density is needed: `V` is open and closed in `U ×_X Y`, and an
open and closed immersion `c` has `c_! = c_*` (Tag 0GJ1 for the square of `c` with itself).

## Main results

* `Stacks.EtaleCohomology.extensionByZeroIsoDirectImage`: `c_! ≅ c_*` for an open and closed
  immersion `c`.
* `Stacks.EtaleCohomology.exists_isFinite_isOpenImmersion_isReduced_comp_eq`: the finite
  extension `f̄` with `Y` reduced (Tag 05K0 and the reduction of `Y`).
* `Stacks.EtaleCohomology.exists_isFinite_extensionByZero_directImage_iso`: the finite extension
  together with `j_! f_* ≅ f̄_* j'_!`.
* `Stacks.EtaleCohomology.IsConstructibleOnEveryBigSite.of_shortExact`: constructible sheaves
  are closed under extensions (Proposition 09BH), on Mathlib's small étale site.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

section Identity

variable (V : Scheme.{u})

/-- The direct image along the identity is the identity. -/
def etaleAbelianDirectImageIdIso : etaleAbelianDirectImage.{u, 0} (𝟙 V) ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId' (smallEtaleBaseChangeId V) _ _

/-- The inverse image along the identity is the identity. -/
def etaleAbelianInverseImageIdIso : etaleAbelianInverseImage.{u, 0} (𝟙 V) ≅ 𝟭 _ :=
  Adjunction.leftAdjointUniq (etaleAbelianInverseImageDirectImageAdj.{u, 0} (𝟙 V))
    (Adjunction.id.ofNatIsoRight (etaleAbelianDirectImageIdIso V).symm)

/-- Extension by zero along the identity is the identity. -/
def extensionByZeroIdIso : extensionByZero.{u, 0} (𝟙 V) ≅ 𝟭 _ :=
  Adjunction.leftAdjointUniq (extensionByZeroAdj.{u, 0} (𝟙 V))
    (Adjunction.id.ofNatIsoRight ((etaleAbelianInverseImageRestrictionIso.{u, 0} (𝟙 V)).symm ≪≫
      etaleAbelianInverseImageIdIso V).symm)

end Identity

/-- **For an open and closed immersion `c`, extension by zero is the direct image**: Tag 0GJ1
for the cartesian square of the monomorphism `c` with itself. -/
def extensionByZeroIsoDirectImage {V P : Scheme.{u}} (c : V ⟶ P) [IsOpenImmersion c]
    [IsClosedImmersion c] : extensionByZero.{u, 0} c ≅ etaleAbelianDirectImage.{u, 0} c :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (etaleAbelianDirectImageIdIso V).symm _ ≪≫
    (directImageExtensionByZeroIso (𝟙 V) (𝟙 V) c c (IsKernelPair.id_of_mono c)).symm ≪≫
    Functor.isoWhiskerRight (extensionByZeroIdIso V) _ ≪≫ Functor.leftUnitor _

/-- **A finite morphism over an open extends to a finite morphism with reduced source** (Tag 05K0
and the reduction of the source). Let `X` be Noetherian, `j : U ⟶ X` an open immersion and
`f : V ⟶ U` finite with `V` reduced. Then there are a reduced scheme `Y`, a finite `f̄ : Y ⟶ X`
and an open immersion `j' : V ⟶ Y` with `j' ≫ f̄ = f ≫ j`. -/
theorem exists_isFinite_isOpenImmersion_isReduced_comp_eq {X U V : Scheme.{u}} [IsNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] (f : V ⟶ U) [IsFinite f] [IsReduced V] :
    ∃ (Y : Scheme.{u}) (fbar : Y ⟶ X) (j' : V ⟶ Y) (_ : IsFinite fbar) (_ : IsOpenImmersion j'),
      IsReduced Y ∧ j' ≫ fbar = f ≫ j := by
  obtain ⟨T, j₁, π, hj₁, -, hπ, hfac⟩ :=
    Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_factorization (f ≫ j)
  have : Surjective T.reductionι := ⟨T.surjective_reductionι⟩
  have : IsIso (pullback.fst j₁ T.reductionι) := isIso_of_isClosedImmersion_of_surjective _
  refine ⟨T.reduction, T.reductionι ≫ π, inv (pullback.fst j₁ T.reductionι) ≫
    pullback.snd j₁ T.reductionι, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [Category.assoc, ← Category.assoc (pullback.snd _ _), ← pullback.condition,
    Category.assoc, IsIso.inv_hom_id_assoc, hfac]

/-- **The finite extension of `f` and the comparison `j_! f_* ≅ f̄_* j'_!`** (the step of Lemma
03SD that combines Tags 05K0 and 0GJ1). Let `X` be Noetherian, `j : U ⟶ X` an open immersion and
`f : V ⟶ U` finite with `V` reduced. Then there are a reduced `Y`, a finite `f̄ : Y ⟶ X` and an
open immersion `j' : V ⟶ Y` with `j' ≫ f̄ = f ≫ j` and `f_* ⋙ j_! ≅ j'_! ⋙ f̄_*`.

The open immersion `V ⟶ U ×_X Y` is finite, hence open and closed, so its extension by zero is
its direct image; Tag 0GJ1 for the cartesian square `U ×_X Y` does the rest. -/
theorem exists_isFinite_extensionByZero_directImage_iso {X U V : Scheme.{u}} [IsNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] (f : V ⟶ U) [IsFinite f] [IsReduced V] :
    ∃ (Y : Scheme.{u}) (fbar : Y ⟶ X) (j' : V ⟶ Y) (_ : IsFinite fbar) (_ : IsOpenImmersion j'),
      IsReduced Y ∧ j' ≫ fbar = f ≫ j ∧
        Nonempty (etaleAbelianDirectImage.{u, 0} f ⋙ extensionByZero.{u, 0} j ≅
          extensionByZero.{u, 0} j' ⋙ etaleAbelianDirectImage.{u, 0} fbar) := by
  obtain ⟨Y, fb, j₀, _, _, hY, hw⟩ := exists_isFinite_isOpenImmersion_isReduced_comp_eq j f
  let c : V ⟶ pullback j fb := pullback.lift f j₀ hw.symm
  have : IsOpenImmersion (c ≫ pullback.snd j fb) := by
    rw [pullback.lift_snd]; infer_instance
  have : IsOpenImmersion c := IsOpenImmersion.of_comp c (pullback.snd j fb)
  have : IsFinite (c ≫ pullback.fst j fb) := by
    rw [pullback.lift_fst]; infer_instance
  have : IsFinite c := IsFinite.of_comp c (pullback.fst j fb)
  have : IsClosedImmersion c := (IsClosedImmersion.iff_isFinite_and_mono c).mpr ⟨‹_›, inferInstance⟩
  refine ⟨Y, fb, c ≫ pullback.snd j fb, inferInstance, inferInstance, hY, ?_, ⟨?_⟩⟩
  · rw [Category.assoc, ← pullback.condition, ← Category.assoc, pullback.lift_fst]
  · exact Functor.isoWhiskerRight (eqToIso (by rw [pullback.lift_fst]) ≪≫
        (etaleAbelianDirectImageCompIso.{u, 0} c (pullback.fst j fb)).symm) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (directImageExtensionByZeroIso (pullback.snd j fb)
        (pullback.fst j fb) fb j (IsPullback.of_hasPullback j fb).flip).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerRight (extensionByZeroIsoDirectImage c).symm _ ≪≫
        extensionByZeroCompIso c (pullback.snd j fb)) _

/-- **Constructible sheaves are closed under extensions** (Proposition 09BH), read on Mathlib's
small étale site with respect to every ambient big étale site. -/
theorem IsConstructibleOnEveryBigSite.of_shortExact {S : Scheme.{u}}
    {T : ShortComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})} (hT : T.ShortExact)
    (h₁ : IsConstructibleOnEveryBigSite T.X₁) (h₃ : IsConstructibleOnEveryBigSite T.X₃) :
    IsConstructibleOnEveryBigSite T.X₂ := fun B hS _ _ ↦
  isConstructibleAbelianSheaf_of_shortExact B (B.obj S hS)
    (hT.map_of_exact (SmallEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}).inverse)
    (h₁ B hS) (h₃ B hS)

/-- **Extension by zero of a sheaf with a finite filtration by a finite constant sheaf is
constructible**, on a Noetherian scheme: by induction along the filtration, extension by zero
being exact (Tag 03S5), constructible sheaves closed under extensions, and the extension by zero
of a finite constant sheaf constructible. -/
theorem isConstructibleOnEveryBigSite_extensionByZero_of_hasConstantFiltration {S V : Scheme.{u}}
    [IsNoetherian S] (j : V ⟶ S) [IsOpenImmersion j] (E : AddCommGrpCat.{u + 1}) [Finite E] :
    ∀ (n : ℕ) (K : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}),
      HasConstantFiltration E n K →
        IsConstructibleOnEveryBigSite ((extensionByZero.{u, 0} j).obj K) := by
  intro n
  induction n with
  | zero =>
    intro K hK
    have hz := (extensionByZero.{u, 0} j).map_isZero hK
    have : Mono (hz.to_ ((extensionByZero.{u, 0} j).obj
        ((constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E))) := hz.mono _
    exact (isConstructibleOnEveryBigSite_extensionByZero_constantSheaf j E).of_mono
      (hz.to_ _)
  | succ n ih =>
    rintro K ⟨T, hT, ⟨e₂⟩, h₁, ⟨e₃⟩⟩
    have := extensionByZero_exact.{u, 0} j
    refine IsConstructibleOnEveryBigSite.of_iso ((extensionByZero.{u, 0} j).mapIso e₂)
      (IsConstructibleOnEveryBigSite.of_shortExact (hT.map_of_exact (extensionByZero.{u, 0} j))
        (ih _ h₁) ?_)
    exact (isConstructibleOnEveryBigSite_extensionByZero_constantSheaf j E).of_iso
      ((extensionByZero.{u, 0} j).mapIso e₃).symm

/-- **Extension by zero along a disjoint union of two opens** (Tag 095L on the source and the
equality `c_! = c_*` for open and closed immersions). For an open immersion `j : W ⟶ X` and a
decomposition of `W` into complementary opens `A` and `B`, every abelian sheaf `G` on `W` gives a
short exact sequence `0 → (j|_A)_! G|_A → j_! G → (j|_B)_! G|_B → 0`, with the outer terms
identified up to isomorphism. -/
theorem exists_shortExact_extensionByZero_of_isCompl {W X : Scheme.{u}} [IsNoetherian W]
    (j : W ⟶ X) [IsOpenImmersion j] {A B : W.Opens} (hAB : IsCompl A B)
    (G : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ∃ T : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}), T.ShortExact ∧
      Nonempty (T.X₁ ≅ (extensionByZero.{u, 0} (A.ι ≫ j)).obj
        ((etaleRestriction.{u, 0} A.ι).obj G)) ∧
      Nonempty (T.X₂ ≅ (extensionByZero.{u, 0} j).obj G) ∧
      Nonempty (T.X₃ ≅ (extensionByZero.{u, 0} (B.ι ≫ j)).obj
        ((etaleAbelianInverseImage.{u, 0} B.ι).obj G)) := by
  have := isClosedImmersion_ι_of_isCompl hAB.symm
  obtain ⟨_, hS⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, 0} B.ι A.ι
    (range_ι_eq_compl_of_isCompl hAB.symm) G
  have := extensionByZero_exact.{u, 0} j
  exact ⟨_, hS.map_of_exact (extensionByZero.{u, 0} j),
    ⟨(extensionByZeroCompIso A.ι j).app _⟩, ⟨Iso.refl _⟩,
    ⟨(extensionByZero.{u, 0} j).mapIso ((extensionByZeroIsoDirectImage B.ι).app _).symm ≪≫
      (extensionByZeroCompIso B.ι j).app _⟩⟩

end Stacks.EtaleCohomology

end
