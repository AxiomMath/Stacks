module

public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Representable.EffectiveEpiFamily

/-!
# Checking universal effective epimorphy on affine bases

A family of morphisms of schemes is universally effective epimorphic as soon as its base
change along every morphism out of an affine scheme is an effective epimorphic family. So
the universal property, which quantifies over all base changes, only has to be verified
over affine bases.

## Main results

* `AlgebraicGeometry.isUniversalEffectiveEpiFamily_of_affine_baseChange` checks universal
  effective epimorphy on affine bases.

## Implementation notes

The affine-base hypothesis is stated with the chosen fibre products, while the conclusion
uses the choice-independent universal effective epimorphic family predicate; the two are
reconciled by transporting an effective epimorphic family along isomorphisms of its members
over the common target. The reduction from an arbitrary base to an affine one is Zariski
descent of the sheaf condition along the affine one-hypercover of the base.

## References

* [Stacks Project, Tag 0EUC](https://stacks.math.columbia.edu/tag/0EUC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry

/-- An effective epimorphic family can be recognised from its base changes to affine
schemes. -/
private theorem isEffectiveEpiFamily_of_affine_baseChanges
    {I : Type w} {Y : Scheme.{u}} (A : I → Scheme.{u}) (q : ∀ i, A i ⟶ Y)
    (h : ∀ (Z : Scheme.{u}) [IsAffine Z] (g : Z ⟶ Y),
      StacksEffectiveEpi.IsEffectiveEpiFamily
        (fun i => pullback (q i) g) (fun i => pullback.snd (q i) g)) :
    StacksEffectiveEpi.IsEffectiveEpiFamily A q := by
  have hrep : StacksEffectiveEpi.IsRepresentableFamily A q := fun _ => inferInstance
  rw [hrep.isEffectiveEpiFamily_iff, ← Sieve.effectiveEpimorphic_family A q,
    Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]
  let E := Y.affineOneHypercover
  let R : Presieve Y := Presieve.ofArrows A q
  intro T
  have hF : Presieve.IsSheaf Scheme.zariskiTopology (yoneda.obj T) := by
    let _ : Scheme.zariskiTopology.Subcanonical := Scheme.subcanonical_zariskiTopology
    exact Presieve.isSheaf_of_le (yoneda.obj T)
      (GrothendieckTopology.Subcanonical.le_canonical (J := Scheme.zariskiTopology))
      (Sheaf.isSheaf_yoneda_obj T)
  have hlocal (Z : Scheme.{u}) [IsAffine Z] (g : Z ⟶ Y) :
      Presieve.IsSheafFor (yoneda.obj T) (Sieve.pullback g (Sieve.generate R)).arrows := by
    have hrep' : StacksEffectiveEpi.IsRepresentableFamily
        (fun i => pullback (q i) g) (fun i => pullback.snd (q i) g) := fun _ => inferInstance
    rw [← Sieve.pullbackArrows_comm g R, ← Presieve.ofArrows_pullback,
      ← Presieve.isSheafFor_iff_generate]
    exact ((Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda _).1
      ((Sieve.effectiveEpimorphic_family _ _).2
        (hrep'.isEffectiveEpiFamily_iff.mp (h Z g)))) T
  refine E.isSheafFor_of_pullback hF (fun i => ?_) (fun i j k => ?_)
  · have : IsAffine (E.X i) := inferInstanceAs (IsAffine (Spec _))
    exact hlocal _ _
  · have : IsAffine (E.Y k) := inferInstanceAs (IsAffine (Spec _))
    exact (hlocal _ _).isSeparatedFor

/-- Being an effective epimorphic family is invariant under replacing the members of the
family by isomorphic schemes over the common target. -/
private theorem isEffectiveEpiFamily_of_iso
    {I : Type w} {Y : Scheme.{u}} {A B : I → Scheme.{u}}
    (p : ∀ i, A i ⟶ Y) (q : ∀ i, B i ⟶ Y)
    (e : ∀ i, A i ≅ B i) (he : ∀ i, (e i).hom ≫ q i = p i)
    (h : StacksEffectiveEpi.IsEffectiveEpiFamily A p) :
    StacksEffectiveEpi.IsEffectiveEpiFamily B q := by
  refine ⟨fun _ => inferInstance, fun T g hg => ?_⟩
  let gA i := (e i).hom ≫ g i
  have hgA : ∀ (i j : I) (Z : Scheme.{u}) (a : Z ⟶ A i) (b : Z ⟶ A j),
      IsPullback a b (p i) (p j) → a ≫ gA i = b ≫ gA j := by
    intro i j Z a b hab
    have hab' : IsPullback (a ≫ (e i).hom) (b ≫ (e j).hom) (q i) (q j) := by
      apply hab.of_iso (Iso.refl _) (e i) (e j) (Iso.refl _) <;> simp [← he]
    simpa [gA, Category.assoc] using hg i j Z (a ≫ (e i).hom) (b ≫ (e j).hom) hab'
  obtain ⟨t, ht, htuniq⟩ := h.2 T gA hgA
  refine ⟨t, fun i => (cancel_epi (e i).hom).1 ?_, fun t' ht' => htuniq t' fun i => ?_⟩
  · rw [← Category.assoc, he i, ht]
  · rw [← he i, Category.assoc, ht']

/-- A family of morphisms of schemes is universally effective epimorphic if all its
base changes to affine schemes are effective epimorphic families. -/
@[stacks 0EUC]
theorem isUniversalEffectiveEpiFamily_of_affine_baseChange
    {I : Type w} {X : Scheme.{u}} (X' : I → Scheme.{u}) (f : ∀ i, X' i ⟶ X)
    (h : ∀ (Y : Scheme.{u}) [IsAffine Y] (g : Y ⟶ X),
      StacksEffectiveEpi.IsEffectiveEpiFamily
        (fun i => pullback (f i) g) (fun i => pullback.snd (f i) g)) :
    StacksEffectiveEpi.IsUniversalEffectiveEpiFamily X' f := by
  refine ⟨fun _ => inferInstance, fun Y g A q p hp => ?_⟩
  let C i := pullback (f i) g
  let π i : C i ⟶ Y := pullback.snd (f i) g
  have hcan : StacksEffectiveEpi.IsEffectiveEpiFamily C π := by
    refine isEffectiveEpiFamily_of_affine_baseChanges C π fun Z hZ k => ?_
    let ρ i : pullback (f i) (k ≫ g) ⟶ Z := pullback.snd (f i) (k ≫ g)
    let e (i) : pullback (f i) (k ≫ g) ≅ pullback (π i) k :=
      (pullbackLeftPullbackSndIso (f i) g k).symm
    have he : ∀ i, (e i).hom ≫ pullback.snd (π i) k = ρ i := fun i =>
      pullbackLeftPullbackSndIso_inv_snd_snd (f i) g k
    exact isEffectiveEpiFamily_of_iso ρ (fun i => pullback.snd (π i) k) e he (@h Z hZ (k ≫ g))
  let e (i) : C i ≅ A i :=
    ((hp i).flip.isoIsPullback _ _ (IsPullback.of_hasPullback (f i) g)).symm
  have he : ∀ i, (e i).hom ≫ q i = π i := fun i => by
    simp [e, π, IsPullback.isoIsPullback_inv_snd]
  exact isEffectiveEpiFamily_of_iso π q e he hcan

end AlgebraicGeometry
