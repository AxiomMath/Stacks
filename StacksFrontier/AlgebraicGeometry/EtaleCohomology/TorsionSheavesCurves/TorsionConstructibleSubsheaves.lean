module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LocalTorsionColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstructibleBigSiteIndependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsShortExactConstructible
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A torsion sheaf is a filtered colimit of constructible subsheaves

Let `X` be a Noetherian scheme. Every torsion abelian sheaf `F` on Mathlib's small étale site of
`X` is the colimit of a filtered diagram of constructible sheaves each of which maps
monomorphically to `F`. This is Tag 03SA (2) read on Mathlib's site, with the terms replaced by
their images in `F`, which is the form in which the proof of Theorem 03SC uses it: a subsheaf of
`F` inherits every torsion condition imposed on `F`.

## Main results

* `Stacks.EtaleCohomology.torsionSheafProperty_sheafEquiv_inverse`: torsion passes from Mathlib's
  site to the size-bounded site of Tag 021B.
* `Stacks.EtaleCohomology.isColimit_imageCocone`: replacing the terms of a colimit cocone by their
  images in the cocone point gives a colimit cocone.
* `Stacks.EtaleCohomology.exists_isColimit_isConstructibleOnEveryBigSite_mono`: **the
  presentation.**
* `Stacks.EtaleCohomology.isPrimePowerTorsion_of_mono`,
  `Stacks.EtaleCohomology.isPrimeToCharacteristicTorsion_of_mono`: the torsion conditions pass
  to subsheaves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- **Torsion passes to the site of Tag 021B.** A torsion abelian sheaf on Mathlib's small étale
site restricts to a torsion sheaf on the size-bounded small étale site: the trivializing sieves
pull back along the cocontinuous embedding. -/
theorem torsionSheafProperty_sheafEquiv_inverse (B : BigEtaleSite.{u}) (X : Scheme.{u})
    (hX : B.Contains X) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) :
    Stacks.Torsion.torsionSheafProperty (SmallEtale.topology B X hX)
      ((SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}).inverse.obj F) := by
  intro V x
  obtain ⟨R, hR, h⟩ := hF ((SmallEtale.toEtaleSite B X hX).obj V) x
  exact ⟨R.functorPullback (SmallEtale.toEtaleSite B X hX),
    (SmallEtale.toEtaleSite B X hX).cover_lift (SmallEtale.topology B X hX)
      X.smallEtaleTopology hR, fun W f hf ↦ h _ _ hf⟩

section Image

variable {C : Type*} [Category C] [Abelian C] {I : Type*} [Category I] {D : I ⥤ C}
  {c : Cocone D} (hc : IsColimit c)

/-- The cocone on the images of the legs of `c`, with the same point. -/
abbrev imageCocone (c : Cocone D) : Cocone (Abelian.image c.ι) :=
  Cocone.mk c.pt (Abelian.image.ι c.ι)

/-- **Images of the legs of a colimit cocone form a colimit cocone.** -/
def isColimitImageCocone : IsColimit (imageCocone c) where
  desc s := hc.desc (Cocone.mk s.pt (Abelian.factorThruImage c.ι ≫ s.ι))
  fac s j := by
    rw [← cancel_epi ((Abelian.factorThruImage c.ι).app j)]
    have h := hc.fac (Cocone.mk s.pt (Abelian.factorThruImage c.ι ≫ s.ι)) j
    simp only [NatTrans.comp_app] at h
    rw [← h, ← Category.assoc, ← NatTrans.comp_app, Abelian.image.fac]
  uniq s m hm := by
    refine hc.hom_ext fun j ↦ ?_
    rw [hc.fac]
    change c.ι.app j ≫ m = (Abelian.factorThruImage c.ι).app j ≫ s.ι.app j
    rw [← hm j, ← Category.assoc, ← NatTrans.comp_app, Abelian.image.fac]

include hc in
/-- **A colimit cocone can be replaced by one with monomorphic legs and the same point**, each new
term being a quotient of the old one. -/
theorem exists_isColimit_mono_of_isColimit :
    ∃ (D' : I ⥤ C) (ι' : D' ⟶ (Functor.const I).obj c.pt),
      Nonempty (IsColimit (Cocone.mk c.pt ι')) ∧
        ∀ j, Mono (ι'.app j) ∧ ∃ p : D.obj j ⟶ D'.obj j, Epi p :=
  ⟨Abelian.image c.ι, Abelian.image.ι c.ι, ⟨isColimitImageCocone hc⟩,
    fun j ↦ ⟨inferInstance, (Abelian.factorThruImage c.ι).app j, inferInstance⟩⟩

end Image


/-- **Constructibility on every big étale site passes to quotients.** -/
theorem IsConstructibleOnEveryBigSite.of_epi {S : Scheme.{u}} [IsNoetherian S]
    {F Q : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}} (p : F ⟶ Q) [Epi p]
    (hF : IsConstructibleOnEveryBigSite F) : IsConstructibleOnEveryBigSite Q :=
  fun B hS _ _ ↦ isConstructibleEtaleAbelianSheaf_of_epi B hS p (hF B hS)

/-- **A torsion sheaf is a filtered colimit of constructible subsheaves** (Tag 03SA (2) on
Mathlib's small étale site, terms replaced by their images). On a Noetherian scheme every torsion
abelian sheaf `F` is the point of a colimit cocone over a small filtered category whose terms are
constructible on every big étale site and whose legs are monomorphisms. -/
@[sga "4½ Arcata 4.3.3"]
theorem exists_isColimit_isConstructibleOnEveryBigSite_mono {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (ι : D ⟶ (Functor.const I).obj F), Nonempty (IsColimit (Cocone.mk F ι)) ∧
        ∀ j, IsConstructibleOnEveryBigSite (D.obj j) ∧ Mono (ι.app j) := by
  let B := BigEtaleSite.containing X
  have hX : B.Contains X := BigEtaleSite.contains_containing X
  let e := SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}
  have : CompactSpace (B.obj X hX).obj := inferInstanceAs (CompactSpace X)
  have : QuasiSeparatedSpace (B.obj X hX).obj := inferInstanceAs (QuasiSeparatedSpace X)
  obtain ⟨I, hI, hfilt, D', ι', ⟨hc'⟩, hD'⟩ :=
    exists_isFilteredColimit_isConstructibleAbelianSheaf_of_qcqs B (B.obj X hX) (e.inverse.obj F)
      (torsionSheafProperty_sheafEquiv_inverse B X hX F hF)
  let c₁ := e.functor.mapCocone (Cocone.mk _ ι')
  let c₂ : Cocone (D' ⋙ e.functor) :=
    { pt := F
      ι := c₁.ι ≫ (Functor.const I).map (e.counit.app F) }
  have hc₂ : IsColimit c₂ :=
    (isColimitOfPreserves e.functor hc').ofIsoColimit (Cocones.ext (e.counitIso.app F) fun _ ↦ rfl)
  obtain ⟨D, ι, ⟨hc⟩, hD⟩ := exists_isColimit_mono_of_isColimit hc₂
  refine ⟨I, hI, hfilt, D, ι, ⟨hc⟩, fun j ↦ ⟨?_, (hD j).1⟩⟩
  obtain ⟨p, _⟩ := (hD j).2
  have hj : IsConstructibleOnEveryBigSite (e.functor.obj (D'.obj j)) :=
    IsConstructibleOnEveryBigSite.of_contains hX
      (isConstructibleAbelianSheaf_congr B (B.obj X hX) (e.unitIso.app (D'.obj j)) (hD' j))
  exact hj.of_epi p

section Torsion

variable {C : Type*} [Category C] {J : GrothendieckTopology C} [HasWeakSheafify J AddCommGrpCat.{u}]
  {F G : Sheaf J AddCommGrpCat.{u}} (i : G ⟶ F) [Mono i]

/-- A section of a subsheaf is killed by an integer once its image is. -/
theorem nsmul_eq_zero_of_mono {U : C} (x : G.obj.obj (Opposite.op U)) (n : ℕ)
    (h : n • i.hom.app (Opposite.op U) x = 0) : n • x = 0 := by
  have : Mono (i.hom.app (Opposite.op U)) := inferInstance
  refine (AddCommGrpCat.mono_iff_injective _).1 this ?_
  rw [map_nsmul, h, map_zero]

/-- A restriction of a section of a subsheaf is killed by an integer once its image is. -/
private theorem nsmul_map_eq_zero_of_mono {U V : C} (f : V ⟶ U) (x : G.obj.obj (Opposite.op U))
    (n : ℕ) (h : n • F.obj.map f.op (i.hom.app _ x) = 0) : n • G.obj.map f.op x = 0 :=
  nsmul_eq_zero_of_mono i _ _ (by rwa [NatTrans.naturality_apply i.hom f.op x])

include i in
/-- **Prime-power torsion passes to subsheaves.** -/
theorem isPrimePowerTorsion_of_mono {l : ℕ} (h : Stacks.Torsion.IsPrimePowerTorsion J l F) :
    Stacks.Torsion.IsPrimePowerTorsion J l G := by
  intro U x
  obtain ⟨R, hR, hR'⟩ := h U (i.hom.app _ x)
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  obtain ⟨r, hr, hx⟩ := hR' V f hf
  refine ⟨r, hr, nsmul_map_eq_zero_of_mono i f x _ hx⟩

include i in
/-- **Torsion prime to `p` passes to subsheaves.** -/
theorem isPrimeToCharacteristicTorsion_of_mono {p : ℕ}
    (h : Stacks.Torsion.IsPrimeToCharacteristicTorsion J p F) :
    Stacks.Torsion.IsPrimeToCharacteristicTorsion J p G := by
  intro U x
  obtain ⟨R, hR, hR'⟩ := h U (i.hom.app _ x)
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  obtain ⟨n, hn, hcop, hx⟩ := hR' V f hf
  refine ⟨n, hn, hcop, nsmul_map_eq_zero_of_mono i f x _ hx⟩

end Torsion

end Stacks.EtaleCohomology
