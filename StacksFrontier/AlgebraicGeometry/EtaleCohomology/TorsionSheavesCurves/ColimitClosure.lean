module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.Reduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FilteredColimitsOfEtaleCohomology
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.SectionsOnALocallySmallSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence

/-!
# The assertions of Stacks Tag 03SC pass to filtered colimits

Let `X` be a quasi-compact quasi-separated scheme. Étale cohomology of `X` commutes with filtered
colimits of abelian sheaves (Stacks Tag 03Q5), and inverse image along a morphism of schemes
commutes with all colimits, being a left adjoint. So a class of `H^q(X, colim F_i)` comes from
some `H^q(X, F_i)`, and a class of `H^q(X, F_i)` dying in the colimit dies at some later stage.
This file draws the consequences the proof of Tag 03SC uses: vanishing passes to a filtered
colimit, and so does bijectivity or surjectivity of a restriction map. Assembled, the six
assertions of Tag 03SC that are not about constructible sheaves pass from the terms of a filtered
diagram to its colimit.

## Main results

* `Stacks.EtaleCohomology.exists_sheafH_map_eq_of_isColimit` and
  `Stacks.EtaleCohomology.exists_sheafH_map_eq_zero_of_isColimit`: Tag 03Q5 elementwise.
* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_colimit_of_forall` and
  `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_colimit_of_forall`.
* `Stacks.EtaleCohomology.TorsionCurveAssertions.of_isColimit`: the closure of the assertions of
  Tag 03SC under filtered colimits.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

section Colimit

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
  {D : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone D}

/-- **Stacks Tag 03Q5 for `Sheaf.H`.** On a quasi-compact quasi-separated scheme the cohomology
functor carries a filtered colimit cocone to a colimit cocone. -/
def isColimitMapCoconeFunctorH (hc : IsColimit c) (q : ℕ) :
    IsColimit ((Sheaf.functorH.{u + 1, u + 1, u, u + 1} X.smallEtaleTopology q).mapCocone c) := by
  have := Stacks.Cohomology.GlobalSections.additive_Γ.{u + 1, u, u + 1} X.smallEtaleTopology
  have h1 : IsIso (colimit.post D
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived q)) :=
    isIso_colimit_post_rightDerived_Γ_smallEtale.{u + 1, u} X q D
  have : IsIso (colimit.post D (Sheaf.functorH.{u + 1, u + 1, u, u + 1} X.smallEtaleTopology q)) :=
    Stacks.Cohomology.isIso_colimit_post_of_natIso D _ _
      (Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{u + 1, u, u + 1}
        X.smallEtaleTopology q)
  have := preservesColimit_of_isIso_post
    (Sheaf.functorH.{u + 1, u + 1, u, u + 1} X.smallEtaleTopology q) D
  exact isColimitOfPreserves _ hc

/-- Every class of the cohomology of a filtered colimit comes from a term of the diagram. -/
theorem exists_sheafH_map_eq_of_isColimit (hc : IsColimit c) (q : ℕ)
    (x : Sheaf.H.{u + 1} c.pt q) :
    ∃ (i : I) (y : Sheaf.H.{u + 1} (D.obj i) q), Sheaf.H.map (c.ι.app i) q y = x := by
  obtain ⟨i, y, hy⟩ := Concrete.isColimit_exists_rep _ (isColimitMapCoconeFunctorH hc q) x
  exact ⟨i, y, hy⟩

/-- A class of the cohomology of a term of a filtered diagram which dies in the cohomology of the
colimit dies at a later stage. -/
theorem exists_sheafH_map_eq_zero_of_isColimit (hc : IsColimit c) (q : ℕ) {i : I}
    (y : Sheaf.H.{u + 1} (D.obj i) q) (hy : Sheaf.H.map (c.ι.app i) q y = 0) :
    ∃ (j : I) (φ : i ⟶ j), Sheaf.H.map (D.map φ) q y = 0 := by
  have h :
      ((Sheaf.functorH.{u + 1, u + 1, u, u + 1} X.smallEtaleTopology q).mapCocone c).ι.app i y =
      ((Sheaf.functorH.{u + 1, u + 1, u, u + 1} X.smallEtaleTopology q).mapCocone c).ι.app i 0 := by
    change Sheaf.H.map (c.ι.app i) q y = Sheaf.H.map (c.ι.app i) q 0
    rw [hy, map_zero]
  obtain ⟨j, φ, ψ, hφ⟩ := Concrete.isColimit_exists_of_rep_eq _
    (isColimitMapCoconeFunctorH hc q) y 0 h
  refine ⟨j, φ, ?_⟩
  change Sheaf.H.map (D.map φ) q y = Sheaf.H.map (D.map ψ) q 0 at hφ
  rw [hφ, map_zero]

/-- Vanishing of cohomology passes to a filtered colimit. -/
theorem subsingleton_sheafH_colimit_of_forall (hc : IsColimit c) (q : ℕ)
    (h : ∀ i, Subsingleton (Sheaf.H.{u + 1} (D.obj i) q)) :
    Subsingleton (Sheaf.H.{u + 1} c.pt q) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨i, x', rfl⟩ := exists_sheafH_map_eq_of_isColimit hc q x
  obtain ⟨j, y', rfl⟩ := exists_sheafH_map_eq_of_isColimit hc q y
  rw [Subsingleton.elim x' 0, Subsingleton.elim y' 0, map_zero, map_zero]

end Colimit

section Restriction

variable {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ X)
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
  {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
  {D : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone D}

omit [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] in
/-- Restriction commutes with the map on cohomology induced by a morphism of sheaves. -/
theorem etaleCohomologyRestrictionMap_sheafHMap
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G) (q : ℕ)
    (x : Sheaf.H.{u + 1} F q) :
    etaleCohomologyRestrictionMap.{u, u + 1, u + 1} g G q (Sheaf.H.map φ q x) =
      Sheaf.H.map ((etaleAbelianInverseImage.{u, u + 1} g).map φ) q
        (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} g F q x) :=
  etaleCohomologyRestrictionMap_comp_mk₀.{u, u + 1, u + 1} g φ q x

/-- The inverse image of a colimit cocone is a colimit cocone. -/
def isColimitMapCoconeInverseImage (hc : IsColimit c) :
    IsColimit ((etaleAbelianInverseImage.{u, u + 1} g).mapCocone c) :=
  isColimitOfPreserves _ hc

/-- **Injectivity of restriction passes to a filtered colimit.** -/
theorem injective_etaleCohomologyRestrictionMap_colimit_of_forall (hc : IsColimit c) (q : ℕ)
    (h : ∀ i, Function.Injective
      (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} g (D.obj i) q)) :
    Function.Injective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} g c.pt q) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨i, y, rfl⟩ := exists_sheafH_map_eq_of_isColimit hc q x
  rw [etaleCohomologyRestrictionMap_sheafHMap] at hx
  obtain ⟨j, φ, hφ⟩ :=
    exists_sheafH_map_eq_zero_of_isColimit (isColimitMapCoconeInverseImage g hc) q _ hx
  change Sheaf.H.map ((etaleAbelianInverseImage.{u, u + 1} g).map (D.map φ)) q _ = 0 at hφ
  rw [← etaleCohomologyRestrictionMap_sheafHMap] at hφ
  rw [← c.w φ, Sheaf.H.map_comp_apply, (injective_iff_map_eq_zero _).mp (h j) _ hφ, map_zero]

omit [CompactSpace X] [QuasiSeparatedSpace X] in
/-- **Surjectivity of restriction passes to a filtered colimit.** -/
theorem surjective_etaleCohomologyRestrictionMap_colimit_of_forall (hc : IsColimit c) (q : ℕ)
    (h : ∀ i, Function.Surjective
      (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} g (D.obj i) q)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} g c.pt q) := by
  intro z
  obtain ⟨i, w, rfl⟩ :=
    exists_sheafH_map_eq_of_isColimit (isColimitMapCoconeInverseImage g hc) q z
  obtain ⟨y, rfl⟩ := h i w
  exact ⟨Sheaf.H.map (c.ι.app i) q y, etaleCohomologyRestrictionMap_sheafHMap g _ q y⟩

/-- **Bijectivity of restriction passes to a filtered colimit.** -/
theorem bijective_etaleCohomologyRestrictionMap_colimit_of_forall (hc : IsColimit c) (q : ℕ)
    (h : ∀ i, Function.Bijective
      (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} g (D.obj i) q)) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} g c.pt q) :=
  ⟨injective_etaleCohomologyRestrictionMap_colimit_of_forall g hc q fun i => (h i).1,
    surjective_etaleCohomologyRestrictionMap_colimit_of_forall g hc q fun i => (h i).2⟩

end Restriction

namespace TorsionCurveAssertions

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [AlgebraicGeometry.IsNoetherian X]
  [QuasiCompact f] [QuasiSeparated f]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
  {D : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone D}

omit [AlgebraicGeometry.IsNoetherian X] [QuasiSeparated f]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- The base change of a quasi-compact `k`-scheme `X` to a field extension `k'` is
quasi-compact. -/
theorem compactSpace_scalarExtension (k' : Type u) [Field k'] [Algebra k k'] :
    CompactSpace (scalarExtension k k' f) :=
  QuasiCompact.compactSpace_of_compactSpace
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))

omit [AlgebraicGeometry.IsNoetherian X] [QuasiCompact f]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- The base change of a quasi-separated `k`-scheme `X` to a field extension `k'` is
quasi-separated. -/
theorem quasiSeparatedSpace_scalarExtension (k' : Type u) [Field k'] [Algebra k k'] :
    QuasiSeparatedSpace (scalarExtension k k' f) :=
  quasiSeparatedSpace_of_quasiSeparated
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))

omit [QuasiCompact f] [QuasiSeparated f]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- Every open subscheme of a Noetherian scheme is quasi-compact. -/
theorem compactSpace_opens (U : X.Opens) : CompactSpace (U : Scheme.{u}) :=
  isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)

omit [QuasiCompact f] [QuasiSeparated f]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- Every open subscheme of a quasi-separated scheme is quasi-separated. -/
theorem quasiSeparatedSpace_opens (U : X.Opens) : QuasiSeparatedSpace (U : Scheme.{u}) :=
  quasiSeparatedSpace_of_quasiSeparated U.ι

/-- **The assertions of Stacks Tag 03SC pass to a filtered colimit.** On a Noetherian scheme `X`
over a field, let `F` be the colimit of a filtered diagram of abelian sheaves satisfying the eight
assertions. If each torsion condition on `F` imposed by an assertion is inherited by the terms of
the diagram, and the assertions hold for `F` when it is constructible, then they hold for `F`. -/
theorem of_isColimit (hc : IsColimit c) (hD : ∀ i, TorsionCurveAssertions f (D.obj i))
    (hp : ∀ p : ℕ, Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology p c.pt →
      ∀ i, Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology p (D.obj i))
    (ht : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology (ringExpChar k) c.pt →
      ∀ i, Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology (ringExpChar k)
        (D.obj i))
    (hcons : IsConstructibleSmallEtaleSheaf c.pt → TorsionCurveAssertions f c.pt) :
    TorsionCurveAssertions f c.pt where
  vanishing q hq := subsingleton_sheafH_colimit_of_forall hc q fun i => (hD i).vanishing q hq
  vanishing_of_isAffine hX q hq :=
    subsingleton_sheafH_colimit_of_forall hc q fun i => (hD i).vanishing_of_isAffine hX q hq
  vanishing_of_isPrimePowerTorsion p hp' hp0 hF q hq :=
    subsingleton_sheafH_colimit_of_forall hc q fun i =>
      (hD i).vanishing_of_isPrimePowerTorsion p hp' hp0 (hp p hF i) q hq
  finite_of_isPrimeToCharacteristicTorsion hcF :=
    (hcons hcF).finite_of_isPrimeToCharacteristicTorsion hcF
  finite_of_isProper hf hcF := (hcons hcF).finite_of_isProper hf hcF
  bijective_of_isPrimeToCharacteristicTorsion htF k' _ _ _ _ q := by
    have := compactSpace_scalarExtension f k'
    have := quasiSeparatedSpace_scalarExtension f k'
    exact bijective_etaleCohomologyRestrictionMap_colimit_of_forall _ hc q fun i =>
      (hD i).bijective_of_isPrimeToCharacteristicTorsion (ht htF i) k' q
  bijective_of_isProper hf k' _ _ _ _ q := by
    have := compactSpace_scalarExtension f k'
    have := quasiSeparatedSpace_scalarExtension f k'
    exact bijective_etaleCohomologyRestrictionMap_colimit_of_forall _ hc q fun i =>
      (hD i).bijective_of_isProper hf k' q
  surjective_restriction U _ := by
    have := compactSpace_opens U
    have := quasiSeparatedSpace_opens U
    exact surjective_etaleCohomologyRestrictionMap_colimit_of_forall _ hc 2 fun i =>
      (hD i).surjective_restriction U

end TorsionCurveAssertions

end Stacks.EtaleCohomology

end
