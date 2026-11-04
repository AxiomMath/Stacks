module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackOfToposHom

/-!
# The derived pullback of algebraic spaces is right t-exact

Let `f : X ⟶ Y` be a morphism of algebraic spaces.  An object of `D(𝒪_Y)` with no cohomology
above degree `n` is represented by a complex of flat modules strictly bounded above by `n`, on
which `Lf^*` is computed by degreewise pullback; so `Lf^*` preserves the bound.

## Main results

* `AlgebraicGeometry.Space.exists_flat_representative_of_isLE`: the bounded above flat
  representative.
* `AlgebraicGeometry.Space.isLE_smallEtaleDerivedModulePullback_obj`: `Lf^*` is right t-exact.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 06YF](https://stacks.math.columbia.edu/tag/06YF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}

/-- Every object of `D(𝒪_Y)` bounded above by `n` is represented by a complex of flat modules
strictly bounded above by `n`. -/
theorem exists_flat_representative_of_isLE
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) (n : ℤ)
    (hE : E.IsLE n) :
    ∃ K : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ,
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
        (O := (smallEtaleRingedTopos B S hS Y).O) (K.X i)) ∧
      K.IsStrictlyLE n ∧ Nonempty (DerivedCategory.Q.obj K ≅ E) := by
  obtain ⟨M, hMLE, ⟨eM⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE E n
  let Pflat : ObjectProperty (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :=
    fun F => AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS Y).O) F
  have _ : Pflat.ContainsZero :=
    ⟨⟨⊥_ _, initialIsInitial.isZero, isFlat_of_isZero B S hS initialIsInitial.isZero⟩⟩
  have hcover : ∀ F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y),
      ∃ (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (_ : Pflat G)
        (g : G ⟶ F), Epi g := by
    intro F
    obtain ⟨G, g, hG, hg⟩ :=
      Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat_ofSize
        (smallEtaleRingedTopos B S hS Y).O F
    exact ⟨G, hG, g, hg⟩
  obtain ⟨P, g, -, _, hPflat, hPLE⟩ :=
    (CochainComplex.exists_quasiIso_prop Pflat hcover n).1 M
  exact ⟨P, hPflat, hPLE, ⟨asIso (DerivedCategory.Q.map g) ≪≫ eM.symm⟩⟩

/-- **The derived pullback along a morphism of algebraic spaces is right t-exact**: if the
cohomology of `E` vanishes in degrees `> n`, so does that of `Lf^*E`.  `E` is represented by a
complex of flat modules strictly bounded above by `n`, on which `Lf^*` is degreewise pullback. -/
theorem isLE_smallEtaleDerivedModulePullback_obj (f : X ⟶ Y)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) (n : ℤ)
    (hE : E.IsLE n) : ((smallEtaleDerivedModulePullback B S hS f).obj E).IsLE n := by
  obtain ⟨K, hflat, hKLE, ⟨e⟩⟩ := exists_flat_representative_of_isLE E n hE
  obtain ⟨e'⟩ := nonempty_smallEtaleDerivedModulePullback_obj_Q_iso f K n hflat
  have : CochainComplex.IsStrictlyLE
      ((((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) n :=
    Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isStrictlyLE_pullbackComplex
      (smallEtaleRingedToposHom B S hS f) K n
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (e'.symm ≪≫ (smallEtaleDerivedModulePullback B S hS f).mapIso e) n


end AlgebraicGeometry.Space

end
