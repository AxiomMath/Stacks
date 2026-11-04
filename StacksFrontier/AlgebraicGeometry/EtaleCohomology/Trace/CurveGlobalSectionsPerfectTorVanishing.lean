module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectTorsion

/-!
# The Tor vanishing for the global sections of a resolution on a curve

Let `X` be a curve over a field `k`, `k̄` an algebraically closed extension, `Y = X_{k̄}`, `Λ` a
finite ring, not necessarily commutative, and `G` a sheaf of `Λ`-modules on the small étale site
of `Y` with finite projective stalks. Let `G[0] ⟶ I` be an injective resolution in degrees
`≥ 0`, so that `M = Γ(Y, I)` computes `RΓ(Y, G)`. For a complex `R` of finite free right
`Λ`-modules concentrated in degrees `[e, c]` with `e ≤ -4`, exact in the degrees `p > e` other
than `0` — a truncated finite free resolution of a finite right module `N` — the total complex
`Tot(R ⊗[Λ] M)` has no cohomology in degree `-1`.

This is the Tor-dimension input of the proof of [Stacks, Tag 03TV]: `Tot(R ⊗[Λ] M)` is the
complex of global sections of the twist complex `R ⊠ I`, whose terms are acyclic and which is
exact in the degrees `e + 1, …, -1`; dimension shifting embeds its cohomology in degree `-1` into
`H^{-1-e}(Y, Z^e)` of its sheaf of cycles in degree `e`, which vanishes by Tag 0A53 since `Z^e` is
torsion and `-1 - e ≥ 3`.

## Main results

* `Stacks.SheafTwist.subsingleton_ext_twistComplex_cycles`: the cycles of `R ⊠ I` on `X_{k̄}` have
  no cohomology above degree two.
* `Stacks.SheafTwist.isZero_homology_mapBifunctor_moduleSections`: the Tor vanishing.

## References

* [Stacks Project, Tag 03TV](https://stacks.math.columbia.edu/tag/03TV)
* [Stacks Project, Tag 0A53](https://stacks.math.columbia.edu/tag/0A53)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Abelian HomologicalComplex
open StacksDraft.Perfect StacksDraft.Perfect.TorTotal

universe w u r

namespace Stacks.SheafTwist

variable {Λ : Type r} [Ring Λ] [Finite Λ] (D : BalancedDerivedTensoring.{r, max (u + 1) r} Λ)
  {k : Type u} [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
  (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosed kbar] (hcurve : IsCurve k g)

include hcurve in
/-- **The cycles of the twist complex on `X_{k̄}` have no cohomology above degree two**: they are
torsion, so Tag 0A53 applies. -/
lemma subsingleton_ext_twistComplex_cycles
    (R : CochainComplex (FiniteFree.{max (u + 1) r} Λ) ℤ)
    (I : CochainComplex (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar)) ℤ)
    [HasMapBifunctor R I (twist.{u, r} D (Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar))
      (ComplexShape.up ℤ)] (n : ℤ) (q : ℕ) (hq : 2 < q) :
    Subsingleton (Ext.{max (u + 1) r} (Stacks.EtaleSections.zSheaf.{r}
      (Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar))
      ((twistComplex D (Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar) R I).cycles n) q) :=
  (Stacks.EtaleCohomology.ProjectiveCurveBaseChange.torsionSheafSituation.{r} g kbar hcurve _
    (torsionSheafProperty_twistComplex_cycles D _ R I n)).isVanishingAboveDegreeTwo q hq

include hcurve in
/-- **The Tor vanishing for the global sections of an injective resolution on `X_{k̄}`.** Let `G`
have finite projective stalks and let `G[0] ⟶ I` be an injective resolution. For a complex `R` of
finite free right `Λ`-modules concentrated in degrees `[e, c]` with `e + 3 ≤ -1`, exact in the
degrees `p > e` other than `0`, the total complex `Tot(R ⊗[Λ] Γ(X_{k̄}, I))` has no cohomology in
degree `-1`. -/
theorem isZero_homology_mapBifunctor_moduleSections
    (G : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar))
    (hG : ∀ y : Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar,
      Module.Finite Λ (((geometricSitePoint.{u, r} _ y).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj G) ∧
      Module.Projective Λ (((geometricSitePoint.{u, r} _ y).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj G))
    (I : CochainComplex (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar)) ℤ) [∀ n, Injective (I.X n)]
    (ι : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G ⟶ I) [QuasiIso ι]
    (R : CochainComplex (ModuleCat.{max (u + 1) r} (MulOpposite Λ)) ℤ) (e c : ℤ)
    (hb : ∀ p, p < e ∨ c < p → IsZero (R.X p))
    (hfree : ∀ p, Module.Finite (MulOpposite Λ) (R.X p) ∧ Module.Free (MulOpposite Λ) (R.X p))
    (hR : ∀ p, e < p → p ≠ 0 → R.ExactAt p) (he : e + 3 ≤ -1)
    [HasMapBifunctor R (((moduleSections (Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar)
      ).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) D.ordinary (ComplexShape.up ℤ)] :
    IsZero ((mapBifunctor R (((moduleSections (Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar)
      ).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) D.ordinary (ComplexShape.up ℤ)).homology
        (-1)) := by
  let Y := Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar
  let R' := liftComplex.{u} R hfree
  let M' := ((moduleSections Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  have h' : ∀ p, p < e ∨ c < p → IsZero (R'.X p) := fun p hp =>
    IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι (finiteFree.{max (u + 1) r} Λ)) _
      (hb p hp)
  let K := ((twist.{u, r} D Y).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)).obj R' |>.obj I
  have : HasMapBifunctor R' I (twist.{u, r} D Y) (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_finite _ _ (finite_support_of_columnBounds K e c fun p hp =>
      isZero_of_forall_isZero_X fun q => ((twist.{u, r} D Y).map_isZero (h' p hp)).obj (I.X q))
  have : HasMapBifunctor R' M' (ObjectProperty.ι (finiteFree.{max (u + 1) r} Λ) ⋙ D.ordinary)
      (ComplexShape.up ℤ) := ‹HasMapBifunctor R M' D.ordinary (ComplexShape.up ℤ)›
  have : (HomologicalComplex₂.TotalMap.mapBicomplex (Stacks.EtaleSections.sections.{r, u} Y)
      K).HasTotal (ComplexShape.up ℤ) := HomologicalComplex₂.hasTotal_of_finite _ _
    (finite_support_of_columnBounds _ e c (fun p hp => isZero_of_forall_isZero_X fun q =>
      (Stacks.EtaleSections.sections.{r, u} Y).map_isZero
        (((twist.{u, r} D Y).map_isZero (h' p hp)).obj (I.X q))))
  let T := twistComplex D Y R' I
  let eX : ((forget₂ (ModuleCat.{max (u + 1) r} ℤ)
      AddCommGrpCat.{max (u + 1) r}).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (mapBifunctor R' M' (ObjectProperty.ι (finiteFree.{max (u + 1) r} Λ) ⋙ D.ordinary)
          (ComplexShape.up ℤ)) ≅
      StacksDraft.DimensionShift.homComplex (Stacks.EtaleSections.zSheaf.{r} Y) T :=
    (sectionsTwistComplexIso D Y R' I e c h').symm ≪≫
      Stacks.EtaleSections.sectionsComplexIso.{r} Y T
  let n := (-2 - e).toNat
  have hn : e + 1 + (n : ℤ) = -1 := by omega
  obtain ⟨f, hf⟩ := StacksDraft.DimensionShift.exists_injective_homology_ext
    (Stacks.EtaleSections.zSheaf.{r} Y) n T e
    (fun k hk => exactAt_twistComplex D Y R' e c h' G hG I ι (e + 1 + k) (by omega)
      (hR (e + 1 + k) (by omega) (by omega)))
    (fun k _ q => subsingleton_ext_twistComplex_X.{max (u + 1) r} Y D R' I e c h' (e + k) q)
  have hsub := subsingleton_ext_twistComplex_cycles D g kbar hcurve R' I e (n + 1) (by omega)
  have hz : IsZero ((StacksDraft.DimensionShift.homComplex
      (Stacks.EtaleSections.zSheaf.{r} Y) T).homology (-1)) := by
    rw [← hn]
    have := hf.subsingleton
    exact AddCommGrpCat.isZero_of_subsingleton _
  have hz' := hz.of_iso (HomologicalComplex.homologyMapIso eX (-1))
  rw [← exactAt_iff_isZero_homology] at hz' ⊢
  exact (ShortComplex.exact_map_iff_of_faithful _
    (forget₂ (ModuleCat.{max (u + 1) r} ℤ) AddCommGrpCat.{max (u + 1) r})).1 hz'

end Stacks.SheafTwist

end
