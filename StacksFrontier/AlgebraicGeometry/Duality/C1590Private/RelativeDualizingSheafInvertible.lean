module

public import StacksFrontier.AlgebraicGeometry.Duality.C1590Private.RelativeDualizingSheafShape
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.GorensteinDualizingInvertible
public import StacksFrontier.AlgebraicGeometry.FiberRank.FlatFibreFiniteFree
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantStalkRank
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantRank
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibreRankLocallyConstant
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Blowup.CentreConormalRank
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBaseChangeExcess
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFreeLocal
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankFromBasis

/-!
# The relative dualizing sheaf of a family of Gorenstein curves is invertible (Stacks 0E6R)

Let `f : X ⟶ S` be a proper, flat morphism of finite presentation over an affine scheme `S`
whose fibres are Gorenstein, equidimensional of dimension one. Then:

* `ω^•_{X/S} = a(𝒪_S)` has no cohomology above degree `-1` (Stacks 0E6P), so its cohomology sheaf
  `ω_{X/S} = H^{-1}(ω^•_{X/S})` commutes with arbitrary base change and restricts on each fibre
  `X_s` to the dualizing sheaf `ω_{X_s}` of Stacks 0BS2;
* `ω_{X/S}` is an invertible `𝒪_X`-module (Stacks 0E6R).

For invertibility, `ω_{X/S}` is finitely presented and flat over `S`, being the pullback of the
module `ω_V` of
`AlgebraicGeometry.C1590Private.exists_relativeDualizingComplex_iso_derivedPullback`, and its
restriction to a fibre `X_s` is the dualizing sheaf `ω_{X_s}`, which is invertible since `X_s` is
Gorenstein (Stacks 0BS6). By the fibrewise criterion of Stacks 080Q, `ω_{X/S}` is free of some
finite rank `n` near every point; pulling the trivialisation back to the fibre and comparing with
`ω_{X_s}` gives `n = 1`.

## Main results

* `AlgebraicGeometry.C1590Private.isLE_relativeDualizingComplex`: Stacks 0E6P, the vanishing.
* `AlgebraicGeometry.C1590Private.isFiniteLocallyFreeOfRank_relativeDualizingSheaf` and
  `AlgebraicGeometry.C1590Private.isInvertible_relativeDualizingSheaf`: Stacks 0E6R.
* `AlgebraicGeometry.C1590Private.relativeDualizingSheafFibreIso`: the restriction to a fibre.

## References

* [Stacks Project, Tag 0E6P](https://stacks.math.columbia.edu/tag/0E6P)
* [Stacks Project, Tag 0E6R](https://stacks.math.columbia.edu/tag/0E6R)
* [Stacks Project, Tag 080Q](https://stacks.math.columbia.edu/tag/080Q)
* [Stacks Project, Tag 0BS6](https://stacks.math.columbia.edu/tag/0BS6)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Duality TopologicalSpace

universe u

namespace AlgebraicGeometry.C1590Private

section Shift

variable {X V : Scheme.{u}} (g : X ⟶ V) (M : V.Modules)

/-- A module placed in degree `-1` has no cohomology above degree `-1`. -/
theorem isLE_singleFunctor_shift_one :
    (((DerivedCategory.singleFunctor V.Modules 0).obj M)⟦(1 : ℤ)⟧).IsLE (-1) :=
  DerivedCategory.TStructure.t.isLE_shift _ 0 1 (-1)

/-- The cohomology in degree `-1` of a module placed in degree `-1` is the module. -/
def homologySingleFunctorShiftOneIso :
    (DerivedCategory.homologyFunctor V.Modules (-1)).obj
        (((DerivedCategory.singleFunctor V.Modules 0).obj M)⟦(1 : ℤ)⟧) ≅ M :=
  eqToIso (by rw [← DerivedCategory.shift_homologyFunctor V.Modules (-1)]; rfl) ≪≫
    ((DerivedCategory.homologyFunctor V.Modules 0).shiftIso 1 (-1) 0 (by omega)).app
      ((DerivedCategory.singleFunctor V.Modules 0).obj M) ≪≫
    eqToIso (by rw [DerivedCategory.shift_homologyFunctor]; rfl) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso V.Modules 0).app M

/-- The cohomology in degree `-1` of the derived pullback of a module placed in degree `-1` is
the pullback of the module. -/
def homologyDerivedPullbackSingleShiftOneIso :
    (DerivedCategory.homologyFunctor X.Modules (-1)).obj ((Stacks.Duality.derivedPullback g).obj
        (((DerivedCategory.singleFunctor V.Modules 0).obj M)⟦(1 : ℤ)⟧)) ≅
      (Scheme.Modules.pullback g).obj M :=
  homologyDerivedPullbackTopDegreeIso g _ (-1) (isLE_singleFunctor_shift_one M) ≪≫
    (Scheme.Modules.pullback g).mapIso (homologySingleFunctorShiftOneIso M)

end Shift

/-- A module which is finite locally free of some rank is finite locally free. -/
theorem isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : _root_.SheafOfModules.{u} R) (r : ℕ)
    [h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F := by
  obtain ⟨q, hq, hr⟩ := h.exists_isFiniteLocallyFreeOfRankData
  exact ⟨q, hq, ⟨fun i => ⟨Finite.of_equiv _ (hr i).some.symm⟩⟩⟩

section Affine

variable {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) [IsProper f] [Flat f]
  [LocallyOfFinitePresentation f]

/-- **Stacks 0E6P: `ω^•_{X/S}` has no cohomology above degree `-1`**, for a family of curves
with Gorenstein fibres equidimensional of dimension one over an affine base. -/
theorem isLE_relativeDualizingComplex (h : HasGorensteinCurveFibres f) :
    (relativeDualizingComplex f).obj.IsLE (-1) := by
  obtain ⟨T, V, π, fV, gV, M, _, -, -, -, ⟨e⟩⟩ :=
    exists_relativeDualizingComplex_iso_derivedPullback f h
  have := isLE_derivedPullback_obj gV _ (-1) (isLE_singleFunctor_shift_one M)
  exact DerivedCategory.TStructure.t.isLE_of_iso e.symm (-1)

/-- **The relative dualizing sheaf restricts to the dualizing sheaf of each fibre** (Stacks 0E6Q):
for a family of curves with Gorenstein fibres equidimensional of dimension one over an affine
base, the pullback of `ω_{X/S}` to the fibre `X_s` is the dualizing sheaf `ω_{X_s}` of the proper
`κ(s)`-scheme `X_s` (Stacks 0BS2). -/
def relativeDualizingSheafFibreIso (h : HasGorensteinCurveFibres f) (s : S) :
    (Scheme.Modules.pullback (f.fiberι s)).obj (relativeDualizingSheaf f) ≅
      dualizingSheafOverField (k := S.residueField s) (f.fiberToSpecResidueField s) :=
  relativeDualizingSheafFibreIsoOfIsLE f (isLE_relativeDualizingComplex f h) s

/-- The relative dualizing sheaf is the pullback of a finitely presented module flat over a base,
along a cartesian square. -/
theorem exists_relativeDualizingSheaf_iso_pullback (h : HasGorensteinCurveFibres f) :
    ∃ (T V : Scheme.{u}) (π : S ⟶ T) (fV : V ⟶ T) (gV : X ⟶ V) (M : V.Modules)
      (_ : LocallyOfFinitePresentation fV),
      IsPullback gV f fV π ∧ M.IsFinitePresentation ∧
        IsFlatOver fV.toLRSHom.toShHom M ∧
        Nonempty (relativeDualizingSheaf f ≅ (Scheme.Modules.pullback gV).obj M) := by
  obtain ⟨T, V, π, fV, gV, M, hfp, sq, hM, hflat, ⟨e⟩⟩ :=
    exists_relativeDualizingComplex_iso_derivedPullback f h
  exact ⟨T, V, π, fV, gV, M, hfp, sq, hM, hflat,
    ⟨(DerivedCategory.homologyFunctor X.Modules (-1)).mapIso e ≪≫
      homologyDerivedPullbackSingleShiftOneIso gV M⟩⟩

/-- The relative dualizing sheaf is of finite presentation. -/
theorem isFinitePresentation_relativeDualizingSheaf (h : HasGorensteinCurveFibres f) :
    (relativeDualizingSheaf f).IsFinitePresentation := by
  obtain ⟨T, V, π, fV, gV, M, _, -, hM, -, ⟨e⟩⟩ := exists_relativeDualizingSheaf_iso_pullback f h
  exact (SheafOfModules.isFinitePresentation.{u, u, u} _).prop_of_iso e.symm
    (@Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ gV.toLRSHom.toShHom M hM)

/-- The relative dualizing sheaf is flat over the base. -/
theorem isFlatOverAt_relativeDualizingSheaf (h : HasGorensteinCurveFibres f) (x : X) :
    IsFlatOverAt f.toLRSHom.toShHom (relativeDualizingSheaf f) x := by
  obtain ⟨T, V, π, fV, gV, M, _, sq, hM, hflat, ⟨e⟩⟩ :=
    exists_relativeDualizingSheaf_iso_pullback f h
  exact (isFlatOverAt_iff_of_moduleIso _ e x).mpr (@modulePullback_isFlatOverAt _ _ _ _ _ _ _ _
    sq M (isQuasicoherent_of_isFinitePresentation M) x (hflat _))

omit [IsAffine S] [Flat f] [LocallyOfFinitePresentation f] in
/-- The dualizing sheaf of a fibre is invertible, of rank one. -/
theorem isFiniteLocallyFreeOfRank_one_dualizingSheafOverField_fibre
    (h : HasGorensteinCurveFibres f) (x : X) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (dualizingSheafOverField (k := S.residueField (f x)) (f.fiberToSpecResidueField (f x))) 1 :=
  have := (h x).1
  (isInvertible_dualizingSheafOverField_of_isGorenstein (k := S.residueField (f x))
    (f.fiberToSpecResidueField (f x)) inferInstance (h x).2.1 (h x).2.2).2

/-- **Stacks 0E6R: the relative dualizing sheaf is finite locally free of rank one**, for a
family of curves with Gorenstein fibres equidimensional of dimension one over an affine base. -/
theorem isFiniteLocallyFreeOfRank_relativeDualizingSheaf (h : HasGorensteinCurveFibres f) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (relativeDualizingSheaf f) 1 := by
  let F := relativeDualizingSheaf f
  have : F.IsFinitePresentation := isFinitePresentation_relativeDualizingSheaf f h
  have hfp : AlgebraicGeometry.FinitePresentation f := ⟨inferInstance, inferInstance, inferInstance⟩
  -- near every point `F` is free of some finite rank (Stacks 080Q)
  have hfree : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ n : ℕ,
      Nonempty (F.over U ≅ _root_.SheafOfModules.free (ULift.{u} (Fin n))) := by
    intro x
    let ωs := dualizingSheafOverField (k := S.residueField (f x)) (f.fiberToSpecResidueField (f x))
    have := isFiniteLocallyFreeOfRank_one_dualizingSheafOverField_fibre f h x
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} ωs :=
      isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank ωs 1
    have : ωs.IsQuasicoherent := inferInstance
    have h₁ : IsFlatOverAt (𝟙 (f.fiber (f x))).toLRSHom.toShHom ωs (f.asFiber x) :=
      VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree (𝟙 _) ωs _
    have h₂ := (isFlatOverAt_iff_of_moduleIso _ (relativeDualizingSheafFibreIso f h (f x))
      (f.asFiber x)).mpr h₁
    exact Scheme.Modules.exists_iso_free_over_of_flat_over_at_of_flat_fiber_stalk f hfp F x
      (isFlatOverAt_relativeDualizingSheaf f h x) ((isFlatOverAt_id_iff _ _).mp h₂)
  choose U hxU n e using hfree
  have hrank : ∀ x y : X, y ∈ U x → Scheme.Modules.fiberRank F y = n x := fun x y hy =>
    Scheme.Modules.fiberRank_eq_of_iso_free_over F (U x) (n x) (e x).some hy
  have hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F :=
    Stacks.SheafOfModules.LocalKernel.isFiniteLocallyFree_of_isOpenCover F U
      (IsOpenCover.mk (eq_top_iff.2 fun x _ => Opens.mem_iSup.2 ⟨x, hxU x⟩)) fun x =>
        have := AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_free
          (R := X.ringCatSheaf.over (U x)) (n x)
        have := isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank
          (_root_.SheafOfModules.free (R := X.ringCatSheaf.over (U x)) (ULift.{u} (Fin (n x))))
          (n x)
        Stacks.AlgebraicGeometry.isFiniteLocallyFree_of_iso (e x).some.symm
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_forall_fiberRank_eq F 1 fun x => ?_
  rw [hrank x x (hxU x)]
  let s := f x
  let ι := f.fiberι s
  let W : (f.fiber s).Opens := ι ⁻¹ᵁ U x
  have hpW : f.asFiber x ∈ W := by
    show ι (f.asFiber x) ∈ U x
    rw [f.fiberι_asFiber x]
    exact hxU x
  have hW₁ := Stacks.Chow.isFiniteLocallyFreeOfRank_modulePullback (ι ∣_ U x) _ (n x)
    (Scheme.Modules.isFiniteLocallyFreeOfRank_pullback_of_fiberRank_eq F (U x) (n x) (hrank x))
  let ωs := dualizingSheafOverField (k := S.residueField s) (f.fiberToSpecResidueField s)
  have hW₂ := Stacks.Chow.isFiniteLocallyFreeOfRank_modulePullback W.ι ωs 1
    (isFiniteLocallyFreeOfRank_one_dualizingSheafOverField_fibre f h x)
  let eW : (Scheme.Modules.pullback (ι ∣_ U x)).obj ((Scheme.Modules.pullback (U x).ι).obj F) ≅
      (Scheme.Modules.pullback W.ι).obj ωs :=
    (Scheme.Modules.pullbackComp (ι ∣_ U x) (U x).ι).app F ≪≫
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι ι (U x))).app F ≪≫
      ((Scheme.Modules.pullbackComp W.ι ι).app F).symm ≪≫
      (Scheme.Modules.pullback W.ι).mapIso (relativeDualizingSheafFibreIso f h s)
  exact Scheme.Modules.isFiniteLocallyFreeOfRank_unique _
    (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} eW hW₁) hW₂
    ⟨f.asFiber x, hpW⟩

/-- **Stacks 0E6R: the relative dualizing sheaf is invertible**, for a family of curves with
Gorenstein fibres equidimensional of dimension one over an affine base. -/
theorem isInvertible_relativeDualizingSheaf (h : HasGorensteinCurveFibres f) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (relativeDualizingSheaf f) :=
  Stacks.ModuleDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one X _
    (isFiniteLocallyFreeOfRank_relativeDualizingSheaf f h)

end Affine

end AlgebraicGeometry.C1590Private

end
