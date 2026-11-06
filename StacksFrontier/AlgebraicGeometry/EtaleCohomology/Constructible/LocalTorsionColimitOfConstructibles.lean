module

public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleLiftOverPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafSideConditions
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointSupport.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.AbelianShriekConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IntegerShriekPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleSheafPresentationColimits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShriekGeneratorConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactConstructibleAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionEtaleCohomology
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianWeakSerre
import StacksCore.Tactic.StacksAttribute

/-!
# Torsion étale sheaves as filtered colimits of constructible ones

Let `X` be a quasi-compact and quasi-separated scheme. Every torsion abelian sheaf on the small
étale site of `X` is a filtered colimit of constructible abelian sheaves. This is part (2) of
Stacks 03SA; parts (1) and (3), for sheaves of sets and for sheaves of modules over a Noetherian
ring, are `AlgebraicGeometry.exists_isFilteredColimit_isConstructibleSetSheaf_of_qcqs` and
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleModuleSheaf_of_qcqs`.

"Torsion" is the local condition of Stacks 0DD7, `Stacks.Torsion.torsionSheafProperty`: every
section becomes annihilated by a positive integer after restriction along the arrows of a covering
sieve, the integer being allowed to vary over the sieve. That is the condition under which the
source's `𝓕 = ⋃ 𝓕[n]` holds in the category of sheaves. The pointwise condition
`AlgebraicGeometry.IsTorsionAbelianSheaf` implies it
(`AlgebraicGeometry.torsionSheafProperty_of_isTorsionAbelianSheaf`), so the statement at the local
condition is the stronger one.

## The route taken

The source reduces part (2) to part (3): a torsion abelian sheaf `F` is the union of its
`n`-torsion subsheaves `F[n]`, each `F[n]` is a sheaf of `ℤ/nℤ`-modules, and `ℤ/nℤ` is Noetherian.
The reduction carried out here is the same one with `ℤ/nℤ` replaced by `ℤ` and the passage to
`ℤ/nℤ`-modules replaced by division by `n` *after* part (3) has been applied, in three steps.

1. **The torsion filtration.** `Stacks.Torsion.isIso_torsionFiltrationDesc` writes `F` as the
   colimit over `n` of the kernels `F[n!]` of multiplication by `n!` — the union `𝓕 = ⋃ 𝓕[d]` of
   Stacks 0DDC, at exactly the local torsion condition of Stacks 0DD7. So it is enough to show
   that an abelian sheaf *annihilated by a positive integer* `n` is a filtered colimit of
   constructible sheaves.
2. **Part (3) and division by `n`.** An abelian sheaf is a sheaf of `ULift ℤ`-modules, by
   `AddCommGrpCat.moduleCatUliftIntEquivalence`, and `ULift ℤ` is a Noetherian ring in
   `Type (u + 1)`, which is where part (3) is stated. So part (3) writes the sheaf of
   `ULift ℤ`-modules attached to `F` as a filtered colimit of constructible ones, `F = colim Nᵢ`.
   Dividing the whole diagram by `n` changes neither the colimit — `n` already annihilates `F` —
   nor the constructibility of the terms, constructibility being a weak Serre condition
   (Stacks 03RZ (3)). What it gains is that every term is annihilated by `n`, which turns the
   *finite generation* of its local values into *finiteness* (Stacks 093U (2), in the form
   `Stacks.ConstantSheaf.isFiniteLocallyConstant_of_isFiniteTypeLocallyConstantModuleSheaf`).
3. **Collapsing the two colimits.** Steps 1 and 2 exhibit `F` as a filtered colimit of filtered
   colimits of constructible sheaves. `CategoryTheory.ObjectProperty.ind_ind` collapses that into
   a single filtered colimit, given that a constructible abelian sheaf is a compact object —
   Stacks 09Z4, `AlgebraicGeometry.isFinitelyPresentable_of_isConstructibleAbelianSheaf`, with
   its Stacks 095N input discharged by
   `AlgebraicGeometry.hasFiniteShriekPresentation_of_isConstructibleModuleSheaf_int`.

Every input above is a theorem of the library.

## Main results

* `AlgebraicGeometry.ind_isConstructibleAbelianSheaf_of_torsionSheafProperty` — part (2) in the
  `CategoryTheory.ObjectProperty.ind` spelling.
* `AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf_of_qcqs`
  — **Stacks 03SA (2)**, in the diagram-and-cocone spelling of parts (1) and (3).

## Implementation notes

The coefficient universe is `AddCommGrpCat.{u + 1}`, as for the abelian sheaves of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles`. Division by
`n` is `moduloFunctor`, the cokernel of multiplication by `n`, with `moduloCoconeIsColimit` for the
statement that it leaves a colimit already annihilated by `n` alone; both are stated for an
arbitrary preadditive category with cokernels.

## References

* [Stacks Project, Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)
* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 09Z4](https://stacks.math.columbia.edu/tag/09Z4)
* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
* [Stacks Project, Tag 0DDC](https://stacks.math.columbia.edu/tag/0DDC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry


/-! ### Division by an integer -/

section Modulo

universe uC vC uI vI

private theorem nsmul_id_comm {C : Type uC} [Category.{vC} C] [Preadditive C]
    {M N : C} (f : M ⟶ N) (n : ℕ) :
    (n • 𝟙 M) ≫ f = f ≫ (n • 𝟙 N) := by
  rw [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasCokernels C]

/-- `M ↦ M/nM`, the cokernel of multiplication by `n`. -/
private def moduloFunctor (n : ℕ) : C ⥤ C where
  obj M := cokernel (n • 𝟙 M)
  map {M N} f := cokernel.desc _ (f ≫ cokernel.π (n • 𝟙 N)) (by
    rw [← Category.assoc, nsmul_id_comm f n, Category.assoc, cokernel.condition, comp_zero])
  map_id M := by
    apply (cancel_epi (cokernel.π (n • 𝟙 M))).1
    rw [cokernel.π_desc, Category.comp_id, Category.id_comp]
  map_comp {M N P} f g := by
    apply (cancel_epi (cokernel.π (n • 𝟙 M))).1
    rw [cokernel.π_desc, ← Category.assoc, cokernel.π_desc, Category.assoc, Category.assoc,
      cokernel.π_desc]

/-- The projection `M ⟶ M/nM`. -/
private def moduloProjection (n : ℕ) : 𝟭 C ⟶ moduloFunctor (C := C) n where
  app M := cokernel.π (n • 𝟙 M)
  naturality _ _ _ := (cokernel.π_desc _ _ _).symm

private theorem epi_moduloProjection (n : ℕ) (M : C) : Epi ((moduloProjection n).app M) :=
  (inferInstance : Epi (cokernel.π (n • 𝟙 M)))

private theorem nsmul_id_cokernel (n : ℕ) (M : C) :
    n • 𝟙 (cokernel (n • 𝟙 M)) = 0 := by
  apply (cancel_epi (cokernel.π (n • 𝟙 M))).1
  rw [comp_zero, (nsmul_id_comm (cokernel.π (n • 𝟙 M)) n).symm, cokernel.condition]

private theorem nsmul_id_moduloFunctor (n : ℕ) (M : C) :
    n • 𝟙 ((moduloFunctor n).obj M) = 0 := nsmul_id_cokernel n M

/-- A map out of `M` killing `n` factors through `M/nM`. -/
private def moduloDesc (n : ℕ) {M Y : C} (g : M ⟶ Y) (h : n • 𝟙 Y = 0) :
    (moduloFunctor n).obj M ⟶ Y :=
  cokernel.desc (n • 𝟙 M) g (by rw [nsmul_id_comm g n, h, comp_zero])

private theorem moduloProjection_moduloDesc (n : ℕ) {M Y : C} (g : M ⟶ Y) (h : n • 𝟙 Y = 0) :
    (moduloProjection n).app M ≫ moduloDesc n g h = g :=
  cokernel.π_desc _ _ _

/-- The legs of the cocone, out of the diagram divided by `n`, at a point killed by `n`. -/
private def moduloCoconeι {I : Type uI} [Category.{vI} I] {D : I ⥤ C} (n : ℕ)
    (c : Cocone D) (h : n • 𝟙 c.pt = 0) :
    (D ⋙ moduloFunctor n) ⟶ (Functor.const I).obj c.pt where
  app i := moduloDesc n (c.ι.app i) h
  naturality i j f := by
    have := epi_moduloProjection n (D.obj i)
    apply (cancel_epi ((moduloProjection n).app (D.obj i))).1
    have hn := (moduloProjection n).naturality (D.map f)
    simp only [Functor.id_map] at hn
    simp only [Functor.comp_map, Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
    rw [← Category.assoc, ← hn, Category.assoc, moduloProjection_moduloDesc,
      moduloProjection_moduloDesc]
    exact c.w f

private theorem moduloProjection_moduloCoconeι {I : Type uI} [Category.{vI} I] {D : I ⥤ C}
    (n : ℕ) (c : Cocone D) (h : n • 𝟙 c.pt = 0) (i : I) :
    (moduloProjection n).app (D.obj i) ≫ (moduloCoconeι n c h).app i = c.ι.app i :=
  moduloProjection_moduloDesc n (c.ι.app i) h

/-- Dividing a filtered colimit by `n` changes nothing when `n` already kills the colimit. -/
private def moduloCoconeIsColimit {I : Type uI} [Category.{vI} I] {D : I ⥤ C} (n : ℕ)
    (c : Cocone D) (h : n • 𝟙 c.pt = 0) (hc : IsColimit c) :
    IsColimit (Cocone.mk c.pt (moduloCoconeι n c h)) where
  desc s := hc.desc
    { pt := s.pt
      ι :=
        { app i := (moduloProjection n).app (D.obj i) ≫ s.ι.app i
          naturality i j f := by
            have hn := (moduloProjection n).naturality (D.map f)
            simp only [Functor.id_map] at hn
            have h₂ := s.w f
            simp only [Functor.comp_map, Functor.const_obj_obj, Functor.const_obj_map,
              Category.comp_id] at h₂ ⊢
            rw [← Category.assoc, hn, Category.assoc, h₂] } }
  fac s i := by
    have := epi_moduloProjection n (D.obj i)
    rw [← cancel_epi ((moduloProjection n).app (D.obj i)), ← Category.assoc,
      moduloProjection_moduloCoconeι]
    exact hc.fac _ i
  uniq s m hm := by
    refine hc.hom_ext fun i => ?_
    rw [hc.fac, ← moduloProjection_moduloCoconeι n c h i, Category.assoc, hm i]

end Modulo


/-! ### Side conditions -/

section Side

universe uA vA uB vB uC2 vC2

private theorem additive_sheafCompose {C : Type uC2} [Category.{vC2} C]
    (J : GrothendieckTopology C)
    {A : Type uA} [Category.{vA} A] [Preadditive A]
    {Bc : Type uB} [Category.{vB} Bc] [Preadditive Bc]
    (T : A ⥤ Bc) [T.Additive] [J.HasSheafCompose T] : (sheafCompose J T).Additive where
  map_add := by
    intro X Y f g
    ext U
    exact T.map_add

private theorem ofArrows_self_mem {C : Type uC2} [Category.{vC2} C]
    (J : GrothendieckTopology C) (U : C) :
    Sieve.ofArrows (fun _ : PUnit.{max uC2 vC2 + 1} => U) (fun _ => 𝟙 U) ∈ J U := by
  refine J.superset_covering ?_ (J.top_mem U)
  intro Y f _
  exact ⟨U, f, 𝟙 U, ⟨PUnit.unit⟩, Category.comp_id f⟩

end Side

/-! ### Kernels -/

section Kernels

universe uC vC

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasKernels C]

private theorem nsmul_id_kernel (n : ℕ) (M : C) :
    n • 𝟙 (kernel (n • 𝟙 M)) = 0 := by
  apply (cancel_mono (kernel.ι (n • 𝟙 M))).1
  rw [zero_comp, nsmul_id_comm (kernel.ι (n • 𝟙 M)) n, kernel.condition]

end Kernels

/-- An additive functor sends an object killed by `n` to an object killed by `n`. -/
private theorem nsmul_id_map_eq_zero {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (T : C ⥤ D) [T.Additive] {M : C} {n : ℕ} (h : n • 𝟙 M = 0) :
    n • 𝟙 (T.obj M) = 0 := by
  simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] using
    congrArg T.map h

/-! ### Torsion abelian étale sheaves -/
variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- Abelian sheaves on the small étale site read as sheaves of `ULift ℤ`-modules. -/
private abbrev uliftIntSheafEquivalence (Z : B.Scheme) :
    Sheaf (SmallEtale.topology B Z.obj Z.property) AddCommGrpCat.{u + 1} ≌
      Sheaf (SmallEtale.topology B Z.obj Z.property) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) :=
  Sheaf.coefficientEquivalence (SmallEtale.topology B Z.obj Z.property)
    AddCommGrpCat.moduleCatUliftIntEquivalence.{u + 1, u + 1}

private theorem additive_uliftIntSheafEquivalence_functor (Z : B.Scheme) :
    (uliftIntSheafEquivalence B Z).functor.Additive := by
  have : AddCommGrpCat.moduleCatUliftIntEquivalence.{u + 1, u + 1}.functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  exact additive_sheafCompose _ _

private theorem additive_uliftIntSheafEquivalence_inverse (Z : B.Scheme) :
    (uliftIntSheafEquivalence B Z).inverse.Additive := by
  have : AddCommGrpCat.moduleCatUliftIntEquivalence.{u + 1, u + 1}.inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  exact additive_sheafCompose _ _

/-- An abelian étale sheaf annihilated by a positive integer is locally annihilated. -/
private theorem isLocallyAnnihilated_of_nsmul_id_eq_zero (Z : B.Scheme) (n : ℕ) (hn : n ≠ 0)
    (F : Sheaf (SmallEtale.topology B Z.obj Z.property) AddCommGrpCat.{u + 1})
    (hzero : n • 𝟙 F = 0) :
    Stacks.ConstantSheaf.IsLocallyAnnihilated.{u, u + 1, 0}
      (SmallEtale.topology B Z.obj Z.property) F := by
  intro U
  refine ⟨PUnit.{u + 2}, fun _ => U, fun _ => 𝟙 U,
    ofArrows_self_mem (SmallEtale.topology B Z.obj Z.property) U, fun _ => ⟨n, hn, ?_⟩⟩
  exact nsmul_id_map_eq_zero ((SmallEtale.topology B Z.obj Z.property).overPullback
    AddCommGrpCat.{u + 1} U) hzero

/-- **The local step.** An abelian étale sheaf annihilated by a positive integer whose attached
sheaf of `ULift ℤ`-modules is locally constant of finite type is finite locally constant: finite
generation over `ℤ` together with annihilation by a positive integer forces the local values to
be finite. -/
private theorem isFiniteLocallyConstant_of_nsmul_id_eq_zero (Z : B.Scheme) (n : ℕ) (hn : n ≠ 0)
    (F : Sheaf (SmallEtale.topology B Z.obj Z.property) AddCommGrpCat.{u + 1})
    (hzero : n • 𝟙 F = 0)
    (Q : Sheaf (SmallEtale.topology B Z.obj Z.property)
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
    (eQ : (sheafCompose (SmallEtale.topology B Z.obj Z.property)
      AddCommGrpCat.moduleCatUliftIntEquivalence.{u + 1, u + 1}.functor).obj F ≅ Q)
    (hQ : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ULift.{u + 1} ℤ)
      (SmallEtale.topology B Z.obj Z.property) Q) :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant
      (SmallEtale.topology B Z.obj Z.property) F := by
  let : ∀ V : SmallEtale B Z.obj Z.property,
      HasSheafify ((SmallEtale.topology B Z.obj Z.property).over V) (ModuleCat.{u + 1} ℤ) :=
    fun V => Stacks.ModuleSheaf.hasSheafify_over_moduleCat.{u + 1, 0, u + 1, u} ℤ
      (SmallEtale.topology B Z.obj Z.property) V
  refine Stacks.ConstantSheaf.isFiniteLocallyConstant_of_isFiniteTypeLocallyConstantModuleSheaf.{u,
    u + 1, 0} _ F ?_ (isLocallyAnnihilated_of_nsmul_id_eq_zero B Z n hn F hzero)
  refine Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_of_coefficientEquivalence
    (SmallEtale.topology B Z.obj Z.property)
    ModuleCat.restrictScalarsUliftIntEquivalence.{u + 1, u + 1}.symm
    (fun M => ModuleCat.isFG (ULift.{u + 1} ℤ) M) (fun M hM => ?_) Q hQ _ ?_
  · have := (ModuleCat.isFG_iff M).1 hM
    exact (ModuleCat.isFG_iff _).2
      (ModuleCat.moduleFinite_restrictScalars_of_ringEquiv (ULift.ringEquiv (R := ℤ)).symm M)
  · exact (sheafCompose (SmallEtale.topology B Z.obj Z.property)
      ModuleCat.restrictScalarsUliftIntEquivalence.{u + 1, u + 1}.inverse).mapIso eQ.symm ≪≫
      ((Sheaf.coefficientEquivalence (SmallEtale.topology B Z.obj Z.property)
      ModuleCat.restrictScalarsUliftIntEquivalence.{u + 1, u + 1}).unitIso.app
        ((Stacks.ConstantSheaf.intSheaf.{u, u + 1, 0}
          (SmallEtale.topology B Z.obj Z.property)).obj F)).symm

/-- **The pieces are constructible.** The quotient by `n` of a constructible sheaf of
`ULift ℤ`-modules, read back as an abelian sheaf, is a constructible abelian sheaf: it is
constructible as a sheaf of modules because constructibility is a weak Serre condition, and it is
annihilated by `n`, which turns finite generation of its local values into finiteness. -/
private theorem isConstructibleAbelianSheaf_inverse_modulo (n : ℕ) (hn : n ≠ 0)
    (N : Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
    (hN : IsConstructibleModuleSheaf B X (ULift.{u + 1} ℤ) N) :
    IsConstructibleAbelianSheaf B X
      ((uliftIntSheafEquivalence B X).inverse.obj ((moduloFunctor n).obj N)) := by
  let := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B X (ULift.{u + 1} ℤ)
  have := additive_uliftIntSheafEquivalence_inverse B X
  have := SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, u + 1} B X
    (ULift.{u + 1} ℤ)
  have hNu : IsConstructibleModuleSheaf B X (ULift.{u + 1} ℤ) ((moduloFunctor n).obj N) :=
    ObjectProperty.prop_cokernel _ (n • 𝟙 N) hN hN
  have hGzero : n • 𝟙 ((uliftIntSheafEquivalence B X).inverse.obj
      ((moduloFunctor n).obj N)) = 0 := by
    exact nsmul_id_map_eq_zero (uliftIntSheafEquivalence B X).inverse
      (nsmul_id_moduloFunctor n N)
  intro U
  obtain ⟨s, hs⟩ := hNu U
  refine ⟨s, fun i => isFiniteLocallyConstant_of_nsmul_id_eq_zero B (s.piece i) n hn _ ?_ _ ?_
    (hs i)⟩
  · exact nsmul_id_map_eq_zero ((smallEtaleBaseChange B (s.inclusion i)).sheafPullback
      AddCommGrpCat.{u + 1} (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property)) hGzero
  · exact (Sheaf.sheafPullbackCoefficientIso (smallEtaleBaseChange B (s.inclusion i))
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
      AddCommGrpCat.moduleCatUliftIntEquivalence.{u + 1, u + 1}).app _ ≪≫
      ((smallEtaleBaseChange B (s.inclusion i)).sheafPullback
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).mapIso
        ((uliftIntSheafEquivalence B X).counitIso.app ((moduloFunctor n).obj N))

section Compact

variable [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]

/-- An abelian étale sheaf annihilated by a positive integer is a filtered colimit of
constructible abelian sheaves. -/
@[sga "4½ Arcata 4.3.3" "special case"]
private theorem ind_isConstructibleAbelianSheaf_of_nsmul_id_eq_zero (n : ℕ) (hn : n ≠ 0)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hzero : n • 𝟙 F = 0) :
    ObjectProperty.ind.{u + 1}
      (fun G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1} =>
        IsConstructibleAbelianSheaf B X G) F := by
  let := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B X (ULift.{u + 1} ℤ)
  have := additive_uliftIntSheafEquivalence_functor B X
  obtain ⟨I, hI, hfilt, D, ι, ⟨hc⟩, hD⟩ :=
    exists_isFilteredColimit_isConstructibleModuleSheaf B X (ULift.{u + 1} ℤ)
      (moduleSheavesAreFilteredColimitsOfPresentations B X (ULift.{u + 1} ℤ))
      (fun W hW => by
        have hWc : CompactSpace W.obj.left.obj := hW.1
        have hWq : QuasiSeparatedSpace W.obj.left.obj := hW.2
        exact isConstructibleModuleSheaf_moduleShriekConstant B X (ULift.{u + 1} ℤ) W)
      ((uliftIntSheafEquivalence B X).functor.obj F)
  have hMu : n • 𝟙 ((uliftIntSheafEquivalence B X).functor.obj F) = 0 :=
    nsmul_id_map_eq_zero (uliftIntSheafEquivalence B X).functor hzero
  exact ⟨I, hI, hfilt,
    (((⟨D ⋙ moduloFunctor n, moduloCoconeι n (Cocone.mk _ ι) hMu,
      moduloCoconeIsColimit n (Cocone.mk _ ι) hMu hc⟩ :
        ColimitPresentation I ((uliftIntSheafEquivalence B X).functor.obj F)).map
          (uliftIntSheafEquivalence B X).inverse).ofIso
            ((uliftIntSheafEquivalence B X).unitIso.app F).symm),
    fun i => isConstructibleAbelianSheaf_inverse_modulo B X n hn (D.obj i) (hD i)⟩

/-- **Stacks 03SA (2), in the `ObjectProperty.ind` spelling.** Let `X` be a quasi-compact and
quasi-separated scheme and let `F` be a torsion abelian sheaf on `X_étale`, torsion in the local
sense of Stacks 0DD7. Then `F` is a filtered colimit of constructible abelian sheaves.

`CategoryTheory.ObjectProperty.ind P F` is by definition the assertion that `F` is the point of a
colimit cocone over a small filtered diagram whose terms satisfy `P`. The proof is the three-step
reduction to part (3) described in the module documentation. -/
@[sga "4 IX 2.7.2" "special case",
  sga "4 XVIII 3.1.1" "Torsion abelian clause",
  sga "4½ Arcata 4.3.3" "more general"]
public theorem ind_isConstructibleAbelianSheaf_of_torsionSheafProperty
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty
      (SmallEtale.topology B X.obj X.property) F) :
    ObjectProperty.ind.{u + 1}
      (fun G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1} =>
        IsConstructibleAbelianSheaf B X G) F := by
  let := SmallEtale.isGrothendieckAbelian_sheaf_succ B X.obj X.property
  let : ∀ (S T : B.Scheme) (g : T ⟶ S),
      ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{u + 1} ℤ)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint :=
    fun S T g => Sheaf.isRightAdjoint_sheafPushforwardContinuous_of_coefficientEquivalence
      (smallEtaleBaseChange B g) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property) AddCommGrpCat.moduleCatIntEquivalence.{u + 1}
  let : ∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} ℤ) :=
    fun T V => Stacks.ModuleSheaf.hasSheafify_over_moduleCat.{u + 1, 0, u + 1, u} ℤ
      (SmallEtale.topology B T.obj T.property) V
  have hFP : (fun G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1} =>
      IsConstructibleAbelianSheaf B X G) ≤
      ObjectProperty.isFinitelyPresentable.{u + 1} _ := fun G hG =>
    isFinitelyPresentable_of_isConstructibleAbelianSheaf B X
      (hasFiniteShriekPresentation_of_isConstructibleModuleSheaf_int B X) G hG
  have hstage (m : ULift.{u + 1, 0} ℕ) :
      ObjectProperty.ind.{u + 1}
        (fun G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1} =>
          IsConstructibleAbelianSheaf B X G)
        ((Stacks.Torsion.torsionFiltration
          (SmallEtale.topology B X.obj X.property) F).obj m) :=
    ind_isConstructibleAbelianSheaf_of_nsmul_id_eq_zero B X (Nat.factorial m.down)
      (Nat.factorial_ne_zero _) _ (nsmul_id_kernel (Nat.factorial m.down) F)
  have h : ObjectProperty.ind.{u + 1} (ObjectProperty.ind.{u + 1}
      (fun G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1} =>
        IsConstructibleAbelianSheaf B X G)) F := ObjectProperty.of_essentiallySmall_index
    (⟨Stacks.Torsion.torsionFiltration (SmallEtale.topology B X.obj X.property) F,
      Stacks.Torsion.torsionFiltrationι (SmallEtale.topology B X.obj X.property) F, by
        have : IsIso (Stacks.Torsion.torsionFiltrationDesc
            (SmallEtale.topology B X.obj X.property) F) :=
          Stacks.Torsion.isIso_torsionFiltrationDesc _ F hF
        exact IsColimit.ofIsoColimit (colimit.isColimit _)
          (Cocone.ext (asIso (Stacks.Torsion.torsionFiltrationDesc
            (SmallEtale.topology B X.obj X.property) F))
            (fun j => Stacks.Torsion.ι_torsionFiltrationDesc _ F j))⟩ :
      ColimitPresentation (ULift.{u + 1, 0} ℕ) F) hstage
  exact (ObjectProperty.ind_ind hFP).le F h

/-- **Stacks 03SA (2).** Let `X` be a quasi-compact and quasi-separated scheme and let `F` be a
torsion abelian sheaf on `X_étale`. Then `F` is a filtered colimit of constructible abelian
sheaves.

The torsion condition is the local one of Stacks 0DD7, `Stacks.Torsion.torsionSheafProperty`:
every section is annihilated by a positive integer after restriction along the arrows of a
covering sieve. The colimit is taken in the category of abelian sheaves on `X_étale`, over a small
filtered index category, and the terms are constructible in the sense of Stacks 03RW (2). This is
`AlgebraicGeometry.ind_isConstructibleAbelianSheaf_of_torsionSheafProperty` in the
diagram-and-cocone spelling of parts (1) and (3). -/
@[stacks 03SA "part (2), torsion abelian sheaves, torsion in the local sense of Stacks 0DD7",
  sga "4½ Arcata 4.3.3" "more general"]
public theorem exists_isFilteredColimit_isConstructibleAbelianSheaf_of_qcqs
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty (SmallEtale.topology B X.obj X.property) F) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
      (ι : D ⟶ (Functor.const I).obj F), Nonempty (IsColimit (Cocone.mk F ι)) ∧
        ∀ i, IsConstructibleAbelianSheaf B X (D.obj i) := by
  obtain ⟨I, hI, hfilt, pres, hpres⟩ :=
    ind_isConstructibleAbelianSheaf_of_torsionSheafProperty B X F hF
  exact ⟨I, hI, hfilt, pres.diag, pres.ι, ⟨pres.isColimit⟩, hpres⟩

end Compact

end AlgebraicGeometry

end
