module

public import StacksFrontier.AlgebraicGeometry.DerivedIso.Transport
public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.BaseChangeDerived
public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.Affine
public import StacksFrontier.AlgebraicGeometry.Etale.FlatFiniteTypeNeighborhood
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteFlatLocallyFree
public import StacksFrontier.Algebra.Homology.StupidTruncationRetract
public import StacksFrontier.CategoryTheory.Sites.CechComplexSortingHomotopy
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfRingedTopoi
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedFlatRepresentative

/-!
# The relative Čech complex of a module flat over the base is K-flat

The relative Čech complex of a quasi-coherent module flat over the base, for an affine cover,
consists of modules flat over the base, so that derived pullback along the base is computed on
it termwise.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeCech Stacks.AlgebraicGeometry.RelativeCechComplex

universe u

namespace Stacks.AlgebraicGeometry.FlatSourceBaseChange

noncomputable section

variable {X S : Scheme.{u}}

/-- An object of `Over X` whose structure morphism is a monomorphism is subterminal. -/
theorem isSubterminal_of_mono_hom {A : Over X} (hm : Mono A.hom) : IsSubterminal A :=
  fun _ h₁ h₂ => over_hom_unique hm h₁ h₂

/-- The members of an affine open cover are subterminal objects of `Over X`. -/
theorem isSubterminal_overMk_affineOpenCover (T : X.AffineOpenCover.{u, u}) (i : T.I₀) :
    IsSubterminal (Over.mk (T.f i)) :=
  isSubterminal_of_mono_hom (inferInstanceAs (Mono (T.f i)))

/-- A finite product, in `Over X`, of objects whose structure morphisms are open immersions has
an open immersion as structure morphism. -/
theorem isOpenImmersion_pi_hom {α : Type} [Finite α] (V : α → Over X)
    [∀ a, IsOpenImmersion (V a).hom] [HasProduct V] : IsOpenImmersion (∏ᶜ V).hom := by
  let e : ∏ᶜ V ≅ (openImmersionFan V).pt :=
    limit.isoLimitCone ⟨_, isLimitOpenImmersionFan V⟩
  rw [← Over.w e.hom]
  show IsOpenImmersion (e.hom.left ≫ (commonOpen V).ι)
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget X).map e.hom))
  exact @IsOpenImmersion.comp _ _ _ e.hom.left (commonOpen V).ι
    (IsOpenImmersion.of_isIso _) (Scheme.Opens.instIsOpenImmersionι _)

/-- **A finite product of flat modules on a scheme is flat**: it is a finite biproduct, hence the
corresponding coproduct, and a coproduct of flat modules is flat. -/
theorem isFlat_pi {ι : Type u} [Finite ι] (G : ι → S.Modules)
    (hG : ∀ i, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := S.sheaf) (G i)) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := S.sheaf) (∏ᶜ G) := by
  have := Fintype.ofFinite ι
  have : HasFiniteBiproducts S.Modules := HasFiniteBiproducts.of_hasFiniteProducts
  exact AlgebraicGeometry.SheafOfModules.IsFlat.of_iso S.sheaf
    ((biproduct.isoCoproduct G).symm ≪≫ biproduct.isoProduct G)
    (Stacks.SheafOfModules.FlatCoproduct.isFlat_coproduct.{u, u} (O := S.sheaf) G hG)

/-- **The value of the relative Čech coefficient presheaf at an open subscheme affine over the
base is flat**, for a module flat over the base: it is the direct image along an affine morphism
of the restriction of the module, which is flat over the base, and flatness over a base passes to
the direct image along an affine morphism ([Stacks, Tag 0FLM]); over the base itself, flatness
over the identity is flatness. -/
theorem isFlat_relativeCechPresheaf_obj (f : X ⟶ S)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (hF : IsFlatOver f.toLRSHom.toShHom F.obj) (A : Over X) [IsOpenImmersion A.hom]
    [IsAffineHom (A.hom ≫ f)] :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := S.sheaf)
      (((relativeCechPresheaf f).obj F).obj (op A)) := by
  rw [relativeCechPresheaf_obj_obj, ← isFlatOver_id_iff_isFlat]
  have : ((Scheme.Modules.pullback A.hom).obj F.obj).IsQuasicoherent :=
    AffineBaseChange.isQuasicoherent_pullback _ F.obj
  have h := (isFlatOver_pushforward_iff (A.hom ≫ f) (𝟙 S)
    ((Scheme.Modules.pullback A.hom).obj F.obj)).1
  rw [Category.comp_id] at h
  exact h fun a =>
    (isFlatOverAt_pullback_iff_of_isFlatAt A.hom f F.obj a (Flat.stalkMap A.hom a)).1 (hF (A.hom a))

/-- **The value of the absolute Čech coefficient presheaf at an open subscheme affine over `X` is
flat**, for a flat module: the direct image along an affine flat morphism of a flat module is
flat ([Stacks, Tag 0FLM] over the base `X` itself). -/
theorem isFlat_absoluteCechPresheaf_obj
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) F.obj)
    (A : Over X) [IsOpenImmersion A.hom] [IsAffineHom A.hom] :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      (((CechPushforwardComplex.absoluteCechPresheaf X).obj F).obj (op A)) := by
  refine (isFlatOver_id_iff_isFlat _).1 ?_
  replace hF := (isFlatOver_id_iff_isFlat _).2 hF
  have : ((Scheme.Modules.pullback A.hom).obj F.obj).IsQuasicoherent :=
    AffineBaseChange.isQuasicoherent_pullback _ F.obj
  exact (isFlatOver_pushforward_iff A.hom (𝟙 X) ((Scheme.Modules.pullback A.hom).obj F.obj)).1
    fun a => (isFlatOverAt_pullback_iff_of_isFlatAt A.hom (𝟙 X) F.obj a
      (Flat.stalkMap A.hom a)).1 (hF (A.hom a))

section Retract

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The derived pullback of a complex homotopic to a truncation of itself through flat terms
is computed termwise.** If `e : C ⟶ C` is homotopic to the identity, vanishes above degree `N`,
and the terms of `C` in degrees `≤ N` are flat, then `C` is, in the homotopy category, a retract
of the bounded above complex of flat modules `σ^{≤N}C`, which is K-flat; the comparison
`Lg^*C ⟶ g^*C` is therefore invertible. -/
theorem isIso_derivedPullbackComparison_of_homotopy {Y Y' : RingedSpace.{u, u}} (g : Y' ⟶ Y)
    (C : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) (e : C ⟶ C) (N : ℤ)
    (he : ∀ n, N < n → e.f n = 0) (H : Homotopy e (𝟙 C))
    (hflat : ∀ n, n ≤ N → AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf)
      (C.X n)) :
    IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison g).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C)) := by
  let D := C.stupidTrunc (ComplexShape.embeddingUpIntLE N)
  have hD : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) (D.X n) := by
    intro n
    by_cases hn : n ≤ N
    · exact AlgebraicGeometry.SheafOfModules.IsFlat.of_iso Y.sheaf
        (StacksDraft.StupidTruncation.stupidTruncLEXIso C N n hn).symm (hflat n hn)
    · exact AlgebraicGeometry.SheafOfModules.IsFlat.of_isZero Y.sheaf
        (CochainComplex.isZero_of_isStrictlyLE D N n (by omega))
  have hb : ∃ n : ℤ, CochainComplex.IsStrictlyLE D n := ⟨N, inferInstance⟩
  exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms _)
    (NatTrans.retractArrowApp
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison g)
      (StacksDraft.StupidTruncation.retractOfHomotopy C e N he H))
    (Stacks.DerivedPullback.Composition.isIso_derivedPullbackComparison_app_of_isKFlat g
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj D)
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_of_boundedAbove_of_flat Y D hb
        hD))

end Retract

section Complex

open Stacks.CategoryTheory.CechComplex

/-- The intersection of finitely many members of an affine open cover is an open immersion over
`X`. -/
private theorem isOpenImmersion_inter_hom (T : X.AffineOpenCover.{u, u}) {p : ℕ}
    (x : Fin (p + 1) → T.I₀) :
    IsOpenImmersion (inter (fun i ↦ (Over.mk (T.f i) : Over X)) x).hom := by
  have : ∀ a, IsOpenImmersion (Over.mk (T.f (x a)) : Over X).hom :=
    fun a => inferInstanceAs (IsOpenImmersion (T.f (x a)))
  exact isOpenImmersion_pi_hom _

/-- The relative Čech coefficient presheaf of a module flat over the base takes flat values on
the intersections of members of an affine open cover. -/
private theorem isFlat_relativeCechPresheaf_obj_inter
    (f : X ⟶ S) (T : X.AffineOpenCover.{u, u})
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from S))]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (hF : IsFlatOver f.toLRSHom.toShHom F.obj) {p : ℕ} (x : Fin (p + 1) → T.I₀) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := S.sheaf)
      (((relativeCechPresheaf f).obj F).obj
        (op (inter (fun i ↦ (Over.mk (T.f i) : Over X)) x))) := by
  have := isOpenImmersion_inter_hom T x
  have : IsAffineHom ((inter (fun i ↦ (Over.mk (T.f i) : Over X)) x).hom ≫ f) :=
    RelativeCechBaseChange.isAffineHom_pi_hom_comp (f := f) T x
  exact isFlat_relativeCechPresheaf_obj f F hF _

variable (f : X ⟶ S) (T : X.AffineOpenCover.{u, u}) [Fintype T.I₀]
  [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from S))]
  (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)

/-- Every term of the `ℕ`-indexed relative Čech complex of a module flat over the base is flat. -/
theorem isFlat_cechComplex_X (hF : IsFlatOver f.toLRSHom.toShHom F.obj) (p : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := S.sheaf)
      (((cechComplexFunctor fun i ↦ (Over.mk (T.f i) : Over X)).obj
        ((relativeCechPresheaf f).obj F)).X p) := by
  refine isFlat_pi (ι := Fin (p + 1) → T.I₀)
    (fun x => ((relativeCechPresheaf f).obj F).obj (op (inter (fun i ↦ (Over.mk (T.f i) : Over X))
        x)))
    (isFlat_relativeCechPresheaf_obj_inter f T F hF)

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The derived pullback of the Čech complex of an affine open cover, with coefficients in a
presheaf of flat modules, is computed termwise.** Signed sorting is homotopic to the identity of
the Čech complex and vanishes in degrees at least the number of members of the cover. -/
theorem isIso_derivedPullbackComparison_cechComplex {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (P : (Over X)ᵒᵖ ⥤ Y.Modules)
    (hP : ∀ (p : ℕ) (x : Fin (p + 1) → T.I₀),
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf)
        (P.obj (op (inter (fun i ↦ (Over.mk (T.f i) : Over X)) x)))) :
    IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
      g.toLRSHom.toShHom).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((cechComplexFunctor fun i ↦ (Over.mk (T.f i) : Over X)).obj P).extend
          ComplexShape.embeddingUpNat))) := by
  classical
  let : LinearOrder T.I₀ := linearOrderOfSTO WellOrderingRel
  have hU : ∀ i, IsSubterminal (Over.mk (T.f i) : Over X) :=
    isSubterminal_overMk_affineOpenCover T
  refine isIso_derivedPullbackComparison_of_homotopy g.toLRSHom.toShHom _
    (HomologicalComplex.extendMap (Sorting.sortHom _ _ hU) ComplexShape.embeddingUpNat)
    ((Fintype.card T.I₀ : ℤ) - 1) ?_
    (((Sorting.sortHomHomotopy _ _ hU).extend ComplexShape.embeddingUpNat).trans
      (Homotopy.ofEq (HomologicalComplex.extendMap_id _ _))) ?_
  · intro n hn
    obtain ⟨p, rfl⟩ : ∃ p : ℕ, (p : ℤ) = n := ⟨n.toNat, by omega⟩
    rw [HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingUpNat.f p = p from rfl),
      Sorting.sortHom_f, Sorting.sortEnd_eq_zero _ _ p (by omega), zero_comp, comp_zero]
    rfl
  · intro n _
    by_cases h0 : 0 ≤ n
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, (p : ℤ) = n := ⟨n.toNat, by omega⟩
      exact AlgebraicGeometry.SheafOfModules.IsFlat.of_iso Y.sheaf
        (HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat rfl).symm
        (isFlat_pi (ι := Fin (p + 1) → T.I₀)
          (fun x => P.obj (op (inter (fun i ↦ (Over.mk (T.f i) : Over X)) x))) (hP p))
    · exact AlgebraicGeometry.SheafOfModules.IsFlat.of_isZero Y.sheaf
        (HomologicalComplex.isZero_extend_X _ _ n fun i hi => by
          change (i : ℤ) = n at hi
          omega)

/-- **The derived pullback of the relative Čech complex of a module flat over the base is computed
termwise.** -/
theorem isIso_derivedPullbackComparison_relativeCechComplex
    (hF : IsFlatOver f.toLRSHom.toShHom F.obj) {S' : Scheme.{u}} (g : S' ⟶ S) :
    IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
      g.toLRSHom.toShHom).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((relativeCechComplex f T).obj F).obj))) :=
  isIso_derivedPullbackComparison_cechComplex T g _
    fun _ => isFlat_relativeCechPresheaf_obj_inter f T F hF

/-- **The derived pullback of the absolute Čech resolution of a flat module is computed
termwise.** -/
theorem isIso_derivedPullbackComparison_absoluteCechComplex
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) F.obj)
    {X' : Scheme.{u}} (g' : X' ⟶ X) :
    IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
      g'.toLRSHom.toShHom).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((Tag01XLDerivedIso.absoluteCechComplexPlus T).obj F).obj))) :=
  isIso_derivedPullbackComparison_cechComplex T g' _ fun p x => by
    have := isOpenImmersion_inter_hom T x
    have : IsAffineHom (inter (fun i ↦ (Over.mk (T.f i) : Over X)) x).hom :=
      RelativeCechBaseChange.isAffineHom_pi_hom T x
    exact isFlat_absoluteCechPresheaf_obj F hF _

end Complex

end

end Stacks.AlgebraicGeometry.FlatSourceBaseChange
