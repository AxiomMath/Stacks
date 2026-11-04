module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalizedPullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedEpsilonBaseRingChart
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedEpsilonNaiveCotangentLocalCriterion
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentPushforwardSectionsH1

/-!
# Stacks 0D0X: the charts of affine Zariski squares

Step M4 of the proof of Stacks 0D0X localizes the comparison of the degree `-1` cohomology
sheaves of `ε^*NL_{X₀/Y₀}` and `NL_{X/Y}` to the étale charts `ε(Z)` of affine opens `Z` of `X₀`
mapping into an affine open `W` of `Y₀`.  This file shows that these charts cover the small étale
site of `X = h_U`, and computes the map `κ_{-1} : 𝒦₀ ⟶ ε_*𝒦` of degree `-1` cohomology sheaves on
the sections attached to the classes of `H₁` of the chart rings.

## Main results

* `AlgebraicGeometry.Space.coversTop_representedAffineSquare`: the affine opens `Z` of `X₀` with
  `f₀(Z)` inside an affine open of `Y₀` cover `X₀`.
* `AlgebraicGeometry.Space.coversTop_representedEpsilonFunctor_affineSquare`: their étale charts
  cover the small étale site of `X`.
* `AlgebraicGeometry.Space.subsingleton_hom_representedEpsilonFunctor_obj`: there is at most one
  morphism from an étale chart of `X` into the chart of a Zariski open of `X₀`.
* `Stacks.SheafOfModules.eqToHom_comp_naiveCotangentComplex_d_negOne_zero`: the differential of
  the naive cotangent complex read on the conormal sheaf.
* `Stacks.SheafOfModules.canonicalConormalKernelIso`: the kernel of the conormal map is the kernel
  of the differential of `NL_{B/A}`; `AlgebraicGeometry.Space.naiveCotangentKernelIso` for
  `NL_{X/Y}`.
* `Stacks.SheafOfModules.app_eq_of_comp_eq_naiveCotangentComplexPushforwardSquareMap_f_negOne`:
  a map of kernels lifting a square through a pushforward, on sections attached to classes of `H₁`.
* `Stacks.SheafOfModules.sectionsH1NaiveCotangent_heq`,
  `Stacks.SheafOfModules.h1CotangentMapOfSquare_algebraSections_heq`: transport of the image of an
  `H₁` class along equalities of the data, one equality per argument.
* `AlgebraicGeometry.Space.representedChartH1Map_comp`: the chart `H₁` of a Zariski square carried
  through the Zariski sections and the square of step 2 is the chart map.
* `AlgebraicGeometry.Space.representedEpsilonKernelHom_app_chartKernelSection`: `κ_{-1}` carries
  the section of `𝒦₀` attached to a chart class to the section of `𝒦` attached to it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Sheaves.ToposPushforward

universe u

namespace Stacks.SheafOfModules

universe v₁ u₁ w₁ z₁

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w₁}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]

/-- The differential `NL^{-1} ⟶ NL^0` read on the conormal sheaf of the canonical presentation is
the left-hand map of the conormal sequence. -/
theorem eqToHom_comp_naiveCotangentComplex_d_negOne_zero (A B : Sheaf J CommRingCat.{w₁})
    (a : A ⟶ B) :
    eqToHom (naiveCotangentComplex_X_negOne.{v₁, u₁, w₁, z₁} J A B a).symm ≫
        (naiveCotangentComplex.{v₁, u₁, w₁, z₁} J A B a).d (-1) 0 =
      (canonicalConormalSequence.{v₁, u₁, w₁, z₁} J A B a).f ≫
        eqToHom (naiveCotangentComplex_X_zero.{v₁, u₁, w₁, z₁} J A B a).symm := by
  rw [naiveCotangentComplex_d_negOne_zero, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- **The degree `-1` cohomology of `NL_{B/A}` is the kernel of the conormal map**: the kernel of
the left-hand map of the canonical conormal sequence is the kernel of the differential
`NL^{-1} ⟶ NL^0`. -/
def canonicalConormalKernelIso (A B : Sheaf J CommRingCat.{w₁}) (a : A ⟶ B) :
    kernel (canonicalConormalSequence.{v₁, u₁, w₁, z₁} J A B a).f ≅
      kernel ((naiveCotangentComplex.{v₁, u₁, w₁, z₁} J A B a).d (-1) 0) where
  hom := kernel.lift _
    (kernel.ι _ ≫ eqToHom (naiveCotangentComplex_X_negOne.{v₁, u₁, w₁, z₁} J A B a).symm) (by
      rw [Category.assoc, eqToHom_comp_naiveCotangentComplex_d_negOne_zero, kernel.condition_assoc,
        zero_comp])
  inv := kernel.lift _
    (kernel.ι _ ≫ eqToHom (naiveCotangentComplex_X_negOne.{v₁, u₁, w₁, z₁} J A B a)) (by
      rw [← cancel_mono (eqToHom (naiveCotangentComplex_X_zero.{v₁, u₁, w₁, z₁} J A B a).symm),
        Category.assoc, Category.assoc, ← eqToHom_comp_naiveCotangentComplex_d_negOne_zero,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, kernel.condition, zero_comp])
  hom_inv_id := (cancel_mono (kernel.ι _)).1 (by simp)
  inv_hom_id := (cancel_mono (kernel.ι _)).1 (by simp)

/-- `canonicalConormalKernelIso` followed by the inclusion of the kernel of the differential of
`NL_{B/A}` is the inclusion of the kernel of the conormal map, followed by the identification of
the degree `-1` term. -/
theorem canonicalConormalKernelIso_hom_ι (A B : Sheaf J CommRingCat.{w₁}) (a : A ⟶ B) :
    (canonicalConormalKernelIso.{v₁, u₁, w₁, z₁} J A B a).hom ≫ kernel.ι _ =
      kernel.ι _ ≫ eqToHom (naiveCotangentComplex_X_negOne.{v₁, u₁, w₁, z₁} J A B a).symm := by
  dsimp only [canonicalConormalKernelIso]
  exact kernel.lift_ι _ _ _

/-- The image of a class of `H₁(L_{B(U)/A(U)})` in the sections over `U` of the degree `-1`
term of `NL_{B/A}`: `Stacks.SheafOfModules.sectionsH1Comparison` read in `NL^{-1}`. -/
abbrev sectionsH1NaiveCotangent (A B : Sheaf J CommRingCat.{w₁}) (a : A ⟶ B) (U : Cᵒᵖ)
    (z : @Algebra.H1Cotangent (ToType (A.obj.obj U)) (ToType (B.obj.obj U)) _ _
      (algebraSections J A B a U)) :
    ToType (((naiveCotangentComplex.{v₁, u₁, w₁, z₁} J A B a).X (-1)).val.obj U) :=
  (eqToHom (naiveCotangentComplex_X_negOne.{v₁, u₁, w₁, z₁} J A B a).symm).val.app U
    (sectionsH1Comparison.{v₁, u₁, w₁, z₁} J A B a U z)

/-- A section of the kernel of the conormal map whose image in the conormal sheaf comes from a
class `z` of `H₁(L_{B(U)/A(U)})`, read in the kernel of the differential of `NL_{B/A}`, has image
the image of `z` in `NL^{-1}`. -/
theorem canonicalConormalKernelIso_hom_app_ι (A B : Sheaf J CommRingCat.{w₁}) (a : A ⟶ B)
    (U : Cᵒᵖ) (k : ToType ((kernel (presentationConormalSequence.{v₁, u₁, w₁, z₁} J A B a
      (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) (𝟙 _)).f).val.obj U))
    (z : @Algebra.H1Cotangent (ToType (A.obj.obj U)) (ToType (B.obj.obj U)) _ _
      (algebraSections J A B a U))
    (hk : (kernel.ι (presentationConormalSequence.{v₁, u₁, w₁, z₁} J A B a
      (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) (𝟙 _)).f).val.app U k =
        sectionsH1Comparison.{v₁, u₁, w₁, z₁} J A B a U z) :
    (kernel.ι ((naiveCotangentComplex.{v₁, u₁, w₁, z₁} J A B a).d (-1) 0)).val.app U
        ((canonicalConormalKernelIso.{v₁, u₁, w₁, z₁} J A B a).hom.val.app U k) =
      sectionsH1NaiveCotangent.{v₁, u₁, w₁, z₁} J A B a U z :=
  (congrArg (fun g => g.val.app U k)
    (canonicalConormalKernelIso_hom_ι.{v₁, u₁, w₁, z₁} J A B a)).trans
    (congrArg (fun x => (eqToHom
      (naiveCotangentComplex_X_negOne.{v₁, u₁, w₁, z₁} J A B a).symm).val.app U x) hk)

/-- **A map of kernels lifting the degree `-1` map of a square through a pushforward, on a
section attached to a class of `H₁`**: if `ι₀(m)` is the image of `z`, and `k` is a section of the
kernel of the differential of `NL_{B/A}` over `F X₀` whose image is the image of the image `w` of
`z` under the square of rings on sections, then `κ(m) = k`. -/
theorem app_eq_of_comp_eq_naiveCotangentComplexPushforwardSquareMap_f_negOne
    {C₀ : Type u} [Category.{u} C₀] {C : Type (u + 1)} [Category.{u} C]
    {J₀ : GrothendieckTopology C₀} {J : GrothendieckTopology C} {F : C₀ ⥤ C}
    {_ : F.IsContinuous J₀ J} {_ : HasWeakSheafify J₀ CommRingCat.{u}}
    {_ : HasWeakSheafify J CommRingCat.{u}}
    {_ : J₀.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})}
    {_ : J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})}
    {A B : Sheaf J CommRingCat.{u}} {a : A ⟶ B} {A₀ B₀ : Sheaf J₀ CommRingCat.{u}} {a₀ : A₀ ⟶ B₀}
    {ψ : A₀ ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J₀ J).obj A}
    {β : B₀ ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J₀ J).obj B}
    {hsq : a₀ ≫ β = ψ ≫ (F.sheafPushforwardContinuous CommRingCat.{u} J₀ J).map a}
    {K₀ : _root_.SheafOfModules.{u + 1} (Tensor.ringSheaf B₀)}
    {ι₀ : K₀ ⟶ (naiveCotangentComplex.{u, u, u, u + 1} J₀ A₀ B₀ a₀).X (-1)}
    {κ : K₀ ⟶ (_root_.SheafOfModules.pushforward.{u + 1}
      (pushforwardRingHomOfSquare J₀ J F B B₀ β)).obj
        (kernel ((naiveCotangentComplex.{u, u + 1, u, u} J A B a).d (-1) 0))}
    (hκ : κ ≫ (_root_.SheafOfModules.pushforward.{u + 1}
        (pushforwardRingHomOfSquare J₀ J F B B₀ β)).map (kernel.ι _) =
      ι₀ ≫ (naiveCotangentComplexPushforwardSquareMap.{u, u, u, u + 1, u, u}
        J₀ J F A B a A₀ B₀ a₀ ψ β hsq).f (-1))
    (X₀ : C₀ᵒᵖ) (z : @Algebra.H1Cotangent (ToType (A₀.obj.obj X₀)) (ToType (B₀.obj.obj X₀)) _ _
      (algebraSections J₀ A₀ B₀ a₀ X₀)) (m : ToType (K₀.val.obj X₀))
    (hm : ι₀.val.app X₀ m = sectionsH1NaiveCotangent.{u, u, u, u + 1} J₀ A₀ B₀ a₀ X₀ z)
    (k : ToType ((kernel ((naiveCotangentComplex.{u, u + 1, u, u} J A B a).d (-1) 0)).val.obj
        (op (F.obj X₀.unop))))
    (w : @Algebra.H1Cotangent _ _ _ _ (algebraSections J A B a (op (F.obj X₀.unop))))
    (hk : (kernel.ι ((naiveCotangentComplex.{u, u + 1, u, u} J A B a).d (-1) 0)).val.app
        (op (F.obj X₀.unop)) k = sectionsH1NaiveCotangent.{u, u + 1, u, u} J A B a _ w)
    (hw : @Stacks.NaiveCotangent.h1CotangentMapOfSquare _ _ _ _ _ _ _ _
          (algebraSections J₀ A₀ B₀ a₀ X₀) (algebraSections J A B a (op (F.obj X₀.unop)))
          (ψ.hom.app X₀).hom (β.hom.app X₀).hom
          (sectionsSquare_pushforward.{u, u, u, u + 1, u} J₀ J F A B A₀ B₀ ψ β a a₀ hsq X₀) z = w) :
    κ.val.app X₀ m = k := by
  apply injective_app_kernel_ι _ (op (F.obj X₀.unop))
  refine (app_of_comp_eq_naiveCotangentComplexPushforwardSquareMap_f_negOne
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hκ X₀ z m hm).trans ?_
  exact (congrArg (sectionsH1NaiveCotangent.{u, u + 1, u, u} J A B a _) hw).trans hk.symm


omit [HasWeakSheafify J CommRingCat] [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Two factorizations of a morphism of sheaves of commutative rings agree on sections. -/
theorem sheafHom_app_apply_of_comp_eq {P Q Q' R : Sheaf J CommRingCat.{w₁}} {p : P ⟶ Q}
    {q : Q ⟶ R} {p' : P ⟶ Q'} {q' : Q' ⟶ R} (h : p ≫ q = p' ≫ q') (U : Cᵒᵖ)
    (x : ToType (P.obj.obj U)) :
    (q.hom.app U).hom ((p.hom.app U).hom x) = (q'.hom.app U).hom ((p'.hom.app U).hom x) :=
  ConcreteCategory.congr_hom (congrArg (fun t => t.hom.app U) h) x

end Stacks.SheafOfModules

namespace Stacks.SheafOfModules

universe v₁ u₁ w₁ z₁

section Transport

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {_ : HasWeakSheafify J CommRingCat.{w₁}}
  {_ : J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})}

/-- Transport of the image of an `H₁` class in `NL^{-1}` along equalities of the data. -/
theorem sectionsH1NaiveCotangent_heq {J' : GrothendieckTopology C}
    {_ : HasWeakSheafify J' CommRingCat.{w₁}}
    {_ : J'.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})}
    {A B : Sheaf J CommRingCat.{w₁}} {A' B' : Sheaf J' CommRingCat.{w₁}} {a : A ⟶ B}
    {a' : A' ⟶ B'} (hJ : J = J') (hA : HEq A A') (hB : HEq B B') (ha : HEq a a') {U U' : Cᵒᵖ}
    (hU : U = U')
    {z : @Algebra.H1Cotangent (ToType (A.obj.obj U)) (ToType (B.obj.obj U)) _ _
      (algebraSections J A B a U)}
    {z' : @Algebra.H1Cotangent (ToType (A'.obj.obj U')) (ToType (B'.obj.obj U')) _ _
      (algebraSections J' A' B' a' U')} (hz : HEq z z') :
    HEq ((eqToHom (naiveCotangentComplex_X_negOne.{v₁, u₁, w₁, z₁} J A B a).symm).val.app U
        (sectionsH1Comparison.{v₁, u₁, w₁, z₁} J A B a U z))
      (sectionsH1NaiveCotangent.{v₁, u₁, w₁, z₁} J' A' B' a' U' z') := by
  subst hJ hU
  cases hA
  cases hB
  cases ha
  cases hz
  rfl

/-- Transport of the map on `H₁` induced by a square into the sections over `U` along equalities
of the data. -/
theorem h1CotangentMapOfSquare_algebraSections_heq {J' : GrothendieckTopology C}
    {R S : Type*} [CommRing R] [CommRing S]
    {inst : Algebra R S} {A B : Sheaf J CommRingCat.{w₁}} {A' B' : Sheaf J' CommRingCat.{w₁}}
    {a : A ⟶ B} {a' : A' ⟶ B'} (hJ : J = J') (hA : HEq A A') (hB : HEq B B') (ha : HEq a a')
    {U U' : Cᵒᵖ} (hU : U = U')
    {g : R →+* ToType (A.obj.obj U)} {g' : R →+* ToType (A'.obj.obj U')} (hg : HEq g g')
    {k : S →+* ToType (B.obj.obj U)} {k' : S →+* ToType (B'.obj.obj U')} (hk : HEq k k')
    {hc : ∀ r, k (@algebraMap R S _ _ inst r) =
      @algebraMap _ _ _ _ (algebraSections J A B a U) (g r)}
    {hc' : ∀ r, k' (@algebraMap R S _ _ inst r) =
      @algebraMap _ _ _ _ (algebraSections J' A' B' a' U') (g' r)}
    (x : @Algebra.H1Cotangent R S _ _ inst) :
    HEq (@Stacks.NaiveCotangent.h1CotangentMapOfSquare R S _ _ _ _ _ _ inst
        (algebraSections J A B a U) g k hc x)
      (@Stacks.NaiveCotangent.h1CotangentMapOfSquare R S _ _ _ _ _ _ inst
        (algebraSections J' A' B' a' U') g' k' hc' x) := by
  subst hJ hU
  cases hA
  cases hB
  cases ha
  cases hg
  cases hk
  rfl

/-- Two composable morphisms of sheaves of modules applied at equal objects to equal sections. -/
theorem sheafOfModules_app_app_heq {D : Type u₁} [Category.{v₁} D] {K : GrothendieckTopology D}
    {R : Sheaf K RingCat.{w₁}} {P Q T : _root_.SheafOfModules.{z₁} R} (f : P ⟶ Q) (g : Q ⟶ T)
    {X X' : Dᵒᵖ} (hX : X = X') {x : ToType (P.val.obj X)} {x' : ToType (P.val.obj X')}
    (hx : HEq x x') :
    HEq (g.val.app X (f.val.app X x)) (g.val.app X' (f.val.app X' x')) := by
  subst hX
  cases hx
  rfl

end Transport

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U V : BigFppfOver B S hS}
  (φ : U ⟶ V)

/-- **Affine Zariski squares of a represented morphism.**  Pairs of affine opens `Z` of `X₀` and
`W` of `Y₀` with `Z ⊆ f_0^{-1}W`, where `f₀ : X₀ ⟶ Y₀` represents `φ`. -/
def RepresentedAffineSquare : Type u :=
  {p : ((BigFppfOver.toScheme B S hS).obj U).Opens × ((BigFppfOver.toScheme B S hS).obj V).Opens //
    IsAffineOpen p.1 ∧ IsAffineOpen p.2 ∧ p.1 ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ p.2}

/-- **The affine Zariski squares cover `X₀`.** -/
theorem coversTop_representedAffineSquare :
    ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J.CoversTop
      (fun i : RepresentedAffineSquare B S hS φ ↦ i.1.1) := by
  intro O₀ x hx
  let O : ((BigFppfOver.toScheme B S hS).obj U).Opens := O₀
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    ((BigFppfOver.toScheme B S hS).obj V).isBasis_affineOpens.exists_subset_of_mem_open
      (show (BigFppfOver.toScheme B S hS).map φ x ∈ (⊤ : Set _) from trivial) isOpen_univ
  obtain ⟨_, ⟨Z, hZ, rfl⟩, hxZ, hZle⟩ :=
    ((BigFppfOver.toScheme B S hS).obj U).isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((O ⊓ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W :
        ((BigFppfOver.toScheme B S hS).obj U).Opens) : Set _) from ⟨hx, hxW⟩)
      (O ⊓ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W).isOpen
  exact ⟨Z, homOfLE fun y hy ↦ (hZle hy).1,
    ⟨⟨⟨Z, W⟩, hZ, hW, fun y hy ↦ (hZle hy).2⟩, ⟨𝟙 _⟩⟩, hxZ⟩

/-- **The étale charts of the affine Zariski squares cover the small étale site of `X = h_U`.** -/
theorem coversTop_representedEpsilonFunctor_affineSquare :
    (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J.CoversTop
      (fun i : RepresentedAffineSquare B S hS φ ↦ (representedEpsilonFunctor B S hS U).obj i.1.1) :=
  Stacks.Sheaves.LocalizedPullback.coversTop_map (representedEpsilonFunctor B S hS U) ⊤
    ((_root_.AlgebraicGeometry.SmallEtale.isTerminalOpensObjTop (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).isTerminalObj
        (representedSmallEtaleEquivalence B S hS U).inverse _)
    (coversTop_representedAffineSquare B S hS φ)

/-- **There is at most one morphism from an étale chart of `X = h_U` into the chart of a Zariski
open `Z` of `X₀`**: such morphisms correspond to inclusions of the image open into `Z`. -/
instance subsingleton_hom_representedEpsilonFunctor_obj (A : SmallEtale B S hS (yoneda.obj U))
    (Z : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    Subsingleton (A ⟶ (representedEpsilonFunctor B S hS U).obj Z) :=
  ⟨fun _ _ ↦ ((representedImageOpenEpsilonAdjunction B S hS U).homEquiv A Z).symm.injective
    (Subsingleton.elim _ _)⟩

/-- **The two descriptions of the degree `-1` cohomology sheaf of `NL_{X/Y}` agree**: the
kernel `𝒦` of the conormal map of the canonical presentation of `f♯` is the kernel of the
differential of `NL_{X/Y}`. -/
def naiveCotangentKernelIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    naiveCotangentKernel B S hS f ≅ kernel ((naiveCotangentComplex B S hS f).d (-1) 0) :=
  Stacks.SheafOfModules.canonicalConormalKernelIso.{u, u + 1, u, u} _
    (inverseImageStructureSheaf B S hS f) _ (structureSharpInverseImage B S hS f)

/-- `naiveCotangentKernelIso` followed by the inclusion of the kernel of the differential of
`NL_{X/Y}` is the inclusion of `𝒦`, followed by the identification of the degree `-1` term. -/
theorem naiveCotangentKernelIso_hom_ι {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (naiveCotangentKernelIso B S hS f).hom ≫ kernel.ι _ =
      kernel.ι _ ≫ eqToHom (Stacks.SheafOfModules.naiveCotangentComplex_X_negOne.{u, u + 1, u, u}
        _ (inverseImageStructureSheaf B S hS f) _ (structureSharpInverseImage B S hS f)).symm :=
  Stacks.SheafOfModules.canonicalConormalKernelIso_hom_ι.{u, u + 1, u, u} _ _ _ _

/-! ### The chart class at the chart itself -/

section ChartSpelling

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 f.hom)

/-- `AlgebraicGeometry.Space.chartH1Map` at the chart itself, with target the sections over
`d.U`. -/
abbrev chartH1MapAt :=
  @Stacks.NaiveCotangent.h1CotangentMapOfSquare _ _ _ _ _ _ _ _ (chartDiagramAlgebraInst B S hS f d)
    (Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op d.U))
    (chartDiagramRestrictBase B S hS f d (Over.mk (𝟙 d.U)))
    (chartDiagramRestrictO B S hS f d (Over.mk (𝟙 d.U))) (chartSquare_comm B S hS f d _)

/-- `AlgebraicGeometry.Space.naiveCotangentKernelι_chartKernelSection` with the chart class
read through `chartH1MapAt`: the section of `𝒦` over `d.U` attached to a chart class `h` maps to
the image of `chartH1MapAt h` in the sections of `NL^{-1}`. -/
theorem naiveCotangentKernelι_chartKernelSection_at (h : chartH1 B S hS f d) :
    naiveCotangentKernelι B S hS f d.U (chartKernelSection B S hS f d h) =
      Stacks.SheafOfModules.sectionsH1Comparison.{u, u + 1, u, u} _
        (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O
        (structureSharpInverseImage B S hS f) (op d.U) (chartH1MapAt B S hS f d h) :=
  naiveCotangentKernelι_chartKernelSection B S hS f d h

end ChartSpelling

/-! ### The chart `H₁` of a Zariski square and the Zariski `H₁` -/

variable {Z : ((BigFppfOver.toScheme B S hS).obj U).Opens}
  {W : ((BigFppfOver.toScheme B S hS).obj V).Opens}

/-- The base ring map `𝒪_Y(ε W) = 𝒪_{Y₀}(W) ⟶ (f_0^{-1}𝒪_{Y₀})(Z)` of a Zariski square
`Z ⊆ f_0^{-1}W`. -/
abbrev representedChartToZariskiBase (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W) :
    ToType ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O.obj.obj
      (op (representedEpsilonChartDiagram B S hS φ hZW).V)) →+*
      ToType (((inverseImageCommRingFunctor (representedZariskiSchemeHom B S hS φ).toToposHom).obj
        ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O).obj.obj (op Z)) :=
  (Scheme.Hom.inverseImageSections ((BigFppfOver.toScheme B S hS).map φ) hZW).hom.comp
    (Scheme.Opens.topIso W).hom.hom

/-- `ε_*(f♯)` on sections over a Zariski open `Z` is `f♯` over the chart `ε(Z)`. -/
theorem representedEpsilonCommRingPushforward_map_fSharpInverseImage_app_apply
    (y : ToType (((representedEpsilonCommRingPushforward B S hS U).obj
      ((inverseImageCommRingFunctor
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).toToposHom).obj
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O)).obj.obj (op Z))) :
    (((representedEpsilonCommRingPushforward B S hS U).map
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).fSharpInverseImage).hom.app
          (op Z)).hom y =
      ((structureSharpInverseImage B S hS (representedSpaceMap B S hS φ)).hom.app
        (op ((representedEpsilonFunctor B S hS U).obj Z))).hom y :=
  rfl

/-- **The square of step 2 of the proof of Stacks 0D0X on sections over a Zariski open `Z`**:
`(f_0^{-1}𝒪_{Y₀})(Z) ⟶ 𝒪_{X₀}(Z) ⟶ 𝒪_X(ε Z)` is
`(f_0^{-1}𝒪_{Y₀})(Z) ⟶ (f⁻¹𝒪_Y)(ε Z) ⟶ 𝒪_X(ε Z)`. -/
theorem representedEpsilonPushforwardSquare_app_apply
    (x : ToType (((inverseImageCommRingFunctor
        (representedZariskiSchemeHom B S hS φ).toToposHom).obj
          ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O).obj.obj (op Z))) :
    ((representedToZariskiRingedToposSiteHom B S hS U).fSharp.hom.app (op Z)).hom
        (((representedZariskiSchemeHom B S hS φ).fSharpInverseImage.hom.app (op Z)).hom x) =
      ((structureSharpInverseImage B S hS (representedSpaceMap B S hS φ)).hom.app
        (op ((representedEpsilonFunctor B S hS U).obj Z))).hom
        (((representedEpsilonBaseRingAdjunct B S hS φ).hom.app (op Z)).hom x) :=
  (Stacks.SheafOfModules.sheafHom_app_apply_of_comp_eq _
    (representedEpsilonPushforwardSquare_commutes B S hS φ) (op Z) x).trans
    (representedEpsilonCommRingPushforward_map_fSharpInverseImage_app_apply B S hS φ _)

/-- The adjunct of the base ring map of a Zariski square carries the base ring map of the chart
to the unit ring map of the chart diagram. -/
private theorem representedEpsilonBaseRingAdjunct_app_chartToZariskiBase
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (r : ToType ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O.obj.obj
      (op (representedEpsilonChartDiagram B S hS φ hZW).V))) :
    ((representedEpsilonBaseRingAdjunct B S hS φ).hom.app (op Z)).hom
        (representedChartToZariskiBase B S hS φ hZW r) =
      inverseImageChartUnitRingHom B S hS (representedSpaceMap B S hS φ)
        (representedEpsilonChartDiagram B S hS φ hZW) r := by
  have e1 := representedEpsilonBaseRingAdjunct_app_inverseImageSections B S hS φ hZW
    ((Scheme.Opens.topIso W).hom.hom r)
  have e2 : (AlgebraicGeometry.RingedToposHom.forgetFSharp
      (representedToSchemeZariskiRingedToposHom B S hS V)).hom.app (op W)
        ((Scheme.Opens.topIso W).hom.hom r) = r :=
    (representedToSchemeZariskiRingedToposHom_forgetFSharp_app B S hS V W _).trans
      (ConcreteCategory.congr_hom (Scheme.Opens.topIso W).hom_inv_id r)
  rwa [e2] at e1

/-- **The square from the chart diagram of a Zariski square to the Zariski sections commutes**:
`𝒪_Y(ε W) ⟶ 𝒪_X(ε Z) = 𝒪_{X₀}(Z)` is `𝒪_Y(ε W) = 𝒪_{Y₀}(W) ⟶ (f_0^{-1}𝒪_{Y₀})(Z) ⟶ 𝒪_{X₀}(Z)`. -/
theorem representedChartToZariski_comm (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (r : ToType ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O.obj.obj
      (op (representedEpsilonChartDiagram B S hS φ hZW).V))) :
    (Scheme.Opens.topIso Z).hom.hom
        (@algebraMap _ _ _ _ (chartDiagramAlgebraInst B S hS (representedSpaceMap B S hS φ)
          (representedEpsilonChartDiagram B S hS φ hZW)) r) =
      @algebraMap _ _ _ _ (Stacks.SheafOfModules.algebraSections
        ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J
        ((inverseImageCommRingFunctor (representedZariskiSchemeHom B S hS φ).toToposHom).obj
          ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O)
        ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O
        (representedZariskiSchemeHom B S hS φ).fSharpInverseImage (op Z))
        (representedChartToZariskiBase B S hS φ hZW r) := by
  have e1 := representedEpsilonBaseRingAdjunct_app_chartToZariskiBase B S hS φ hZW r
  have e3 := representedEpsilonPushforwardSquare_app_apply B S hS φ
    (representedChartToZariskiBase B S hS φ hZW r)
  have e4 := structureSharpInverseImage_inverseImageChartUnit B S hS (representedSpaceMap B S hS φ)
    (representedEpsilonChartDiagram B S hS φ hZW) r
  have e5 := representedToZariskiRingedToposSiteHom_fSharp_app_apply B S hS U Z
    (((representedZariskiSchemeHom B S hS φ).fSharpInverseImage.hom.app (op Z)).hom
      (representedChartToZariskiBase B S hS φ hZW r))
  exact (congrArg (Scheme.Opens.topIso Z).hom.hom (e4.symm.trans
    ((congrArg ((structureSharpInverseImage B S hS (representedSpaceMap B S hS φ)).hom.app
      (op ((representedEpsilonFunctor B S hS U).obj Z))).hom e1.symm).trans
        (e3.symm.trans e5)))).trans
    (ConcreteCategory.congr_hom (Scheme.Opens.topIso Z).inv_hom_id _)

/-- `AlgebraicGeometry.Space.naiveCotangentKernelIso` for the represented morphism `h_φ`, with
target the kernel of the differential of `NL_{X/Y}` written out. -/
def representedNaiveCotangentKernelIso :
    naiveCotangentKernel B S hS (representedSpaceMap B S hS φ) ≅
      kernel ((representedSpaceNaiveCotangentComplex B S hS φ).d (-1) 0) :=
  naiveCotangentKernelIso B S hS (representedSpaceMap B S hS φ)

/-- `naiveCotangentKernelIso_hom_ι` for the represented morphism `h_φ`. -/
theorem representedNaiveCotangentKernelIso_hom_ι :
    (representedNaiveCotangentKernelIso B S hS φ).hom ≫ kernel.ι _ =
      kernel.ι _ ≫ eqToHom (Stacks.SheafOfModules.naiveCotangentComplex_X_negOne.{u, u + 1, u, u}
        _ (inverseImageStructureSheaf B S hS (representedSpaceMap B S hS φ)) _
          (structureSharpInverseImage B S hS (representedSpaceMap B S hS φ))).symm :=
  naiveCotangentKernelIso_hom_ι B S hS (representedSpaceMap B S hS φ)

/-! ### `κ_{-1}` on the sections attached to chart classes -/

/-- The sheaf `f⁻¹𝒪_Y` in the spelling of `NL_{X/Y}`. -/
abbrev representedNLBase :
    Sheaf (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J CommRingCat.{u} :=
  (inverseImageCommRingFunctor
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).toToposHom).obj
    (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O

/-- The map `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` in the spelling of `NL_{X/Y}`. -/
abbrev representedNLSharp :
    representedNLBase B S hS φ ⟶
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O :=
  (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).fSharpInverseImage

/-- The algebra `(f⁻¹𝒪_Y)(ε Z) → 𝒪_X(ε Z)` in the spelling of `NL_{X/Y}`. -/
abbrev representedNLAlgebra (Z : ((BigFppfOver.toScheme B S hS).obj U).Opens) :=
  Stacks.SheafOfModules.algebraSections
    (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J
    (representedNLBase B S hS φ)
    (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O
    (representedNLSharp B S hS φ)
    (op ((representedToZariskiRingedToposSiteHom B S hS U).u.obj (unop (op Z))))

/-- The base map of the chart square of a Zariski square, into `(f⁻¹𝒪_Y)(ε Z)`. -/
abbrev representedChartRestrictBase (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W) :
    ToType ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O.obj.obj
      (op (representedEpsilonChartDiagram B S hS φ hZW).V)) →+*
      ToType ((representedNLBase B S hS φ).obj.obj
        (op ((representedToZariskiRingedToposSiteHom B S hS U).u.obj (unop (op Z))))) :=
  chartDiagramRestrictBase B S hS (representedSpaceMap B S hS φ)
    (representedEpsilonChartDiagram B S hS φ hZW) (Over.mk (𝟙 _))

/-- The identity of `𝒪_X(ε Z)`, the structure map of the chart square of a Zariski square. -/
abbrev representedChartRestrictO (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W) :
    ToType ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.obj
      (op (representedEpsilonChartDiagram B S hS φ hZW).U)) →+*
      ToType ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.obj
        (op ((representedToZariskiRingedToposSiteHom B S hS U).u.obj (unop (op Z))))) :=
  chartDiagramRestrictO B S hS (representedSpaceMap B S hS φ)
    (representedEpsilonChartDiagram B S hS φ hZW) (Over.mk (𝟙 _))

/-- The unit square of a Zariski square `Z ⊆ f_0^{-1}W` commutes: restricting along
`representedChartRestrictO` after the chart's algebra map is the algebra map of
`representedNLAlgebra` after `representedChartRestrictBase`. -/
theorem representedChartSquare_comm (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (r : ToType ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O.obj.obj
      (op (representedEpsilonChartDiagram B S hS φ hZW).V))) :
    representedChartRestrictO B S hS φ hZW
        (@algebraMap _ _ _ _ (chartDiagramAlgebraInst B S hS (representedSpaceMap B S hS φ)
          (representedEpsilonChartDiagram B S hS φ hZW)) r) =
      @algebraMap _ _ _ _ (representedNLAlgebra B S hS φ Z)
        (representedChartRestrictBase B S hS φ hZW r) :=
  chartSquare_comm B S hS _ _ _ r

/-- **The chart map `H ⟶ H₁` of a Zariski square, in the spelling of `NL_{X/Y}`**: the map
`H₁(L_{𝒪_X(ε Z)/𝒪_Y(ε W)}) ⟶ H₁(L_{𝒪_X(ε Z)/(f⁻¹𝒪_Y)(ε Z)})` of the unit square. -/
abbrev representedChartH1Map (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W) :=
  @Stacks.NaiveCotangent.h1CotangentMapOfSquare _ _ _ _ _ _ _ _
    (chartDiagramAlgebraInst B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW))
    (representedNLAlgebra B S hS φ Z) (representedChartRestrictBase B S hS φ hZW)
    (representedChartRestrictO B S hS φ hZW) (representedChartSquare_comm B S hS φ hZW)

/-- `chartH1MapAt` at the chart of a Zariski square agrees, up to the spelling of its source and
target, with `representedChartH1Map`. -/
theorem chartH1MapAt_heq_representedChartH1Map
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (h : chartH1 B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW)) :
    HEq (chartH1MapAt B S hS (representedSpaceMap B S hS φ)
        (representedEpsilonChartDiagram B S hS φ hZW) h)
      (representedChartH1Map B S hS φ hZW h) := by
  refine Stacks.SheafOfModules.h1CotangentMapOfSquare_algebraSections_heq ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals rfl

/-- The algebra `f_0^{-1}𝒪_{Y₀}(Z) → 𝒪_{X₀}(Z)` of a Zariski open `Z`. -/
abbrev representedZariskiAlgebra (Z : ((BigFppfOver.toScheme B S hS).obj U).Opens) :=
  Stacks.SheafOfModules.algebraSections
    ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J
    ((inverseImageCommRingFunctor (representedZariskiSchemeHom B S hS φ).toToposHom).obj
      ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O)
    ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O
    (representedZariskiSchemeHom B S hS φ).fSharpInverseImage (op Z)

/-- The chart class of a Zariski square carried to `H₁` of the Zariski sections over `Z`. -/
abbrev representedChartToZariskiH1 (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W) :=
  @Stacks.NaiveCotangent.h1CotangentMapOfSquare _ _ _ _ _ _ _ _
    (chartDiagramAlgebraInst B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW))
    (representedZariskiAlgebra B S hS φ Z)
    (representedChartToZariskiBase B S hS φ hZW) (Scheme.Opens.topIso Z).hom.hom
    (representedChartToZariski_comm B S hS φ hZW)

/-- **The two routes from the chart `H₁` to `H₁` of the sections over `ε Z` agree**: the class
`h ∈ H₁(L_{𝒪_X(ε Z)/𝒪_Y(ε W)})` carried to the Zariski sections over `Z` and then along the
square of step 2 is the image of `h` under the chart map. -/
theorem representedChartH1Map_comp (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (h : chartH1 B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW))
    (hc : ∀ r, ((representedToZariskiRingedToposSiteHom B S hS U).fSharp.hom.app (op Z)).hom
      (@algebraMap _ _ _ _ (representedZariskiAlgebra B S hS φ Z) r) =
        @algebraMap _ _ _ _ (representedNLAlgebra B S hS φ Z)
          (((representedEpsilonBaseRingAdjunct B S hS φ).hom.app (op Z)).hom r)) :
    @Stacks.NaiveCotangent.h1CotangentMapOfSquare _ _ _ _ _ _ _ _
        (representedZariskiAlgebra B S hS φ Z) (representedNLAlgebra B S hS φ Z)
        ((representedEpsilonBaseRingAdjunct B S hS φ).hom.app (op Z)).hom
        ((representedToZariskiRingedToposSiteHom B S hS U).fSharp.hom.app (op Z)).hom hc
        (representedChartToZariskiH1 B S hS φ hZW h) =
      representedChartH1Map B S hS φ hZW h := by
  let := chartDiagramAlgebraInst B S hS (representedSpaceMap B S hS φ)
    (representedEpsilonChartDiagram B S hS φ hZW)
  let := representedZariskiAlgebra B S hS φ Z
  let := representedNLAlgebra B S hS φ Z
  refine (Stacks.NaiveCotangent.h1CotangentMapOfSquare_comp _ _ _ _ _ _ h).trans ?_
  refine Stacks.NaiveCotangent.h1CotangentMapOfSquare_congr _ _ (RingHom.ext fun r => ?_)
    (RingHom.ext fun a => ?_) h
  · exact (representedEpsilonBaseRingAdjunct_app_chartToZariskiBase B S hS φ hZW r).trans
      (ConcreteCategory.congr_hom ((inverseImageStructureSheaf B S hS
      (representedSpaceMap B S hS φ)).obj.map_id
        (op ((representedEpsilonFunctor B S hS U).obj Z))).symm _)
  · exact ((representedToZariskiRingedToposSiteHom_fSharp_app_apply B S hS U Z _).trans
      (ConcreteCategory.congr_hom (Scheme.Opens.topIso Z).hom_inv_id a)).trans
      (ConcreteCategory.congr_hom ((smallEtaleRingedTopos B S hS
        (representedAlgebraicSpace B S hS U)).O.obj.map_id
          (op ((representedEpsilonFunctor B S hS U).obj Z))).symm a)

/-- **The chart section of `𝒦` at the chart of a Zariski square, read in the kernel of the
differential of `NL_{X/Y}`**, is the image of the chart class in `NL^{-1}_{X/Y}`. -/
theorem representedChartKernelSection_heq (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (h : chartH1 B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW)) :
    HEq ((kernel.ι ((representedSpaceNaiveCotangentComplex B S hS φ).d (-1) 0)).val.app
        (op ((representedToZariskiRingedToposSiteHom B S hS U).u.obj (unop (op Z))))
        ((representedNaiveCotangentKernelIso B S hS φ).hom.val.app
          (op ((representedToZariskiRingedToposSiteHom B S hS U).u.obj Z))
          (chartKernelSection B S hS (representedSpaceMap B S hS φ)
            (representedEpsilonChartDiagram B S hS φ hZW) h)))
      ((eqToHom (Stacks.SheafOfModules.naiveCotangentComplex_X_negOne.{u, u + 1, u, u}
          _ (inverseImageStructureSheaf B S hS (representedSpaceMap B S hS φ)) _
          (structureSharpInverseImage B S hS (representedSpaceMap B S hS φ))).symm).val.app
        (op (representedEpsilonChartDiagram B S hS φ hZW).U)
        (Stacks.SheafOfModules.sectionsH1Comparison.{u, u + 1, u, u} _
          (inverseImageStructureSheaf B S hS (representedSpaceMap B S hS φ)) _
          (structureSharpInverseImage B S hS (representedSpaceMap B S hS φ))
          (op (representedEpsilonChartDiagram B S hS φ hZW).U)
          (chartH1MapAt B S hS (representedSpaceMap B S hS φ)
            (representedEpsilonChartDiagram B S hS φ hZW) h))) := by
  refine (Stacks.SheafOfModules.sheafOfModules_app_app_heq
    (representedNaiveCotangentKernelIso B S hS φ).hom (kernel.ι _)
    (X' := op (representedEpsilonChartDiagram B S hS φ hZW).U) rfl HEq.rfl).trans (heq_of_eq ?_)
  refine (congrArg (fun g => g.val.app (op (representedEpsilonChartDiagram B S hS φ hZW).U)
    (chartKernelSection B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW) h))
    (representedNaiveCotangentKernelIso_hom_ι B S hS φ)).trans ?_
  exact congrArg (fun t => (eqToHom
      (Stacks.SheafOfModules.naiveCotangentComplex_X_negOne.{u, u + 1, u, u}
        _ (inverseImageStructureSheaf B S hS (representedSpaceMap B S hS φ)) _
        (structureSharpInverseImage B S hS (representedSpaceMap B S hS φ))).symm).val.app
      (op (representedEpsilonChartDiagram B S hS φ hZW).U) t)
    (naiveCotangentKernelι_chartKernelSection_at B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW) h)

/-- **`κ_{-1}` on the section of `𝒦₀` attached to a chart class.**  Let `h` be a class of
`H₁(L_{𝒪_X(ε Z)/𝒪_Y(ε W)})` for a Zariski square `Z ⊆ f_0^{-1}W`, and `m` a section of `𝒦₀` over
`Z` whose image in `NL^{-1}_{X₀/Y₀}` is the image of `h` carried to the Zariski sections.  Then
`κ_{-1}(m)` is the section of `𝒦` over `ε Z` attached to `h`. -/
theorem representedEpsilonKernelHom_app_chartKernelSection
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (h : chartH1 B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW))
    (m : ToType ((kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.obj
      (op Z)))
    (hm : (kernel.ι ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.app
        (op Z) m = Stacks.SheafOfModules.sectionsH1NaiveCotangent.{u, u, u, u + 1} _ _ _
          (representedZariskiSchemeHom B S hS φ).fSharpInverseImage (op Z)
          (representedChartToZariskiH1 B S hS φ hZW h)) :
    (representedEpsilonKernelHom B S hS φ).val.app (op Z) m =
      (representedNaiveCotangentKernelIso B S hS φ).hom.val.app
        (op ((representedToZariskiRingedToposSiteHom B S hS U).u.obj Z))
        (chartKernelSection B S hS (representedSpaceMap B S hS φ)
          (representedEpsilonChartDiagram B S hS φ hZW) h) := by
  refine Stacks.SheafOfModules.app_eq_of_comp_eq_naiveCotangentComplexPushforwardSquareMap_f_negOne
    (representedEpsilonKernelHom_comp_ι B S hS φ) (op Z) _ m hm _
    (representedChartH1Map B S hS φ hZW h) ?_ (representedChartH1Map_comp B S hS φ hZW h _)
  refine eq_of_heq ((representedChartKernelSection_heq B S hS φ hZW h).trans ?_)
  refine Stacks.SheafOfModules.sectionsH1NaiveCotangent_heq ?_ ?_ ?_ ?_ ?_
    (chartH1MapAt_heq_representedChartH1Map B S hS φ hZW h)
  all_goals rfl

end AlgebraicGeometry.Space
