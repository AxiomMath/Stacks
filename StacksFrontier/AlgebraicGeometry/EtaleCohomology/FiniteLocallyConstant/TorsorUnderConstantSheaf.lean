module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SliceConstantSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SmallEtaleSitePresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.Sets
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.LocalTriviality

/-!
# Torsors under a finite constant sheaf are finite locally constant

Let `J` be a Grothendieck topology on `C` and let `M` be a finite abelian group. The sheaf of
sets underlying a torsor under the constant sheaf on `M` is finite locally constant.

## Main results

* `Stacks.Cohomology.Torsors.isFiniteLocallyConstant_abelianTorsor_constantSheaf` — on an
  arbitrary site, the sheaf of sets underlying a torsor under a finite constant abelian sheaf is
  finite locally constant.
* `AlgebraicGeometry.isFiniteLocallyConstant_abelianTorsor_smallEtaleTopology` — the same on
  Mathlib's small étale site `AlgebraicGeometry.Scheme.smallEtaleTopology`, where the
  side-condition on weak equivalences is discharged.
* `AlgebraicGeometry.exists_finiteEtale_representing_abelianTorsor` — consequently a torsor under
  a finite constant abelian sheaf on Mathlib's small étale site of `X` is represented by an
  object of the size-bounded small étale site of Stacks 021B whose structure morphism is finite,
  that is by a scheme finite étale over `X`.

## Implementation notes

The constant sheaf on `M` is a sheaf of abelian groups, and a torsor under it is a torsor under
the multiplicatively written sheaf of groups `Stacks.Cohomology.Torsors.abelianSheafAsGroupSheaf`
underlying it.

Transport to Mathlib's small étale site is not by instantiating the general statement at the
size-bounded site of Stacks 021B and then comparing: the general statement applies directly to
`AlgebraicGeometry.Scheme.smallEtaleTopology`, whose objects form a type in `Type (u + 1)` with
morphisms in `Type u`, so its coefficient universe `max (u + 1) u` is `u + 1`. Only the
representability statement crosses between the two sites, through
`AlgebraicGeometry.SmallEtale.isFiniteLocallyConstant_sheafEquiv_inverse_iff`, because Stacks
03RV is available on the size-bounded site.

The existence of sheafification for abelian sheaves at coefficient universe `u + 1` is a
hypothesis, as everywhere in this part of the library: Mathlib's instances for Mathlib's small
étale site are for coefficients whose morphisms live in the universe `u` of the schemes. The
corresponding hypothesis on weak equivalences is *not* carried, being a consequence of essential
smallness of the site.

## References

* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
* [Stacks Project, Tag 0A5G](https://stacks.math.columbia.edu/tag/0A5G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.ConstantSheaf

universe v u

namespace Stacks.Cohomology.Torsors

/-- **A torsor under a finite constant abelian sheaf is finite locally constant.** The sheaf of
sets underlying a torsor under the constant sheaf on a finite abelian group `M` is a finite
locally constant sheaf. -/
theorem isFiniteLocallyConstant_abelianTorsor_constantSheaf
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (M : AddCommGrpCat.{max u v}) [Finite M]
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (F : AbelianTorsor ((constantSheaf J AddCommGrpCat.{max u v}).obj M)) :
    IsFiniteLocallyConstant J
      (⟨F.1.presheaf, F.1.isSheaf⟩ : Sheaf J (Type (max u v))) := by
  classical
  let unit : (Functor.const Cᵒᵖ).obj (Multiplicative M) ⟶
      (abelianSheafAsGroupSheaf
        ((constantSheaf J AddCommGrpCat.{max u v}).obj M)).presheaf :=
    { app := fun U => ↾fun a => Multiplicative.ofAdd
        ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).app U (Multiplicative.toAdd a))
      naturality := by
        intro U V f
        ext a
        show Multiplicative.ofAdd
            ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).app V (Multiplicative.toAdd a)) =
          Multiplicative.ofAdd ((sheafify J ((Functor.const Cᵒᵖ).obj M)).map f
            ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).app U (Multiplicative.toAdd a)))
        congr 1
        exact congrArg (fun q => q (Multiplicative.toAdd a))
          ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).naturality f) }
  have hinj : Presheaf.IsLocallyInjective J unit := by
    refine ⟨fun {U} x y h => ?_⟩
    have h' : (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app U (Multiplicative.toAdd x) =
        (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app U (Multiplicative.toAdd y) :=
      congrArg Multiplicative.toAdd h
    refine J.superset_covering (fun V f hf => ?_)
      ((inferInstance :
        Presheaf.IsLocallyInjective J
          (toSheafify J ((Functor.const Cᵒᵖ).obj M))).equalizerSieve_mem
            (Multiplicative.toAdd x) (Multiplicative.toAdd y) h')
    exact congrArg Multiplicative.ofAdd hf
  have hsurj : Presheaf.IsLocallySurjective J unit := by
    refine ⟨fun {U} x => ?_⟩
    refine J.superset_covering (fun V f hf => ?_)
      ((inferInstance :
        Presheaf.IsLocallySurjective J
          (toSheafify J ((Functor.const Cᵒᵖ).obj M))).imageSieve_mem (Multiplicative.toAdd x))
    obtain ⟨a, ha⟩ := hf
    exact ⟨Multiplicative.ofAdd a, congrArg Multiplicative.ofAdd ha⟩
  have key : ∀ (V : C), F.1.presheaf.obj (op V) →
      Nonempty ((constantSheaf (J.over V) (Type (max u v))).obj (Multiplicative M) ≅
        (J.overPullback (Type (max u v)) V).obj ⟨F.1.presheaf, F.1.isSheaf⟩) := by
    intro V s
    obtain ⟨φ, hφ⟩ := (PseudoTorsor.isTrivial_over_iff F.1 V).2 ⟨s⟩
    have hiso : IsIso φ.hom := hφ
    have h1 : Presheaf.IsLocallyInjective (J.over V)
        ((Over.forget V).op.whiskerLeft unit) :=
      Presheaf.isLocallyInjective_whisker (J.over V) J (Over.forget V) _
    have h2 : Presheaf.IsLocallySurjective (J.over V)
        ((Over.forget V).op.whiskerLeft unit) :=
      Presheaf.isLocallySurjective_whisker (J.over V) J (Over.forget V) _
    let χ : (Over.forget V).op ⋙
        (abelianSheafAsGroupSheaf
          ((constantSheaf J AddCommGrpCat.{max u v}).obj M)).presheaf ⟶
        (Over.forget V).op ⋙ F.1.presheaf := φ.hom
    have hχ : IsIso χ := hiso
    let ψ := (Over.forget V).op.whiskerLeft unit ≫ χ
    have h1' : Presheaf.IsLocallyInjective (J.over V) ψ := by
      have := h1
      have := hχ
      infer_instance
    have h2' : Presheaf.IsLocallySurjective (J.over V) ψ := by
      have := h2
      have := hχ
      infer_instance
    have hsheaf : IsIso (toSheafify J F.1.presheaf) := isIso_toSheafify J F.1.isSheaf
    let ε : (presheafToSheaf J (Type (max u v))).obj F.1.presheaf ≅
        (⟨F.1.presheaf, F.1.isSheaf⟩ : Sheaf J (Type (max u v))) :=
      (sheafToPresheaf J (Type (max u v))).preimageIso
        (asIso (toSheafify J F.1.presheaf)).symm
    exact ⟨constantSheafObjIsoOverPullback J V ψ h1' h2' ≪≫
      (J.overPullback (Type (max u v)) V).mapIso ε⟩
  refine ⟨fun U => ?_⟩
  obtain ⟨S, hS, hne⟩ := F.2 U
  refine ⟨Σ V : C, {f : V ⟶ U // S f}, fun a => a.1, fun a => a.2.1, ?_, fun a => ?_⟩
  · refine J.superset_covering (fun V f hf => ?_) hS
    exact Sieve.ofArrows_mk (fun a : Σ V : C, {f : V ⟶ U // S f} => a.1)
      (fun a => a.2.1) ⟨V, f, hf⟩
  · obtain ⟨s⟩ := hne a.2.2
    exact ⟨Multiplicative M, inferInstance, key a.1 s⟩

end Stacks.Cohomology.Torsors

namespace AlgebraicGeometry

open Stacks.Cohomology.Torsors

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (M : AddCommGrpCat.{u + 1}) [Finite M]
  [HasSheafify X.obj.smallEtaleTopology AddCommGrpCat.{u + 1}]

/-- **A torsor under a finite constant abelian sheaf on the small étale site is finite locally
constant.** -/
theorem isFiniteLocallyConstant_abelianTorsor_smallEtaleTopology
    (F : AbelianTorsor
      ((constantSheaf X.obj.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)) :
    IsFiniteLocallyConstant X.obj.smallEtaleTopology
      (⟨F.1.presheaf, F.1.isSheaf⟩ :
        Sheaf X.obj.smallEtaleTopology (Type (u + 1))) := by
  have : EssentiallySmall.{u + 1} X.obj.Etale := essentiallySmallSelf.{u + 1, u, u + 1} _
  have : X.obj.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  exact isFiniteLocallyConstant_abelianTorsor_constantSheaf X.obj.smallEtaleTopology M F

/-- **A torsor under a finite constant abelian sheaf on the small étale site is represented by a
scheme finite étale over the base.** -/
theorem exists_finiteEtale_representing_abelianTorsor
    (F : AbelianTorsor
      ((constantSheaf X.obj.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)) :
    ∃ U : SmallEtale B X.obj X.property, IsFinite (B.inclusion.map U.obj.hom) ∧
      Nonempty ((SmallEtale.sheafEquiv B X.obj X.property (Type (u + 1))).inverse.obj
          ⟨F.1.presheaf, F.1.isSheaf⟩ ≅
        (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj U) :=
  (Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable B X _).mp
    ((SmallEtale.isFiniteLocallyConstant_sheafEquiv_inverse_iff B X _).mpr
      (isFiniteLocallyConstant_abelianTorsor_smallEtaleTopology B X M F))

end AlgebraicGeometry

end
