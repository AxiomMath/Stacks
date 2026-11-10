module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.FullSubcategory
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive
public import Mathlib.CategoryTheory.Localization.Equivalence
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.Whiskering
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.CategoryTheory.Triangulated.Localization
public import StacksFrontier.Homology.Eta.Cohomology
public import StacksFrontier.Homology.Eta.Complex
public import StacksFrontier.Homology.HomologyColimit
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.RingTheory.Flat.DirectLimit
public import StacksFrontier.RingTheory.GradedAlgebra.Proj.LaurentAway

/-!
# The Berthelot--Ogus eta operator on the homotopy and derived categories

Let `f` be a nonzerodivisor in a commutative ring `A`. The Berthelot--Ogus décalage
`η_f` is an endofunctor of the category of cochain complexes of `f`-torsion-free
`A`-modules. This file records its three homotopy-theoretic properties: it commutes
with translation but is *not* triangulated, it preserves quasi-isomorphisms, and
consequently it descends to an additive (not triangulated) endofunctor of `D(A)`.

## Main definitions

* `Stacks.Eta.DerivedFunctor.FTorsionFreeModule` is the full subcategory of `A`-modules on which
  multiplication by `f` is injective.
* `Stacks.Eta.DerivedFunctor.EtaFunctor` bundles `η_f` on complexes in that subcategory together
  with
  its terms, differentials, and action on morphisms; `Stacks.Eta.DerivedFunctor.etaFunctor`
    implements it.
* `Stacks.Eta.DerivedFunctor.etaShiftIso` is the shift comparison, given by multiplication by
  `f^n`.
* `Stacks.Eta.DerivedFunctor.etaHomotopy` restricts a homotopy to the eta terms, and
  `Stacks.Eta.DerivedFunctor.etaHomotopyFunctor` descends `η_f` to the homotopy category.

## Main results

* `Stacks.Eta.DerivedFunctor.eta_commutes_shift_but_not_triangulated` (tag 0GSN): the shift
  comparison is
  compatible with the fixed multiplication-by-`f` maps, yet the mapping-cone triangle of
  multiplication by `f` on `A[-1]` is carried to a non-distinguished triangle whenever `f`
  is not a unit.
* `Stacks.Eta.QuasiIsoPreservation.quasiIso_etaPow_of_quasiIso` (tag 0F7Q): `η_f` sends
  quasi-isomorphisms of
  complexes of `f`-torsion-free modules to quasi-isomorphisms.
* `Stacks.Eta.DerivedDescent.exists_additive_derived_eta` (tag 0F7R): `η_f` descends to an additive
  endofunctor of `D(A)`, naturally isomorphic to the chain-level décalage on complexes of
  `f`-torsion-free modules.
* `Stacks.Eta.DerivedDescent.isLocalization_homotopyInclusion` and
  `Stacks.Eta.DerivedDescent.isLocalization_underlyingComplexCompQ`: the localization statements
  that descent rests on — `D(A)` is the localization of the homotopy category of complexes of
  `f`-torsion-free modules, and of the complexes themselves, at the quasi-isomorphisms.  They
  are stated separately from tag 0F7R because they are what a *natural transformation* out of
  `D(A)` is built from: a functor on `D(A)` is determined by its restriction to the
  `f`-torsion-free complexes, and so is a natural transformation between two such functors.

## Implementation notes

The source category is represented literally as the full subcategory of `ModuleCat A` on
the `f`-torsion-free modules; its zero object and binary biproducts are instances, so its
homotopy category carries the standard triangulated structure. The eta terms are the
submodules `EtaPow.fetaTerm` of the localized terms, and the substrate is
`StacksFrontier.Homology.Eta.Complex`.

Tag 0F7R needs a functorial supply of complexes with `f`-torsion-free terms in every
quasi-isomorphism class. Section `EtaFlatResolution` replays, from the Section 96
development, exactly the construction needed: every cochain complex of modules receives a
quasi-isomorphism from a complex with flat terms. Tag 06Y4 (K-flatness of that resolution)
is not needed here and is not reproved.

## References

* [Stacks Project, Tag 0GSN](https://stacks.math.columbia.edu/tag/0GSN)
* [Stacks Project, Tag 0F7Q](https://stacks.math.columbia.edu/tag/0F7Q)
* [Stacks Project, Tag 0F7R](https://stacks.math.columbia.edu/tag/0F7R)
* [Berthelot--Ogus, *Notes on crystalline cohomology*, Section 8][Berthelot-Ogus]
* [Bhatt--Morrow--Scholze, *Integral p-adic Hodge theory*, Section 6][BMS]
-/

@[expose] public section

-- Elaborating the eta shift comparisons and the counterexample cone requires the
-- transparency and recursion settings under which the Section 96 proofs were written.
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v w

/-! ## Flat resolutions of unbounded complexes

The single input tag 0F7R takes from outside this cluster: every cochain complex of
modules admits a quasi-isomorphism from a complex with flat terms. The construction is
the one of Section 96, reproduced here so that this cluster is self-contained; only
the flat-terms and quasi-isomorphism conclusions are needed, so K-flatness of the
resolution is neither asserted nor proved. -/

open Stacks.HomologyColimit

namespace EtaFlatResolution

open CategoryTheory CategoryTheory.Limits

universe uc vc ur ux

section HomologyColimit

variable {D : Type uc} [Category.{vc} D] [Abelian D]

end HomologyColimit

/-- Every cochain complex of `R`-modules receives a quasi-isomorphism from a cochain
complex all of whose terms are flat. -/
theorem exists_flatTerms_resolution {R : Type ur} [CommRing R]
    (M : CochainComplex (ModuleCat.{max ur ux} R) ℤ) :
    ∃ (K : CochainComplex (ModuleCat.{max ur ux} R) ℤ) (f : K ⟶ M),
      (∀ n : ℤ, Module.Flat R (K.X n)) ∧ QuasiIso f := by
  let P : ObjectProperty (ModuleCat.{max ur ux} R) := fun X => Projective X
  have : P.ContainsZero := ⟨ModuleCat.of R (Fin 0 → ULift.{ux} R),
    ModuleCat.isZero_of_subsingleton _, inferInstance⟩
  have hsum : ∀ X Y : ModuleCat.{max ur ux} R, P X → P Y → P (X ⊞ Y) :=
    fun X Y (_ : Projective X) (_ : Projective Y) => inferInstance
  have hcover : ∀ X : ModuleCat.{max ur ux} R, ∃ (Y : ModuleCat.{max ur ux} R) (_ : P Y)
      (p : Y ⟶ X), Epi p :=
    fun X => ⟨Projective.over X, inferInstance, Projective.π X, inferInstance⟩
  obtain ⟨Q, q, g, hq, hepi, hle, hflat, -, hladder⟩ :=
    CochainComplex.exists_sequence_quasiIso_truncLE P hsum hcover M
  let Dseq := Functor.ofSequence g
  let c := colimit.cocone Dseq
  have hc : IsColimit c := colimit.isColimit Dseq
  let s : Cocone Dseq := Cocone.mk M
    (NatTrans.ofSequence (fun n => q n ≫ M.ιTruncLE (n : ℤ)) (fun n => by
      rw [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
      exact (hladder n).trans (Category.comp_id _).symm))
  let α : c.pt ⟶ M := hc.desc s
  have hα : ∀ n : ℕ, c.ι.app n ≫ α = q n ≫ M.ιTruncLE (n : ℤ) := fun n => hc.fac s n
  have hqi : QuasiIso α :=
    have : AB5OfSize.{0, 0, max ur ux, max ur ux + 1} AddCommGrpCat.{max ur ux} :=
      AB5OfSize_of_univLE.{0, 0, max ur ux, max ur ux} AddCommGrpCat.{max ur ux}
    have : HasExactColimitsOfShape ℕ (ModuleCat.{max ur ux} R) :=
      HasExactColimitsOfShape.domain_of_functor ℕ
        (forget₂ (ModuleCat.{max ur ux} R) AddCommGrpCat.{max ur ux})
    StacksDraft.UnboundedLeftDerivedFunctor.quasiIso_of_isColimit_of_quasiIso_truncLE q hq hc α hα
  have hterms : ∀ i : ℤ, Module.Flat R (c.pt.X i) := by
    intro i
    have ht : Module.Flat R (colimit (Dseq ⋙ HomologicalComplex.eval _ _ i) : ModuleCat R) :=
      CochainComplex.KFlat.flat_colimit.{ur, ux} _ (fun n => by
        change Module.Flat R ((Q n).X i)
        have : Projective ((Q n).X i) := hflat n i
        infer_instance)
    exact @Module.Flat.of_linearEquiv R _ _ _ _ _ _ _ ht
      (preservesColimitIso (HomologicalComplex.eval _ _ i) Dseq).toLinearEquiv
  exact ⟨c.pt, α, hterms, hqi⟩

end EtaFlatResolution

/-! ## Eta as a functor on complexes of `f`-torsion-free modules (Tag 0GSN) -/

namespace Stacks.Eta.DerivedFunctor

open CategoryTheory CategoryTheory.Limits
open EtaPow

variable {A : Type u} [CommRing A]

/-- The property that multiplication by `f` is injective on an `A`-module. -/
def isFTorsionFree (f : A) : ObjectProperty (ModuleCat.{max u v} A) :=
  fun M => ∀ x : M, f • x = 0 → x = 0

/-- The full subcategory of `A`-modules which are `f`-torsion-free. -/
abbrev FTorsionFreeModule (f : A) := (isFTorsionFree.{u, v} f).FullSubcategory

/-- The zero module is `f`-torsion-free. -/
instance torsionFreeContainsZero (f : A) :
    (isFTorsionFree.{u, v} f).ContainsZero where
  exists_zero := ⟨ModuleCat.of A PUnit, ModuleCat.isZero_of_subsingleton _,
    fun _ _ => Subsingleton.elim _ _⟩

/-- Products of two `f`-torsion-free modules give their biproduct. -/
instance torsionFreeHasBinaryBiproducts (f : A) :
    HasBinaryBiproducts (FTorsionFreeModule.{u, v} f) := by
  constructor
  intro X Y
  let P : FTorsionFreeModule.{u, v} f :=
    ⟨ModuleCat.of A (X.obj × Y.obj), fun x hx =>
      Prod.ext (X.property x.1 (congrArg Prod.fst hx))
        (Y.property x.2 (congrArg Prod.snd hx))⟩
  let b : BinaryBicone X Y := {
    pt := P
    fst := ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.fst A X.obj Y.obj))
    snd := ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.snd A X.obj Y.obj))
    inl := ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.inl A X.obj Y.obj))
    inr := ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.inr A X.obj Y.obj))
    inl_fst := by ext; rfl
    inl_snd := by ext; rfl
    inr_fst := by ext; rfl
    inr_snd := by ext; rfl }
  apply hasBinaryBiproduct_of_total b
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (x.1 + 0, 0 + x.2) = x
  simp

/-- The inclusion of complexes of `f`-torsion-free modules into complexes of all
`A`-modules. -/
noncomputable def underlyingComplex (f : A) :
    CochainComplex (FTorsionFreeModule.{u, v} f) ℤ ⥤ CochainComplex (ModuleCat.{max u v} A) ℤ :=
  (isFTorsionFree.{u, v} f).ι.mapHomologicalComplex (ComplexShape.up ℤ)

/-- The ring as an `f`-torsion-free module when `f` is a nonzerodivisor. -/
noncomputable def torsionFreeSelf (f : A) (hf : f ∈ nonZeroDivisors A) :
    FTorsionFreeModule.{u, v} f :=
  ⟨ModuleCat.of A (ULift.{v} A), fun x hx => by
    apply ULift.ext
    exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hf).mp
      (congrArg ULift.down hx)⟩

/-- The Berthelot--Ogus eta functor on complexes of `f`-torsion-free modules, specified
by its degree-`i` term `{x ∈ f^i M^i | d x ∈ f^(i+1) M^(i+1)}`, its differential induced
by the localized differential, and its action on morphisms induced by localization. -/
structure EtaFunctor (f : A) where
  /-- The underlying endofunctor on complexes of `f`-torsion-free modules. -/
  functor : CochainComplex (FTorsionFreeModule.{u, v} f) ℤ ⥤
    CochainComplex (FTorsionFreeModule.{u, v} f) ℤ
  /-- The identification of each underlying term with the defining eta submodule. -/
  termIso : ∀ (M : CochainComplex (FTorsionFreeModule.{u, v} f) ℤ) (i : ℤ),
    ((functor.obj M).X i).obj ≅ ModuleCat.of A
      (fetaTerm f (((underlyingComplex f).obj M).d i (i + 1)).hom i)
  /-- Under `termIso`, the eta differential is the localized differential. -/
  differential : ∀ (M) (i : ℤ) (x : ((functor.obj M).X i).obj),
    ((((functor.obj M).d i (i + 1)).hom ≫ (termIso M (i + 1)).hom).hom x).val =
      fLoc f (((underlyingComplex f).obj M).d i (i + 1)).hom
        (((termIso M i).hom.hom x).val)
  /-- Under `termIso`, eta sends a complex map to its localized map. -/
  map_f : ∀ {M N} (g : M ⟶ N) (i : ℤ) (x : ((functor.obj M).X i).obj),
    ((((functor.map g).f i).hom ≫ (termIso N i).hom).hom x).val =
      fLoc f (((underlyingComplex f).map g).f i).hom
        (((termIso M i).hom.hom x).val)

/-- The degree-`i` term of the eta complex, as an `f`-torsion-free module. -/
noncomputable def etaTerm (f : A)
    (M : CochainComplex (FTorsionFreeModule.{u, v} f) ℤ) (i : ℤ) : FTorsionFreeModule.{u, v} f :=
  ⟨ModuleCat.of A
      (fetaTerm f (((underlyingComplex f).obj M).d i (i + 1)).hom i),
    by
      intro x hx
      apply Subtype.ext
      have hx' : f • (x : Loc f (((underlyingComplex f).obj M).X i)) = 0 :=
        congrArg Subtype.val hx
      rw [← fUnit_units_smul] at hx'
      exact (smul_eq_zero_iff_eq (Stacks.GradedLaurent.awayUnit f)).mp hx'⟩

/-- The eta differential is the restriction of the localized differential. -/
noncomputable def etaDifferential (f : A)
    (M : CochainComplex (FTorsionFreeModule.{u, v} f) ℤ) (i : ℤ) :
    etaTerm f M i ⟶ etaTerm f M (i + 1) :=
  let C := (underlyingComplex f).obj M
  ObjectProperty.homMk (ModuleCat.ofHom
    (((fLoc f (C.d i (i + 1)).hom).comp
      (fetaTerm f (C.d i (i + 1)).hom i).subtype).codRestrict
        (fetaTerm f (C.d (i + 1) (i + 1 + 1)).hom (i + 1))
        (by
          intro x
          have h : (C.d (i + 1) (i + 1 + 1)).hom ∘ₗ (C.d i (i + 1)).hom = 0 :=
            congrArg ModuleCat.Hom.hom (C.d_comp_d i (i + 1) (i + 1 + 1))
          exact fLoc_mem_fetaTerm h i x.property)))

/-- The eta complex of a complex of `f`-torsion-free modules. -/
noncomputable def etaComplex (f : A)
    (M : CochainComplex (FTorsionFreeModule.{u, v} f) ℤ) :
    CochainComplex (FTorsionFreeModule.{u, v} f) ℤ :=
  CochainComplex.of (etaTerm f M) (etaDifferential f M) (by
    intro i
    ext x
    apply Subtype.ext
    change fLoc f (((underlyingComplex f).obj M).d (i + 1) (i + 1 + 1)).hom
      (fLoc f (((underlyingComplex f).obj M).d i (i + 1)).hom x.val) = 0
    have h := ((underlyingComplex f).obj M).d_comp_d i (i + 1) (i + 1 + 1)
    exact Eta.locMap_locMap_eq_zero (Submonoid.powers f) _ _
      (congrArg ModuleCat.Hom.hom h) x.val)

/-- Localization of linear maps is compatible with composition. -/
theorem fLoc_comp_apply (f : A) {X Y Z : Type*}
    [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    [AddCommGroup Z] [Module A Z] (g : X →ₗ[A] Y) (h : Y →ₗ[A] Z)
    (x : Loc f X) :
    fLoc f h (fLoc f g x) = fLoc f (h.comp g) x := by
  induction x using LocalizedModule.induction_on with
  | h m s => simp [fLoc, Eta.locMap_mk]

/-- Localization of the identity map is the identity. -/
theorem fLoc_id_apply (f : A) {X : Type*}
    [AddCommGroup X] [Module A X] (x : Loc f X) :
    fLoc f (LinearMap.id : X →ₗ[A] X) x = x := by
  induction x using LocalizedModule.induction_on with
  | h m s => simp [fLoc, Eta.locMap_mk]

/-- The localization of a morphism of complexes maps the eta term of the source into the eta term
of the target. -/
theorem fLoc_mem_etaTerm (f : A)
    {M N : CochainComplex (FTorsionFreeModule.{u, v} f) ℤ} (g : M ⟶ N) (i : ℤ)
    (x : fetaTerm f (((underlyingComplex f).obj M).d i (i + 1)).hom i) :
    fLoc f (((underlyingComplex f).map g).f i).hom x.val ∈
      fetaTerm f (((underlyingComplex f).obj N).d i (i + 1)).hom i := by
  let C := (underlyingComplex f).obj M
  let D := (underlyingComplex f).obj N
  let a := (underlyingComplex f).map g
  change fLoc f (a.f i).hom x.val ∈ fetaTerm f (D.d i (i + 1)).hom i
  obtain ⟨hpow, hd⟩ := (mem_fetaTerm).mp x.property
  apply (mem_fetaTerm).mpr
  constructor
  · obtain ⟨m, hm⟩ := mem_fpowSub.mp hpow
    apply mem_fpowSub.mpr
    refine ⟨(a.f i).hom m, ?_⟩
    rw [← hm, fLoc_zpow_smul, fLoc_toLoc]
  · have hcomm :
        (D.d i (i + 1)).hom.comp (a.f i).hom =
          (a.f (i + 1)).hom.comp (C.d i (i + 1)).hom :=
      congrArg ModuleCat.Hom.hom (a.comm i (i + 1))
    have heq : fLoc f (D.d i (i + 1)).hom (fLoc f (a.f i).hom x.val) =
        fLoc f (a.f (i + 1)).hom (fLoc f (C.d i (i + 1)).hom x.val) := by
      rw [fLoc_comp_apply, fLoc_comp_apply, hcomm]
    rw [heq]
    obtain ⟨m, hm⟩ := mem_fpowSub.mp hd
    apply mem_fpowSub.mpr
    refine ⟨(a.f (i + 1)).hom m, ?_⟩
    rw [← hm, fLoc_zpow_smul, fLoc_toLoc]

/-- The action of eta on a morphism of complexes. -/
noncomputable def etaMap (f : A)
    {M N : CochainComplex (FTorsionFreeModule.{u, v} f) ℤ} (g : M ⟶ N) :
    etaComplex f M ⟶ etaComplex f N :=
  CochainComplex.ofHom
    (fun i => ObjectProperty.homMk (ModuleCat.ofHom
      (((fLoc f (((underlyingComplex f).map g).f i).hom).comp
        (fetaTerm f (((underlyingComplex f).obj M).d i (i + 1)).hom i).subtype).codRestrict
          (fetaTerm f (((underlyingComplex f).obj N).d i (i + 1)).hom i)
          (fun x => fLoc_mem_etaTerm f g i x))))
    (by
      intro i
      ext x
      apply Subtype.ext
      let C := (underlyingComplex f).obj M
      let D := (underlyingComplex f).obj N
      let a := (underlyingComplex f).map g
      simp only [etaComplex, CochainComplex.of_d]
      change fLoc f (D.d i (i + 1)).hom (fLoc f (a.f i).hom x.val) =
        fLoc f (a.f (i + 1)).hom (fLoc f (C.d i (i + 1)).hom x.val)
      rw [fLoc_comp_apply, fLoc_comp_apply]
      exact congrArg (fun t : C.X i →ₗ[A] D.X (i + 1) => fLoc f t x.val)
        (congrArg ModuleCat.Hom.hom (a.comm i (i + 1))))

/-- The Berthelot--Ogus eta endofunctor on complexes of `f`-torsion-free modules. -/
noncomputable def etaFunctor (f : A) : EtaFunctor.{u, v} f where
  functor := {
    obj := etaComplex f
    map := etaMap f
    map_id := by
      intro M
      ext i x
      apply Subtype.ext
      change fLoc f (LinearMap.id : (M.X i).obj →ₗ[A] (M.X i).obj) x.val = x.val
      exact fLoc_id_apply f x.val
    map_comp := by
      intro M N P g h
      ext i x
      apply Subtype.ext
      dsimp only [etaComplex, CochainComplex.of_X, etaTerm] at x
      change fLoc f (((underlyingComplex f).map (g ≫ h)).f i).hom x.val =
        fLoc f (((underlyingComplex f).map h).f i).hom
          (fLoc f (((underlyingComplex f).map g).f i).hom x.val)
      have hc : (((underlyingComplex f).map (g ≫ h)).f i).hom =
          (((underlyingComplex f).map h).f i).hom.comp
            (((underlyingComplex f).map g).f i).hom :=
        rfl
      rw [hc]
      exact (fLoc_comp_apply f _ _ x.val).symm
  }
  termIso := fun M i => Iso.refl _
  differential := by
    intro M i x
    simp only [etaComplex, CochainComplex.of_d]
    rfl
  map_f := by
    intro M N g i x
    rfl

/-- Integer powers translate the localized power submodules. -/
theorem zpow_smul_mem_fpowSub (f : A) {X : Type*} [AddCommGroup X] [Module A X]
    (n i : ℤ) (x : Loc f X) :
    (Stacks.GradedLaurent.awayUnit f ^ n) • x ∈ fpowSub f X (i + n) ↔ x ∈ fpowSub f X i := by
  simp only [mem_fpowSub]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    apply (Eta.zpowEquiv (Submonoid.powers f) X (Stacks.GradedLaurent.awayUnit f) n).injective
    change (Stacks.GradedLaurent.awayUnit f ^ n) •
        ((Stacks.GradedLaurent.awayUnit f ^ i) • toLoc f X m) =
      (Stacks.GradedLaurent.awayUnit f ^ n) • x
    rwa [smul_smul, ← zpow_add, add_comm n i]
  · rintro ⟨m, rfl⟩
    exact ⟨m, by rw [zpow_add, mul_smul, smul_comm]⟩

/-- Localization is compatible with the sign in a shifted differential. -/
theorem fLoc_intUnit_smul (f : A) {X Y : Type*}
    [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (s : ℤˣ) (g : X →ₗ[A] Y) (x : Loc f X) :
    fLoc f (s • g) x = s • fLoc f g x := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · simp
  · simp only [Units.smul_def, Units.val_neg, Units.val_one, neg_one_smul]
    induction x using LocalizedModule.induction_on with
    | h m t => simp only [Eta.locMap_mk, LinearMap.neg_apply, LocalizedModule.mk_neg]

/-- Multiplication by `f^n` identifies the terms of eta before and after shifting. -/
theorem etaShiftTerm_mem (f : A)
    (M : CochainComplex (FTorsionFreeModule.{u, v} f) ℤ) (n i : ℤ)
    (x : Loc f (M.X (i + n)).obj) :
    (Stacks.GradedLaurent.awayUnit f ^ n) • x ∈
        fetaTerm f (M.d (i + n) (i + n + 1)).hom.hom (i + n) ↔
      x ∈ fetaTerm f ((M⟦n⟧).d i (i + 1)).hom.hom i := by
  change _ ↔ x ∈ fetaTerm f
    (n.negOnePow • (M.d (i + n) (i + 1 + n)).hom.hom) i
  rw [show i + 1 + n = i + n + 1 by omega]
  simp only [mem_fetaTerm, fLoc_intUnit_smul, fLoc_zpow_smul,
    zpow_smul_mem_fpowSub, add_right_comm i n 1]
  constructor
  · rintro ⟨hx, hd⟩
    exact ⟨hx, (fpowSub f _ (i + 1)).toAddSubgroup.zsmul_mem hd _⟩
  · rintro ⟨hx, hd⟩
    refine ⟨hx, ?_⟩
    have hh := (fpowSub f _ (i + 1)).toAddSubgroup.zsmul_mem hd (↑n.negOnePow⁻¹ : ℤ)
    simp only [← Units.smul_def, inv_smul_smul] at hh
    with_unfolding_all exact hh

/-- The termwise linear equivalence giving the shift comparison for eta. -/
noncomputable def etaShiftTermEquiv (f : A)
    (M : CochainComplex (FTorsionFreeModule.{u, v} f) ℤ) (n i : ℤ) :
    (etaTerm f (M⟦n⟧) i).obj ≃ₗ[A] (etaTerm f M (i + n)).obj :=
  (Eta.zpowEquiv (Submonoid.powers f) (M.X (i + n)).obj
      (Stacks.GradedLaurent.awayUnit f) n).ofSubmodules
    (fetaTerm f ((M⟦n⟧).d i (i + 1)).hom.hom i)
    (fetaTerm f (M.d (i + n) (i + n + 1)).hom.hom (i + n)) (by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (etaShiftTerm_mem f M n i y).mpr hy
      · intro hx
        let e := Eta.zpowEquiv (Submonoid.powers f) (M.X (i + n)).obj
          (Stacks.GradedLaurent.awayUnit f) n
        refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
        apply (etaShiftTerm_mem f M n i (e.symm x)).mp
        exact (show e (e.symm x) ∈ _ from (e.apply_symm_apply x).symm ▸ hx))

/-- The shift comparison `etaShiftTermEquiv` is multiplication by `f^n`. -/
@[simp]
theorem etaShiftTermEquiv_apply (f : A)
    (M : CochainComplex (FTorsionFreeModule.{u, v} f) ℤ) (n i : ℤ)
    (x : (etaTerm f (M⟦n⟧) i).obj) :
    (etaShiftTermEquiv f M n i x).val = (Stacks.GradedLaurent.awayUnit f ^ n) • x.val := rfl

/-- The differential of `etaComplex f M` is the localization of the differential of `M`. -/
theorem etaComplex_d_val (f : A)
    (M : CochainComplex (FTorsionFreeModule.{u, v} f) ℤ) (i j : ℤ) (hij : i + 1 = j)
    (x : ((etaComplex f M).X i).obj) :
    (((etaComplex f M).d i j).hom.hom x).val = fLoc f (M.d i j).hom.hom x.val := by
  subst j
  simp only [etaComplex, CochainComplex.of_d]
  rfl

/-- The natural shift isomorphism for eta, given by multiplication by `f^n`. -/
noncomputable def etaShiftIso (f : A) (n : ℤ) :
    shiftFunctor (CochainComplex (FTorsionFreeModule.{u, v} f) ℤ) n ⋙ (etaFunctor f).functor ≅
      (etaFunctor f).functor ⋙ shiftFunctor _ n :=
  NatIso.ofComponents (fun M => HomologicalComplex.Hom.isoOfComponents
    (fun i => ObjectProperty.isoMk _ (etaShiftTermEquiv f M n i).toModuleIso)
    (by
      intro i j hij
      change i + 1 = j at hij
      subst j
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change n.negOnePow •
          (((etaComplex f M).d (i + n) (i + 1 + n)).hom.hom
            (etaShiftTermEquiv f M n i x)).val =
        (etaShiftTermEquiv f M n (i + 1)
          (((etaComplex f (M⟦n⟧)).d i (i + 1)).hom.hom x)).val
      rw [etaComplex_d_val f M _ _ (by omega), etaShiftTermEquiv_apply,
        etaShiftTermEquiv_apply, etaComplex_d_val f (M⟦n⟧) _ _ rfl]
      change _ = (Stacks.GradedLaurent.awayUnit f ^ n) •
        fLoc f (n.negOnePow • (M.d (i + n) (i + 1 + n)).hom.hom) x.val
      rw [fLoc_intUnit_smul, fLoc_zpow_smul, smul_comm]))
    (by
      intro M N g
      apply HomologicalComplex.hom_ext
      intro i
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change (Stacks.GradedLaurent.awayUnit f ^ n) • fLoc f (g.f (i + n)).hom.hom x.val =
        fLoc f (g.f (i + n)).hom.hom ((Stacks.GradedLaurent.awayUnit f ^ n) • x.val)
      exact (fLoc_zpow_smul _ _ _).symm)

/-- The components of `etaShiftIso` are multiplication by `f^n`. -/
@[simp]
theorem etaShiftIso_hom_app_f_val (f : A)
    (M : CochainComplex (FTorsionFreeModule.{u, v} f) ℤ) (n i : ℤ)
    (x : ((etaComplex f (M⟦n⟧)).X i).obj) :
    ((((etaShiftIso f n).hom.app M).f i).hom.hom x).val =
      (Stacks.GradedLaurent.awayUnit f ^ n) • x.val := rfl

/-- The components of `etaFunctor` applied to a morphism `g` are the localizations of the
components of `g`. -/
@[simp]
theorem etaFunctor_map_f_val (f : A)
    {M N : CochainComplex (FTorsionFreeModule.{u, v} f) ℤ} (g : M ⟶ N) (i : ℤ)
    (x : ((etaComplex f M).X i).obj) :
    (((((etaFunctor f).functor.map g).f i).hom).hom x).val =
      fLoc f (g.f i).hom.hom x.val := rfl

/-- The isomorphism `XIsoOfEq` of `etaComplex f M` is the localization of that of `M`. -/
theorem etaComplex_XIsoOfEq_hom_val (f : A)
    (M : CochainComplex (FTorsionFreeModule.{u, v} f) ℤ) {i j : ℤ} (h : i = j)
    (x : ((etaComplex f M).X i).obj) :
    ((((etaComplex f M).XIsoOfEq h).hom).hom.hom x).val =
      fLoc f ((M.XIsoOfEq h).hom).hom.hom x.val := by
  subst j
  change x.val = fLoc f LinearMap.id x.val
  exact (fLoc_id_apply f x.val).symm

/-- The localizations of `M.XIsoOfEq h` and `M.XIsoOfEq h.symm` are mutually inverse. -/
theorem fLoc_XIsoOfEq_symm (f : A)
    (M : CochainComplex (FTorsionFreeModule.{u, v} f) ℤ) {i j : ℤ} (h : i = j)
    (x : Loc f (M.X i).obj) :
    fLoc f ((M.XIsoOfEq h.symm).hom).hom.hom
      (fLoc f ((M.XIsoOfEq h).hom).hom.hom x) = x := by
  subst j
  change fLoc f LinearMap.id (fLoc f LinearMap.id x) = x
  rw [fLoc_id_apply, fLoc_id_apply]

/-- The power maps defining the shift comparison are coherent under addition of shifts. -/
noncomputable instance etaFunctorCommShift (f : A) :
    (etaFunctor.{u, v} f).functor.CommShift ℤ where
  commShiftIso := etaShiftIso f
  commShiftIso_zero := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    rw [Functor.CommShift.isoZero_hom_app]
    apply HomologicalComplex.hom_ext
    intro i
    simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctorZero_inv_app_f]
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [ObjectProperty.FullSubcategory.comp_hom, ModuleCat.hom_comp,
      LinearMap.comp_apply, etaShiftIso_hom_app_f_val]
    change _ = ((((etaComplex f M).XIsoOfEq (show i = i + 0 by omega)).hom).hom.hom
      (((((etaFunctor f).functor.map
        ((shiftFunctorZero
          (CochainComplex (FTorsionFreeModule.{u, v} f) ℤ) ℤ).hom.app M)).f i).hom).hom x)).val
    rw [etaComplex_XIsoOfEq_hom_val, etaFunctor_map_f_val,
      CochainComplex.shiftFunctorZero_hom_app_f]
    simp only [zpow_zero, one_smul]
    with_unfolding_all exact
      (fLoc_XIsoOfEq_symm f M (show i + 0 = i by omega) x.val).symm
  commShiftIso_add a b := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    rw [Functor.CommShift.isoAdd_hom_app]
    apply HomologicalComplex.hom_ext
    intro i
    simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctorAdd_inv_app_f,
      CochainComplex.shiftFunctor_map_f']
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [ObjectProperty.FullSubcategory.comp_hom, ModuleCat.hom_comp,
      LinearMap.comp_apply, etaShiftIso_hom_app_f_val]
    change _ = ((((etaComplex f M).XIsoOfEq
      (show i + b + a = i + (a + b) by omega)).hom).hom.hom
      ((((etaShiftIso f a).hom.app M).f (i + b)).hom.hom
        ((((etaShiftIso f b).hom.app (M⟦a⟧)).f i).hom.hom
          (((((etaFunctor f).functor.map
            ((shiftFunctorAdd
              (CochainComplex (FTorsionFreeModule.{u, v} f) ℤ) a b).hom.app M)).f i).hom).hom
                x)))).val
    rw [etaComplex_XIsoOfEq_hom_val, etaShiftIso_hom_app_f_val,
      etaShiftIso_hom_app_f_val, etaFunctor_map_f_val,
      CochainComplex.shiftFunctorAdd_hom_app_f, fLoc_zpow_smul, fLoc_zpow_smul]
    rw [zpow_add, mul_smul]
    with_unfolding_all exact (congrArg
      (fun y : Loc f (M.X (i + (a + b))).obj =>
        (Stacks.GradedLaurent.awayUnit f ^ a) • ((Stacks.GradedLaurent.awayUnit f ^ b) • y))
      (fLoc_XIsoOfEq_symm f M (show i + (a + b) = i + b + a by omega) x.val).symm)

/-- Restricting a homotopy to the eta terms. -/
noncomputable def etaHomotopy (f : A)
    {M N : CochainComplex (FTorsionFreeModule.{u, v} f) ℤ}
    {g k : M ⟶ N} (h : Homotopy g k) : Homotopy (etaMap f g) (etaMap f k) where
  hom i j := ObjectProperty.homMk (ModuleCat.ofHom
    (EtaComplex.etaHomotopyLinear.{u, v} f ((isFTorsionFree.{u, v} f).ι.mapHomotopy h) i j))
  zero i j hij := by
    apply ObjectProperty.hom_ext
    change ModuleCat.ofHom (EtaComplex.etaHomotopyLinear.{u, v} f
      ((isFTorsionFree.{u, v} f).ι.mapHomotopy h) i j) = 0
    change ¬ j + 1 = i at hij
    simp [EtaComplex.etaHomotopyLinear, hij]
  comm i := by
    generalize hj : i - 1 = j
    have hi : i = j + 1 := by omega
    subst i
    clear hj
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (j + 1) (j + 1 + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel j (j + 1) by simp)]
    apply ObjectProperty.hom_ext
    have hh := EtaComplex.etaHomotopyLinear_comm f
      ((isFTorsionFree.{u, v} f).ι.mapHomotopy h) (j + 1)
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (j + 1) (j + 1 + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel j (j + 1) by simp)] at hh
    simp only [EtaComplex.etaObject_d] at hh
    simp only [etaComplex, CochainComplex.of_d]
    with_unfolding_all exact hh

/-- Eta identifies homotopic maps after passing to the homotopy quotient. -/
theorem eta_respects_homotopy (f : A) :
    ∀ (M N : CochainComplex (FTorsionFreeModule.{u, v} f) ℤ) (g k : M ⟶ N),
      homotopic _ _ g k →
        ((etaFunctor f).functor ⋙ HomotopyCategory.quotient _ _).map g =
          ((etaFunctor f).functor ⋙ HomotopyCategory.quotient _ _).map k := by
  rintro M N g k ⟨h⟩
  exact HomotopyCategory.eq_of_homotopy _ _ (etaHomotopy f h)

/-- The eta endofunctor of the homotopy category. -/
noncomputable def etaHomotopyFunctor (f : A) :
    HomotopyCategory (FTorsionFreeModule.{u, v} f) (ComplexShape.up ℤ) ⥤
      HomotopyCategory (FTorsionFreeModule.{u, v} f) (ComplexShape.up ℤ) :=
  CategoryTheory.Quotient.lift _
    ((etaFunctor f).functor ⋙ HomotopyCategory.quotient _ _) (eta_respects_homotopy f)

/-- The comparison between applying eta before and after the homotopy quotient. -/
noncomputable def etaHomotopyFunctorFactors (f : A) :
    HomotopyCategory.quotient _ _ ⋙ etaHomotopyFunctor.{u, v} f ≅
      (etaFunctor f).functor ⋙ HomotopyCategory.quotient _ _ :=
  CategoryTheory.Quotient.lift.isLift _ _ _

/-- The homotopy descent uses the same shift comparison as the complex functor. -/
noncomputable instance etaHomotopyFunctorCommShift (f : A) :
    (etaHomotopyFunctor.{u, v} f).CommShift ℤ :=
  CategoryTheory.Quotient.liftCommShift _ _ _ _

/-- The factorization through the homotopy quotient respects the chosen shift maps. -/
instance etaHomotopyFunctorFactors_commShift (f : A) :
    NatTrans.CommShift (etaHomotopyFunctorFactors.{u, v} f).hom ℤ :=
  CategoryTheory.Quotient.liftCommShift_compatibility _ _ _ _

/-- The shift by one comparison in the source is multiplication by `f`. -/
theorem etaShiftIso_one_hom_app_f_val (f : A)
    (M : CochainComplex (FTorsionFreeModule.{u, v} f) ℤ) (i : ℤ)
    (x : ((etaComplex f (M⟦(1 : ℤ)⟧)).X i).obj) :
    ((((etaShiftIso f 1).hom.app M).f i).hom.hom x).val = f • x.val := by
  change (Stacks.GradedLaurent.awayUnit f ^ (1 : ℤ)) • x.val = f • x.val
  rw [zpow_one, fUnit_units_smul]

/-- Multiplication by `f` on the complex consisting of `A` in degree one. -/
noncomputable def etaCounterexampleMap (f : A) (hf : f ∈ nonZeroDivisors A) :
    (CochainComplex.singleFunctor (FTorsionFreeModule.{u, v} f) 1).obj
        (torsionFreeSelf f hf) ⟶
      (CochainComplex.singleFunctor (FTorsionFreeModule.{u, v} f) 1).obj
        (torsionFreeSelf f hf) :=
  (CochainComplex.singleFunctor (FTorsionFreeModule.{u, v} f) 1).map
    (ObjectProperty.homMk
      (ModuleCat.ofHom (LinearMap.lsmul A (ULift.{v} A) f)))

section Counterexample

open HomologicalComplex

private theorem eta_isZero_X (f : A)
    (M : CochainComplex (FTorsionFreeModule.{u, v} f) ℤ) (i : ℤ)
    (hi : IsZero (M.X i)) : IsZero ((etaComplex f M).X i) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  ext x
  apply Subtype.ext
  obtain ⟨m, hm⟩ := mem_fpowSub.mp (mem_fetaTerm.mp x.property).1
  have hz : m = 0 :=
    (ModuleCat.isZero_iff_subsingleton.mp ((isFTorsionFree f).ι.map_isZero hi)).elim _ _
  change x.val = 0
  rw [← hm, hz, map_zero, smul_zero]

private theorem eta_d_eq_zero (f : A)
    (M : CochainComplex (FTorsionFreeModule.{u, v} f) ℤ) (i j : ℤ)
    (h : M.d i j = 0) : (etaComplex f M).d i j = 0 := by
  by_cases hij : i + 1 = j
  · ext x
    apply Subtype.ext
    rw [etaComplex_d_val f M i j hij, h]
    change fLoc f 0 x.val = 0
    exact EtaComplex.localizedMap_zero_apply f x.val
  · exact (etaComplex f M).shape i j hij

private theorem isZero_quotient_of_two_term
    {C : Type*} [Category C] [Preadditive C]
    (K : CochainComplex C ℤ) (hz : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (K.X i))
    [IsIso (K.d 0 1)] :
    IsZero ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) := by
  let h : ∀ i j : ℤ, K.X i ⟶ K.X j := fun i j =>
    if hi : i = 1 then if hj : j = 0 then
      (K.XIsoOfEq hi).hom ≫ inv (K.d 0 1) ≫ (K.XIsoOfEq hj).inv
    else 0 else 0
  apply (HomotopyCategory.isZero_quotient_obj_iff K).mpr
  refine ⟨{ hom := h, zero := ?_, comm := ?_ }⟩
  · intro i j hij
    dsimp [h]
    split_ifs <;> subst_vars <;> simp_all
  · intro i
    by_cases h0 : i = 0
    · subst i
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by rfl),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by rfl)]
      simp [h]
    · by_cases h1 : i = 1
      · subst i
        rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 1 2 by rfl),
          prevD_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by rfl)]
        simp [h]
      · exact (hz i h0 h1).eq_of_src _ _

private theorem eta_d_isIso (f : A)
    (M : CochainComplex (FTorsionFreeModule.{u, v} f) ℤ)
    (e : (M.X 0).obj ≃ₗ[A] (M.X 1).obj)
    (hd : (M.d 0 1).hom.hom = f • e.toLinearMap) :
    IsIso ((etaComplex f M).d 0 1) := by
  have hb : Function.Bijective ((etaComplex f M).d 0 1).hom.hom := by
    constructor
    · intro x y h
      apply Subtype.ext
      have he := congrArg Subtype.val h
      rw [etaComplex_d_val f M 0 1 rfl, etaComplex_d_val f M 0 1 rfl] at he
      apply LocalizedModule.map_injective (Submonoid.powers f) (M.d 0 1).hom.hom _ he
      rw [hd]
      intro a b hab
      apply e.injective
      apply sub_eq_zero.mp
      apply (M.X 1).property
      simpa [smul_sub] using sub_eq_zero.mpr hab
    · intro y
      have yp : y.val ∈ fetaTerm f (M.d 1 2).hom.hom 1 := y.property
      obtain ⟨m, hm⟩ := mem_fpowSub.mp (mem_fetaTerm.mp yp).1
      have hy : fLoc f (M.d 0 1).hom.hom (toLoc f (M.X 0).obj (e.symm m)) = y.val := by
        rw [fLoc_toLoc, hd]
        simpa only [LinearMap.smul_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
          map_smul, zpow_one, fUnit_units_smul] using hm
      have hx : toLoc f (M.X 0).obj (e.symm m) ∈
          fetaTerm f (M.d 0 1).hom.hom 0 := by
        refine mem_fetaTerm.mpr ⟨?_, ?_⟩
        · exact mem_fpowSub.mpr ⟨e.symm m, by simp only [zpow_zero, one_smul]⟩
        · rw [hy]
          exact (mem_fetaTerm.mp yp).1
      exact ⟨⟨toLoc f (M.X 0).obj (e.symm m), hx⟩, Subtype.ext hy⟩
  have : IsIso ((isFTorsionFree f).ι.map ((etaComplex f M).d 0 1)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hb
  exact isIso_of_reflects_iso _ (isFTorsionFree f).ι

private noncomputable def coneTermIso (f : A) (hf : f ∈ nonZeroDivisors A) :
    (CochainComplex.mappingCone (etaCounterexampleMap.{u, v} f hf)).X 0 ≅
      (CochainComplex.mappingCone (etaCounterexampleMap.{u, v} f hf)).X 1 where
  hom := homotopyCofiber.fstX (etaCounterexampleMap f hf) 0 1 rfl ≫
    homotopyCofiber.inrX (etaCounterexampleMap f hf) 1
  inv := homotopyCofiber.sndX (etaCounterexampleMap f hf) 1 ≫
    homotopyCofiber.inlX (etaCounterexampleMap f hf) 1 0 rfl
  hom_inv_id := by
    apply homotopyCofiber.ext_from_X (etaCounterexampleMap f hf) 1 0 rfl
    · simp only [Category.assoc, homotopyCofiber.inrX_sndX_assoc,
        homotopyCofiber.inlX_fstX_assoc]
      exact (Category.comp_id _).symm
    · apply (isZero_single_obj_X (ComplexShape.up ℤ) 1 (torsionFreeSelf f hf) 0
        (by decide)).eq_of_src
  inv_hom_id := by
    apply homotopyCofiber.ext_from_X (etaCounterexampleMap f hf) 2 1 rfl
    · apply (isZero_single_obj_X (ComplexShape.up ℤ) 1 (torsionFreeSelf f hf) 2
        (by decide)).eq_of_src
    · simp only [Category.assoc, homotopyCofiber.inlX_fstX_assoc,
        homotopyCofiber.inrX_sndX_assoc]
      exact (Category.comp_id _).symm

private theorem etaCounterexampleMap_f_one (f : A) (hf : f ∈ nonZeroDivisors A) :
    (etaCounterexampleMap.{u, v} f hf).f 1 =
      f • 𝟙 (((CochainComplex.singleFunctor (FTorsionFreeModule f) 1).obj
        (torsionFreeSelf f hf)).X 1) := by
  change ((CochainComplex.singleFunctor (FTorsionFreeModule f) 1).map
    (f • 𝟙 (torsionFreeSelf f hf))).f 1 = _
  simp

private theorem cone_d (f : A) (hf : f ∈ nonZeroDivisors A) :
    ((CochainComplex.mappingCone (etaCounterexampleMap.{u, v} f hf)).d 0 1).hom.hom =
      f • ((coneTermIso f hf).hom).hom.hom := by
  have hd : (CochainComplex.mappingCone (etaCounterexampleMap.{u, v} f hf)).d 0 1 =
      f • (coneTermIso f hf).hom := by
    apply homotopyCofiber.ext_from_X (etaCounterexampleMap f hf) 1 0 rfl
    · change homotopyCofiber.inlX (etaCounterexampleMap f hf) 1 0 rfl ≫
        homotopyCofiber.d (etaCounterexampleMap f hf) 0 1 = _
      rw [homotopyCofiber.inlX_d _ 0 1 2 rfl rfl]
      simp [CochainComplex.singleFunctor_obj_d, etaCounterexampleMap_f_one, coneTermIso]
    · apply (isZero_single_obj_X (ComplexShape.up ℤ) 1 (torsionFreeSelf f hf) 0
        (by decide)).eq_of_src
  exact congrArg (fun g => g.hom.hom) hd

private theorem eta_cone_isZero (f : A) (hf : f ∈ nonZeroDivisors A) :
    IsZero ((etaHomotopyFunctor.{u, v} f).obj
      ((HomotopyCategory.quotient _ _).obj
        (CochainComplex.mappingCone (etaCounterexampleMap f hf)))) := by
  let M := CochainComplex.mappingCone (etaCounterexampleMap.{u, v} f hf)
  have : IsIso ((etaComplex f M).d 0 1) :=
    eta_d_isIso f M (((isFTorsionFree f).ι.mapIso (coneTermIso f hf)).toLinearEquiv)
      (cone_d f hf)
  apply isZero_quotient_of_two_term (etaComplex f M)
  intro i h0 h1
  apply eta_isZero_X
  apply (CochainComplex.mappingCone.isZero_X_iff _ i).mpr
  constructor
  · exact isZero_single_obj_X (ComplexShape.up ℤ) 1 (torsionFreeSelf f hf) (i + 1)
      (by omega)
  · exact isZero_single_obj_X (ComplexShape.up ℤ) 1 (torsionFreeSelf f hf) i h1

private theorem isUnit_of_eta_map_isIso (f : A) (hf : f ∈ nonZeroDivisors A)
    (hi : IsIso ((etaHomotopyFunctor.{u, v} f).map
      ((HomotopyCategory.quotient _ _).map (etaCounterexampleMap f hf)))) : IsUnit f := by
  let S := (CochainComplex.singleFunctor (FTorsionFreeModule.{u, v} f) 1).obj
    (torsionFreeSelf f hf)
  let E := etaComplex f S
  let g := etaMap f (etaCounterexampleMap.{u, v} f hf)
  let q := HomotopyCategory.quotient (FTorsionFreeModule.{u, v} f) (ComplexShape.up ℤ)
  have : IsIso (q.map g) := hi
  obtain ⟨k, hk⟩ := q.map_surjective (inv (q.map g))
  have hh : q.map (k ≫ g) = q.map (𝟙 E) := by
    rw [Functor.map_comp, hk, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
  have h := HomotopyCategory.homotopyOfEq (k ≫ g) (𝟙 E) hh
  have hd (i j : ℤ) : E.d i j = 0 :=
    eta_d_eq_zero f S i j (CochainComplex.singleFunctor_obj_d _ _ _ _)
  have he : k.f 1 ≫ g.f 1 = 𝟙 (E.X 1) := by
    have hh := h.comm 1
    change k.f 1 ≫ g.f 1 = E.d _ _ ≫ _ + _ ≫ E.d _ _ + 𝟙 (E.X 1) at hh
    simpa only [hd, zero_comp, comp_zero, zero_add] using hh
  let e : (S.X 1).obj ≃ₗ[A] ULift.{v} A :=
    (((isFTorsionFree f).ι.mapIso
      (singleObjXSelf (ComplexShape.up ℤ) 1 (torsionFreeSelf f hf))).toLinearEquiv)
  let m : (S.X 1).obj := e.symm (ULift.up 1)
  have hx : (Stacks.GradedLaurent.awayUnit f ^ (1 : ℤ)) • toLoc f (S.X 1).obj m ∈
      fetaTerm f (S.d 1 2).hom.hom 1 := by
    apply mem_fetaTerm.mpr
    refine ⟨mem_fpowSub.mpr ⟨m, rfl⟩, ?_⟩
    change fLoc f 0 _ ∈ _
    rw [EtaComplex.localizedMap_zero_apply]
    exact Submodule.zero_mem _
  let x : (E.X 1).obj := ⟨(Stacks.GradedLaurent.awayUnit f ^ (1 : ℤ)) • toLoc f (S.X 1).obj m, hx⟩
  let y : (E.X 1).obj := (k.f 1).hom.hom x
  have yp : y.val ∈ fetaTerm f (S.d 1 2).hom.hom 1 := y.property
  obtain ⟨n, hn⟩ := mem_fpowSub.mp (mem_fetaTerm.mp yp).1
  have hxy : fLoc f (etaCounterexampleMap f hf |>.f 1).hom.hom y.val = x.val :=
    congrArg (fun a => (a.hom.hom x).val) he
  rw [← hn, fLoc_zpow_smul, fLoc_toLoc] at hxy
  have hn' : f • n = m := by
    apply toLoc_injective_of_isSMulRegular
      (isSMulRegular_of_smul_eq_zero (S.X 1).property)
    apply fUnit_zpow_smul_injective 1
    rwa [etaCounterexampleMap_f_one] at hxy
  have hn'' : f * (e n).down = 1 := by
    have heq := congrArg (fun a => (e a).down) hn'
    simpa [m] using heq
  exact isUnit_iff_exists_inv.mpr ⟨(e n).down, hn''⟩

/-- **Stacks 0GSN.** The cone triangle of multiplication by `f` on `A` in degree
one is distinguished. Its eta cone is homotopic to zero. If `f` is not a unit,
the first eta arrow is not invertible and the image triangle is not distinguished.
The compatible shift comparison is the fixed multiplication-by-`f` map
`etaShiftIso_one_hom_app_f_val`. -/
@[stacks 0GSN]
theorem eta_commutes_shift_but_not_triangulated
    (f : A) (hf : f ∈ nonZeroDivisors A) :
    let g := etaCounterexampleMap.{u, v} f hf
    let q := HomotopyCategory.quotient (FTorsionFreeModule.{u, v} f) (ComplexShape.up ℤ)
    let T := CochainComplex.mappingCone.triangleh g
    T ∈ distTriang (HomotopyCategory (FTorsionFreeModule.{u, v} f) (ComplexShape.up ℤ)) ∧
      IsZero ((etaHomotopyFunctor f).obj (q.obj (CochainComplex.mappingCone g))) ∧
      (¬ IsUnit f →
        ¬ IsIso ((etaHomotopyFunctor f).map (q.map g)) ∧
        (etaHomotopyFunctor f).mapTriangle.obj T ∉
          distTriang (HomotopyCategory (FTorsionFreeModule.{u, v} f) (ComplexShape.up ℤ))) := by
  dsimp only
  have hz := eta_cone_isZero.{u, v} f hf
  refine ⟨HomotopyCategory.mappingCone_triangleh_distinguished _, hz, ?_⟩
  intro hnu
  have hni := fun hi => hnu (isUnit_of_eta_map_isIso.{u, v} f hf hi)
  refine ⟨hni, ?_⟩
  intro ht
  exact hni ((CategoryTheory.Pretriangulated.Triangle.distinguished_iff_of_isZero₃ _ hz).mp ht)

end Counterexample

end Stacks.Eta.DerivedFunctor

/-! ## Eta preserves quasi-isomorphisms (Tag 0F7Q) -/

namespace Stacks.Eta.QuasiIsoPreservation

open CategoryTheory Stacks.Eta.DerivedFunctor EtaPow
open scoped nonZeroDivisors

private noncomputable def cycleClass {R : Type*} [Ring R]
    (S : ShortComplex (ModuleCat.{v} R)) : LinearMap.ker S.g.hom →ₗ[R] S.homology :=
  (S.moduleCatCyclesIso.inv ≫ S.homologyπ).hom

private lemma cycleClass_eq {R : Type*} [Ring R]
    (S : ShortComplex (ModuleCat.{v} R)) :
    cycleClass S = S.moduleCatHomologyIso.inv.hom.comp
      (LinearMap.range S.moduleCatToCycles).mkQ :=
  congrArg ModuleCat.Hom.hom S.moduleCatCyclesIso_inv_π

private lemma cycleClass_surjective {R : Type*} [Ring R]
    (S : ShortComplex (ModuleCat.{v} R)) : Function.Surjective (cycleClass S) := by
  rw [cycleClass_eq]
  exact S.moduleCatHomologyIso.symm.toLinearEquiv.surjective.comp
    (Submodule.mkQ_surjective _)

private lemma cycleClass_eq_zero {R : Type*} [Ring R]
    (S : ShortComplex (ModuleCat.{v} R)) (z : LinearMap.ker S.g.hom) :
    cycleClass S z = 0 ↔ ∃ x : S.X₁, S.f.hom x = z.val := by
  rw [cycleClass_eq, LinearMap.comp_apply]
  change S.moduleCatHomologyIso.symm.toLinearEquiv
    ((LinearMap.range S.moduleCatToCycles).mkQ z) = 0 ↔ _
  rw [S.moduleCatHomologyIso.symm.toLinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact ⟨fun ⟨x, hx⟩ => ⟨x, congrArg Subtype.val hx⟩, fun ⟨x, hx⟩ => ⟨x, Subtype.ext hx⟩⟩

private lemma cycleClass_naturality {R : Type*} [Ring R]
    {S T : ShortComplex (ModuleCat.{v} R)} (a : S ⟶ T)
    (x : LinearMap.ker S.g.hom) (y : LinearMap.ker T.g.hom)
    (h : a.τ₂.hom x.val = y.val) :
    (ShortComplex.homologyMap a).hom (cycleClass S x) = cycleClass T y := by
  have hc : (ShortComplex.cyclesMap a).hom (S.moduleCatCyclesIso.inv.hom x) =
      T.moduleCatCyclesIso.inv.hom y := by
    apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
    change (S.moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap a ≫ T.iCycles).hom x =
      (T.moduleCatCyclesIso.inv ≫ T.iCycles).hom y
    rw [ShortComplex.cyclesMap_i, ← Category.assoc, S.moduleCatCyclesIso_inv_iCycles,
      T.moduleCatCyclesIso_inv_iCycles]
    exact h
  change (S.moduleCatCyclesIso.inv ≫ S.homologyπ ≫ ShortComplex.homologyMap a).hom x = _
  rw [ShortComplex.homologyπ_naturality]
  change T.homologyπ.hom ((ShortComplex.cyclesMap a).hom
    (S.moduleCatCyclesIso.inv.hom x)) = T.homologyπ.hom (T.moduleCatCyclesIso.inv.hom y)
  rw [hc]

private lemma quasiIso_iff_cycles {R : Type*} [Ring R]
    {S T : ShortComplex (ModuleCat.{v} R)} (a : S ⟶ T) :
    ShortComplex.QuasiIso a ↔
      (∀ (x : S.X₂), S.g.hom x = 0 →
        (∃ y : T.X₁, T.f.hom y = a.τ₂.hom x) → ∃ y : S.X₁, S.f.hom y = x) ∧
      (∀ (y : T.X₂), T.g.hom y = 0 →
        ∃ (x : S.X₂), S.g.hom x = 0 ∧
          ∃ w : T.X₁, T.f.hom w = y - a.τ₂.hom x) := by
  rw [ShortComplex.quasiIso_iff, ConcreteCategory.isIso_iff_bijective]
  have hz (x : S.X₂) (hx : S.g.hom x = 0) : T.g.hom (a.τ₂.hom x) = 0 := by
    have he := congrArg (fun k : S.X₂ ⟶ T.X₃ => k.hom x) a.comm₂₃
    simpa [hx] using he
  constructor
  · intro ha
    constructor
    · intro x hx hbound
      apply (cycleClass_eq_zero S ⟨x, hx⟩).mp
      apply ha.1
      rw [map_zero, cycleClass_naturality a ⟨x, hx⟩ ⟨a.τ₂.hom x, hz x hx⟩ rfl]
      exact (cycleClass_eq_zero T _).mpr hbound
    · intro y hy
      obtain ⟨c, hc⟩ := ha.2 (cycleClass T ⟨y, hy⟩)
      obtain ⟨x, rfl⟩ := cycleClass_surjective S c
      refine ⟨x.val, x.property, ?_⟩
      apply (cycleClass_eq_zero T (⟨y, hy⟩ - ⟨a.τ₂.hom x.val, hz x.val x.property⟩)).mp
      rw [map_sub,
        ← cycleClass_naturality a x ⟨a.τ₂.hom x.val, hz x.val x.property⟩ rfl, hc, sub_self]
  · rintro ⟨hinj, hsurj⟩
    constructor
    · apply (LinearMap.ker_eq_bot).mp
      apply LinearMap.ker_eq_bot'.mpr
      intro c hc
      obtain ⟨x, rfl⟩ := cycleClass_surjective S c
      rw [cycleClass_naturality a x ⟨a.τ₂.hom x.val, hz x.val x.property⟩ rfl] at hc
      exact (cycleClass_eq_zero S x).mpr
        (hinj x.val x.property ((cycleClass_eq_zero T _).mp hc))
    · intro c
      obtain ⟨y, rfl⟩ := cycleClass_surjective T c
      obtain ⟨x, hx, w, hw⟩ := hsurj y.val y.property
      refine ⟨cycleClass S ⟨x, hx⟩, ?_⟩
      rw [cycleClass_naturality a ⟨x, hx⟩ ⟨a.τ₂.hom x, hz x hx⟩ rfl]
      have he := (cycleClass_eq_zero T (y - ⟨a.τ₂.hom x, hz x hx⟩)).mpr ⟨w, hw⟩
      exact (sub_eq_zero.mp (by simpa only [map_sub] using he)).symm

private lemma eta_cycle_representative {A : Type*} [CommRing A] {f : A}
    {X Y : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (d : X →ₗ[A] Y) (htf : ∀ y : Y, f • y = 0 → y = 0) (i : ℤ)
    (z : fetaTerm f d i) (hz : fLoc f d z.val = 0) :
    ∃ x : X, d x = 0 ∧ (Stacks.GradedLaurent.awayUnit f ^ i) • toLoc f X x = z.val := by
  obtain ⟨x, hx⟩ := mem_fpowSub.mp z.property.1
  refine ⟨x, ?_, hx⟩
  rw [← hx, fLoc_zpow_smul, fLoc_toLoc, fUnit_zpow_smul_eq_zero_iff] at hz
  apply toLoc_injective_of_isSMulRegular (isSMulRegular_of_smul_eq_zero htf)
  simpa only [map_zero] using hz

private lemma eta_cycle_mem {A : Type*} [CommRing A] {f : A}
    {X Y : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (d : X →ₗ[A] Y) (i : ℤ) (x : X) (hx : d x = 0) :
    (Stacks.GradedLaurent.awayUnit f ^ i) • toLoc f X x ∈ fetaTerm f d i := by
  apply mem_fetaTerm.mpr
  refine ⟨mem_fpowSub.mpr ⟨x, rfl⟩, ?_⟩
  rw [fLoc_zpow_smul, fLoc_toLoc, hx, map_zero, smul_zero]
  exact Submodule.zero_mem _

private lemma eta_boundary_iff {A : Type*} [CommRing A] {f : A}
    {X Y : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (d : X →ₗ[A] Y) (htf : ∀ y : Y, f • y = 0 → y = 0) (i : ℤ) (z : Y) :
    (∃ w : fetaTerm f d i,
      fLoc f d w.val = (Stacks.GradedLaurent.awayUnit f ^ (i + 1)) • toLoc f Y z) ↔
      ∃ w : X, d w = f • z := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨x, hx⟩ := mem_fpowSub.mp w.property.1
    refine ⟨x, toLoc_injective_of_isSMulRegular
      (isSMulRegular_of_smul_eq_zero htf) ?_⟩
    apply fUnit_zpow_smul_injective i
    rw [← fUnit_zpow_one_smul_toLoc, fUnit_zpow_smul_smul]
    rwa [← hx, fLoc_zpow_smul, fLoc_toLoc] at hw
  · rintro ⟨w, hw⟩
    have he : fLoc f d ((Stacks.GradedLaurent.awayUnit f ^ i) • toLoc f X w) =
        (Stacks.GradedLaurent.awayUnit f ^ (i + 1)) • toLoc f Y z := by
      rw [fLoc_zpow_smul, fLoc_toLoc, hw, ← fUnit_zpow_one_smul_toLoc,
        fUnit_zpow_smul_smul]
    refine ⟨⟨(Stacks.GradedLaurent.awayUnit f ^ i) • toLoc f X w, ?_⟩, he⟩
    apply mem_fetaTerm.mpr
    refine ⟨mem_fpowSub.mpr ⟨w, rfl⟩, ?_⟩
    rw [he]
    exact mem_fpowSub.mpr ⟨z, rfl⟩

/-- **Stacks 0F7Q.** The Berthelot--Ogus décalage of a quasi-isomorphism of
complexes of `f`-torsion-free modules is a quasi-isomorphism. -/
@[stacks 0F7Q]
theorem quasiIso_etaPow_of_quasiIso
    {A : Type u} [CommRing A] {f : A} (_hf : f ∈ nonZeroDivisors A)
    (E : EtaFunctor.{u, v} f)
    {M N : CochainComplex (FTorsionFreeModule.{u, v} f) ℤ} (g : M ⟶ N)
    (hg : QuasiIso ((underlyingComplex f).map g)) :
    QuasiIso ((underlyingComplex f).map (E.functor.map g)) := by
  let C := (underlyingComplex f).obj M
  let D := (underlyingComplex f).obj N
  let C' := (underlyingComplex f).obj (E.functor.obj M)
  let D' := (underlyingComplex f).obj (E.functor.obj N)
  let a : C ⟶ D := (underlyingComplex f).map g
  let b : C' ⟶ D' := (underlyingComplex f).map (E.functor.map g)
  let tM (i : ℤ) : C'.X i ≃ₗ[A] fetaTerm f (C.d i (i + 1)).hom i :=
    (E.termIso M i).toLinearEquiv
  let tN (i : ℤ) : D'.X i ≃ₗ[A] fetaTerm f (D.d i (i + 1)).hom i :=
    (E.termIso N i).toLinearEquiv
  have hdM (i : ℤ) (x : C'.X i) :
      (tM (i + 1) ((C'.d i (i + 1)).hom x)).val =
        fLoc f (C.d i (i + 1)).hom (tM i x).val := E.differential M i x
  have hdN (i : ℤ) (x : D'.X i) :
      (tN (i + 1) ((D'.d i (i + 1)).hom x)).val =
        fLoc f (D.d i (i + 1)).hom (tN i x).val := E.differential N i x
  have hab (i : ℤ) (x : C'.X i) :
      (tN i ((b.f i).hom x)).val = fLoc f (a.f i).hom (tM i x).val := E.map_f g i x
  have htfM (i : ℤ) : ∀ x : C.X i, f • x = 0 → x = 0 := (M.X i).property
  have htfN (i : ℤ) : ∀ x : D.X i, f • x = 0 → x = 0 := (N.X i).property
  have hdegree (j : ℤ) : QuasiIsoAt b (j + 1) := by
    let sa := (HomologicalComplex.shortComplexFunctor' (ModuleCat A) _
      j (j + 1) (j + 1 + 1)).map a
    let sb := (HomologicalComplex.shortComplexFunctor' (ModuleCat A) _
      j (j + 1) (j + 1 + 1)).map b
    have ha : ShortComplex.QuasiIso sa :=
      (quasiIsoAt_iff' a j (j + 1) (j + 1 + 1) (by simp) (by simp)).mp
        (hg.quasiIsoAt (j + 1))
    obtain ⟨hinj, hsurj⟩ := (quasiIso_iff_cycles sa).mp ha
    change ∀ x : C.X (j + 1), (C.d (j + 1) (j + 1 + 1)).hom x = 0 →
      (∃ y : D.X j, (D.d j (j + 1)).hom y = (a.f (j + 1)).hom x) →
      ∃ y : C.X j, (C.d j (j + 1)).hom y = x at hinj
    change ∀ y : D.X (j + 1), (D.d (j + 1) (j + 1 + 1)).hom y = 0 →
      ∃ x : C.X (j + 1), (C.d (j + 1) (j + 1 + 1)).hom x = 0 ∧
      ∃ w : D.X j, (D.d j (j + 1)).hom w = y - (a.f (j + 1)).hom x at hsurj
    apply (quasiIsoAt_iff' b j (j + 1) (j + 1 + 1) (by simp) (by simp)).mpr
    apply (quasiIso_iff_cycles sb).mpr
    change
      (∀ x : C'.X (j + 1), (C'.d (j + 1) (j + 1 + 1)).hom x = 0 →
        (∃ y : D'.X j, (D'.d j (j + 1)).hom y = (b.f (j + 1)).hom x) →
        ∃ y : C'.X j, (C'.d j (j + 1)).hom y = x) ∧
      (∀ y : D'.X (j + 1), (D'.d (j + 1) (j + 1 + 1)).hom y = 0 →
        ∃ x : C'.X (j + 1), (C'.d (j + 1) (j + 1 + 1)).hom x = 0 ∧
        ∃ w : D'.X j, (D'.d j (j + 1)).hom w = y - (b.f (j + 1)).hom x)
    constructor
    · intro x hx hboundary
      change (C'.d (j + 1) (j + 1 + 1)).hom x = 0 at hx
      have hxloc : fLoc f (C.d (j + 1) (j + 1 + 1)).hom (tM (j + 1) x).val = 0 := by
        rw [← hdM, hx, map_zero]
        rfl
      obtain ⟨z, hz, hzx⟩ := eta_cycle_representative _ (htfM _) _ _ hxloc
      obtain ⟨y, hy⟩ := hboundary
      change (D'.d j (j + 1)).hom y = (b.f (j + 1)).hom x at hy
      have hbnd : ∃ w : D.X j,
          (D.d j (j + 1)).hom w = f • (a.f (j + 1)).hom z := by
        apply (eta_boundary_iff _ (htfN _) j _).mp
        refine ⟨tN j y, ?_⟩
        rw [← hdN, hy, hab, ← hzx, fLoc_zpow_smul, fLoc_toLoc]
      obtain ⟨w, hw⟩ := hinj (f • z) (by rw [map_smul, hz, smul_zero])
        (by simpa only [map_smul] using hbnd)
      obtain ⟨w', hw'⟩ := (eta_boundary_iff _ (htfM _) j z).mpr ⟨w, hw⟩
      refine ⟨(tM j).symm w', ?_⟩
      apply (tM (j + 1)).injective
      apply Subtype.ext
      rw [hdM, LinearEquiv.apply_symm_apply, hw', hzx]
    · intro y hy
      change (D'.d (j + 1) (j + 1 + 1)).hom y = 0 at hy
      have hyloc : fLoc f (D.d (j + 1) (j + 1 + 1)).hom (tN (j + 1) y).val = 0 := by
        rw [← hdN, hy, map_zero]
        rfl
      obtain ⟨z, hz, hzy⟩ := eta_cycle_representative _ (htfN _) _ _ hyloc
      obtain ⟨x, hx, w, hw⟩ := hsurj z hz
      let x' : C'.X (j + 1) := (tM (j + 1)).symm
        ⟨(Stacks.GradedLaurent.awayUnit f ^ (j + 1)) • toLoc f (C.X (j + 1)) x,
          eta_cycle_mem _ _ x hx⟩
      have hxx : (tM (j + 1) x').val =
          (Stacks.GradedLaurent.awayUnit f ^ (j + 1)) • toLoc f (C.X (j + 1)) x :=
        congrArg Subtype.val ((tM (j + 1)).apply_symm_apply _)
      refine ⟨x', ?_, ?_⟩
      · apply (tM (j + 1 + 1)).injective
        apply Subtype.ext
        rw [hdM, hxx, fLoc_zpow_smul, fLoc_toLoc, hx, map_zero, smul_zero, map_zero]
        rfl
      · obtain ⟨w', hw'⟩ := (eta_boundary_iff (D.d j (j + 1)).hom (htfN _) j
              (z - (a.f (j + 1)).hom x)).mpr
            ⟨f • w, by simpa only [map_smul] using congrArg (f • ·) hw⟩
        refine ⟨(tN j).symm w', ?_⟩
        apply (tN (j + 1)).injective
        apply Subtype.ext
        change (tN (j + 1) ((D'.d j (j + 1)).hom ((tN j).symm w'))).val =
          (tN (j + 1) (y - (b.f (j + 1)).hom x')).val
        rw [hdN, LinearEquiv.apply_symm_apply, hw']
        simp only [map_sub, Submodule.coe_sub]
        rw [hab, hxx, fLoc_zpow_smul, fLoc_toLoc, smul_sub, hzy]
  exact ⟨fun i => by simpa using hdegree (i - 1)⟩

end Stacks.Eta.QuasiIsoPreservation

/-! ## Eta on the derived category (Tag 0F7R) -/

namespace Stacks.Eta.DerivedDescent

open CategoryTheory
open Stacks.Eta.DerivedFunctor

/-- The homotopy category of complexes of `f`-torsion-free modules, included into the
homotopy category of all complexes of `A`-modules. -/
noncomputable abbrev homotopyInclusion {A : Type u} [CommRing A] (f : A) :
    HomotopyCategory (FTorsionFreeModule.{u, v} f) (ComplexShape.up ℤ) ⥤
      HomotopyCategory (ModuleCat.{max u v} A) (ComplexShape.up ℤ) :=
  (isFTorsionFree.{u, v} f).ι.mapHomotopyCategory (ComplexShape.up ℤ)

private lemma flat_isFTorsionFree {A : Type u} [CommRing A] {f : A}
    (hf : f ∈ nonZeroDivisors A) (M : ModuleCat.{max u v} A) [Module.Flat A M] :
    isFTorsionFree f M := by
  intro x hx
  exact Module.Flat.isSMulRegular_of_nonZeroDivisors hf (by simpa using hx)

/-- The quasi-isomorphisms of `K(A)` between complexes of `f`-torsion-free modules: the
morphisms of the homotopy category which become quasi-isomorphisms of complexes of
`A`-modules. -/
def fTorsionFreeHomotopyQuasiIso {A : Type u} [CommRing A] (f : A) :
    MorphismProperty (HomotopyCategory (FTorsionFreeModule.{u, v} f) (ComplexShape.up ℤ)) :=
  (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).inverseImage
    (homotopyInclusion.{u, v} f)

/-- The quasi-isomorphisms of complexes of `f`-torsion-free modules: the morphisms which become
quasi-isomorphisms of complexes of `A`-modules. -/
def fTorsionFreeQuasiIso {A : Type u} [CommRing A] (f : A) :
    MorphismProperty (CochainComplex (FTorsionFreeModule.{u, v} f) ℤ) :=
  (HomologicalComplex.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).inverseImage
    (underlyingComplex.{u, v} f)

/-- **`D(A)` is the localization of the homotopy category of complexes of `f`-torsion-free
modules.** For a nonzerodivisor `f`, passing from the homotopy category of complexes of
`f`-torsion-free `A`-modules to `D(A)` is the localization at the quasi-isomorphisms.

The input is Tag 0GSL, applied to the full triangulated subcategory of `K(A)` spanned by the
complexes of `f`-torsion-free modules: the resolutions it asks for are the flat resolutions of
`EtaFlatResolution.exists_flatTerms_resolution`, a flat module being `f`-torsion-free when `f`
is a nonzerodivisor. -/
lemma isLocalization_homotopyInclusion {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)] (f : A) (hf : f ∈ nonZeroDivisors A) :
    (homotopyInclusion.{u, v} f ⋙ DerivedCategory.Qh).IsLocalization
      (fTorsionFreeHomotopyQuasiIso.{u, v} f) := by
  let I := homotopyInclusion.{u, v} f
  let W := HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)
  let : I.Full := by dsimp [I, homotopyInclusion]; infer_instance
  let : I.Faithful := by dsimp [I, homotopyInclusion]; infer_instance
  let : I.CommShift ℤ := by dsimp [I, homotopyInclusion]; infer_instance
  let : I.IsTriangulated := by dsimp [I, homotopyInclusion]; infer_instance
  let P : ObjectProperty (HomotopyCategory (ModuleCat.{max u v} A) (ComplexShape.up ℤ)) :=
    I.essImage
  let : P.IsTriangulated := by dsimp [P]; infer_instance
  let Φ : LocalizerMorphism (W.inverseImage P.ι) W :=
    { functor := P.ι, map := le_rfl }
  have hW : W.IsSaturated :=
    (HomotopyCategory.isSaturated_subcategoryAcyclic_and_quasiIso_and_kernel_eq
      (DerivedCategory.Qh (C := ModuleCat.{max u v} A))).2.1.1
  let : W.IsCompatibleWithTriangulation := by
    dsimp only [W]
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    infer_instance
  let : Φ.HasLeftResolutions := by
    intro X
    obtain ⟨K, q, hflat, hq⟩ :=
      EtaFlatResolution.exists_flatTerms_resolution.{u, v} X.as
    let K' := HomologicalComplex.liftObjectProperty (isFTorsionFree.{u, v} f) K
      (fun n ↦ @flat_isFTorsionFree A _ f hf (K.X n) (hflat n))
    let Y := (HomotopyCategory.quotient _ _).obj K'
    let e : I.obj Y ≅ (HomotopyCategory.quotient _ _).obj K := Iso.refl _
    let YP : P.FullSubcategory := ⟨I.obj Y, ⟨Y, ⟨Iso.refl _⟩⟩⟩
    let a : P.ι.obj YP ⟶ X := e.hom ≫ (HomotopyCategory.quotient _ _).map q
    have he : W e.hom := by
      change W (𝟙 _)
      exact W.id_mem _
    exact ⟨⟨a, by
      dsimp only [W, a]
      exact (HomotopyCategory.quasiIso _ _).comp_mem _ _
        he
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff q).2 hq)⟩⟩
  have hΦ :=
    (P.isSaturated_and_isCompatibleWithTriangulation_inverseImage_ι_and_isLocalizedEquivalence
      W hW).2.2
  let : Φ.IsLocalizedEquivalence := hΦ inferInstance
  let : (P.ι ⋙ DerivedCategory.Qh).IsLocalization (W.inverseImage P.ι) := by
    change (Φ.functor ⋙ DerivedCategory.Qh).IsLocalization (W.inverseImage P.ι)
    exact CategoryTheory.LocalizerMorphism.IsLocalizedEquivalence.isLocalization
      Φ DerivedCategory.Qh
  let E : (HomotopyCategory (FTorsionFreeModule.{u, v} f) (ComplexShape.up ℤ)) ≌
      P.FullSubcategory := I.toEssImage.asEquivalence
  let J : E.symm.functor ⋙ I ≅ P.ι :=
    CategoryTheory.Functor.isoWhiskerLeft E.inverse (Functor.toEssImageCompι I).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      CategoryTheory.Functor.isoWhiskerRight E.counitIso P.ι ≪≫
      P.ι.leftUnitor
  let WT := W.inverseImage I
  have hLoc : (I ⋙ DerivedCategory.Qh).IsLocalization WT := by
    apply CategoryTheory.Functor.IsLocalization.of_equivalence_source
      (P.ι ⋙ DerivedCategory.Qh) (W.inverseImage P.ι)
      (I ⋙ DerivedCategory.Qh) WT E.symm
    · intro X Y g hg
      apply (W.inverseImage I).le_isoClosure
      exact (W.arrow_mk_iso_iff
        (((Functor.mapArrowFunctor _ _).mapIso J).app (Arrow.mk g))).2 hg
    · intro X Y g hg
      change IsIso (DerivedCategory.Qh.map (I.map g))
      exact Localization.inverts DerivedCategory.Qh W _ hg
    · exact CategoryTheory.Functor.isoWhiskerRight J DerivedCategory.Qh
  exact hLoc

/-- Passing from complexes of `f`-torsion-free modules to `D(A)` factors through the homotopy
category. -/
noncomputable def underlyingComplexFactors {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)] (f : A) :
    underlyingComplex.{u, v} f ⋙ DerivedCategory.Q ≅
      HomotopyCategory.quotient (FTorsionFreeModule.{u, v} f) (ComplexShape.up ℤ) ⋙
        homotopyInclusion.{u, v} f ⋙ DerivedCategory.Qh :=
  (CategoryTheory.Functor.isoWhiskerLeft (underlyingComplex.{u, v} f)
      (DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A))).symm ≪≫
    CategoryTheory.Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryFactors (isFTorsionFree.{u, v} f).ι
        (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫
    Functor.associator _ _ _

private lemma homotopyInclusion_map {A : Type u} [CommRing A] (f : A)
    {Y Z : CochainComplex (FTorsionFreeModule.{u, v} f) ℤ} (p : Y ⟶ Z) :
    (homotopyInclusion.{u, v} f).map
        ((HomotopyCategory.quotient (FTorsionFreeModule.{u, v} f)
          (ComplexShape.up ℤ)).map p) =
      (HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).map
        ((underlyingComplex.{u, v} f).map p) :=
  Functor.mapHomotopyCategory_map (isFTorsionFree.{u, v} f).ι p

private lemma homotopyEquivalences_le_fTorsionFreeQuasiIso {A : Type u} [CommRing A] (f : A) :
    HomologicalComplex.homotopyEquivalences (FTorsionFreeModule.{u, v} f) (ComplexShape.up ℤ) ≤
      fTorsionFreeQuasiIso.{u, v} f := by
  intro Y Z p hp
  have h1 : IsIso ((HomotopyCategory.quotient (FTorsionFreeModule.{u, v} f)
      (ComplexShape.up ℤ)).map p) :=
    HomotopyCategory.quotient_inverts_homotopyEquivalences _ _ _ hp
  have h2 : IsIso ((HomotopyCategory.quotient (ModuleCat.{max u v} A)
      (ComplexShape.up ℤ)).map ((underlyingComplex.{u, v} f).map p)) := by
    rw [← homotopyInclusion_map.{u, v} f p]
    exact ((homotopyInclusion.{u, v} f).mapIso (@asIso _ _ _ _ _ h1)).isIso_hom
  have h3 := (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences
    ((underlyingComplex.{u, v} f).map p)).1 h2
  change QuasiIso ((underlyingComplex.{u, v} f).map p)
  exact _root_.homotopyEquivalences_le_quasiIso _ _ _ h3

/-- **`D(A)` is the localization of the complexes of `f`-torsion-free modules.** For a
nonzerodivisor `f`, passing from complexes of `f`-torsion-free `A`-modules to `D(A)` is the
localization at the quasi-isomorphisms.  This is `isLocalization_homotopyInclusion` composed
with the passage to the homotopy category. -/
lemma isLocalization_underlyingComplexCompQ {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)] (f : A) (hf : f ∈ nonZeroDivisors A) :
    (underlyingComplex.{u, v} f ⋙ DerivedCategory.Q).IsLocalization
      (fTorsionFreeQuasiIso.{u, v} f) := by
  have hloc := isLocalization_homotopyInclusion.{u, v, w} f hf
  have hcomp : ((HomotopyCategory.quotient (FTorsionFreeModule.{u, v} f)
      (ComplexShape.up ℤ)) ⋙
      (homotopyInclusion.{u, v} f ⋙ DerivedCategory.Qh)).IsLocalization
      (fTorsionFreeQuasiIso.{u, v} f) := by
    refine CategoryTheory.Functor.IsLocalization.comp _ _
      (HomologicalComplex.homotopyEquivalences (FTorsionFreeModule.{u, v} f)
        (ComplexShape.up ℤ))
      (fTorsionFreeHomotopyQuasiIso.{u, v} f) (fTorsionFreeQuasiIso.{u, v} f) ?_
      (homotopyEquivalences_le_fTorsionFreeQuasiIso.{u, v} f) ?_
    · rw [← MorphismProperty.IsInvertedBy.iff_of_iso _ (underlyingComplexFactors.{u, v, w} f)]
      intro Y Z p hp
      have hq : QuasiIso ((underlyingComplex.{u, v} f).map p) := hp
      change IsIso (DerivedCategory.Q.map ((underlyingComplex.{u, v} f).map p))
      infer_instance
    · intro Y Z p hp
      obtain ⟨q, rfl⟩ := (HomotopyCategory.quotient (FTorsionFreeModule.{u, v} f)
        (ComplexShape.up ℤ)).map_surjective p
      refine MorphismProperty.map_mem_map _ _ _ ?_
      have hp' : HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)
          ((HomotopyCategory.quotient (ModuleCat.{max u v} A)
            (ComplexShape.up ℤ)).map ((underlyingComplex.{u, v} f).map q)) := by
        rwa [← homotopyInclusion_map.{u, v} f q]
      exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).1 hp'
  exact CategoryTheory.Functor.IsLocalization.of_equivalence_target
    (L := HomotopyCategory.quotient (FTorsionFreeModule.{u, v} f) (ComplexShape.up ℤ) ⋙
      (homotopyInclusion.{u, v} f ⋙ DerivedCategory.Qh)) _ _
    (CategoryTheory.Equivalence.refl)
    (Functor.rightUnitor _ ≪≫ (underlyingComplexFactors.{u, v, w} f).symm)

private lemma etaFunctor_additive {A : Type u} [CommRing A] (f : A) :
    (etaFunctor.{u, v} f).functor.Additive := by
  constructor
  intro X Y g h
  ext i x
  apply Subtype.ext
  change EtaPow.fLoc f ((g.f i).hom.hom + (h.f i).hom.hom) x.val =
    EtaPow.fLoc f (g.f i).hom.hom x.val + EtaPow.fLoc f (h.f i).hom.hom x.val
  exact EtaComplex.localizedMap_add_apply _ _ _ _

/-- **Stacks 0F7R.** For a nonzerodivisor `f`, the Berthelot--Ogus décalage
descends to an additive endofunctor of the derived category. On every complex
of `f`-torsion-free modules it is naturally isomorphic, on objects and
morphisms, to the chain-level décalage. -/
@[stacks 0F7R]
theorem exists_additive_derived_eta
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    (f : A) (hf : f ∈ nonZeroDivisors A) :
    ∃ (Leta : DerivedCategory (ModuleCat.{max u v} A) ⥤
        DerivedCategory (ModuleCat.{max u v} A)),
      Leta.Additive ∧
        ∃ E : EtaFunctor.{u, v} f,
          Nonempty (underlyingComplex f ⋙ DerivedCategory.Q ⋙ Leta ≅
            E.functor ⋙ underlyingComplex f ⋙ DerivedCategory.Q) := by
  let I := homotopyInclusion.{u, v} f
  let W := HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)
  let WT := W.inverseImage I
  let : (I ⋙ DerivedCategory.Qh).IsLocalization WT :=
    isLocalization_homotopyInclusion.{u, v, w} f hf
  let Eη := etaFunctor.{u, v} f
  let F := etaHomotopyFunctor.{u, v} f ⋙ I ⋙ DerivedCategory.Qh
  have hF : WT.IsInvertedBy F := by
    intro X Y g hg
    obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
    have hg' : QuasiIso ((underlyingComplex f).map g) := by
      simpa [WT, W, I, homotopyInclusion] using
        (HomotopyCategory.quotient_map_mem_quasiIso_iff ((underlyingComplex f).map g)).1 hg
    have heta := Stacks.Eta.QuasiIsoPreservation.quasiIso_etaPow_of_quasiIso hf Eη g hg'
    apply Localization.inverts DerivedCategory.Qh W
    let N := CategoryTheory.Functor.isoWhiskerRight
      (etaHomotopyFunctorFactors.{u, v} f) I
    apply (W.arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso N).app (Arrow.mk g))).2
    change W ((HomotopyCategory.quotient (ModuleCat.{max u v} A)
      (ComplexShape.up ℤ)).map ((underlyingComplex f).map (Eη.functor.map g)))
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff
      ((underlyingComplex f).map (Eη.functor.map g))).2 heta
  let Leta := Localization.lift F hF (I ⋙ DerivedCategory.Qh)
  let qT := HomotopyCategory.quotient
    (FTorsionFreeModule.{u, v} f) (ComplexShape.up ℤ)
  let B : underlyingComplex f ⋙ DerivedCategory.Q ≅ qT ⋙ I ⋙ DerivedCategory.Qh :=
    underlyingComplexFactors.{u, v, w} f
  have hL : (I ⋙ DerivedCategory.Qh) ⋙ Leta ≅ F :=
    Localization.fac F hF (I ⋙ DerivedCategory.Qh)
  have hcomp : underlyingComplex f ⋙ DerivedCategory.Q ⋙ Leta ≅
      Eη.functor ⋙ underlyingComplex f ⋙ DerivedCategory.Q :=
    CategoryTheory.Functor.isoWhiskerRight B Leta ≪≫
      Functor.associator _ _ _ ≪≫
      CategoryTheory.Functor.isoWhiskerLeft qT hL ≪≫
      (Functor.associator _ _ _).symm ≪≫
      CategoryTheory.Functor.isoWhiskerRight (etaHomotopyFunctorFactors.{u, v} f)
        (I ⋙ DerivedCategory.Qh) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      CategoryTheory.Functor.isoWhiskerLeft Eη.functor B.symm
  refine ⟨Leta, ?_, Eη, ⟨hcomp⟩⟩
  have : Eη.functor.Additive := etaFunctor_additive f
  have : (etaHomotopyFunctor.{u, v} f).Additive := by
    have : (qT ⋙ etaHomotopyFunctor.{u, v} f).Additive :=
      Functor.additive_of_iso (etaHomotopyFunctorFactors.{u, v} f).symm
    exact Functor.additive_of_full_essSurj_comp qT _
  have : F.Additive := by dsimp [F, I, homotopyInclusion]; infer_instance
  have : ((I ⋙ DerivedCategory.Qh) ⋙ Leta).Additive :=
    Functor.additive_of_iso hL.symm
  have hWT : WT = ((HomotopyCategory.subcategoryAcyclic
      (ModuleCat.{max u v} A)).inverseImage I).trW := by
    ext X Y g
    dsimp only [WT, W, MorphismProperty.inverseImage]
    rw [ObjectProperty.inverseImage_trW_iff,
      HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  have : WT.HasLeftCalculusOfFractions := by
    rw [hWT]
    infer_instance
  exact (Localization.functor_additive_iff (I ⋙ DerivedCategory.Qh) WT Leta).2 inferInstance

end Stacks.Eta.DerivedDescent
